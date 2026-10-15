/*
 * This file is part of Baritone.
 *
 * Baritone is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Baritone is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Baritone.  If not, see <https://www.gnu.org/licenses/>.
 */

package baritone.pathing.path;

import baritone.Baritone;
import baritone.api.pathing.calc.IPath;
import baritone.api.utils.BetterBlockPos;
import baritone.api.utils.Rotation;
import baritone.api.utils.RotationUtils;
import baritone.api.utils.input.Input;
import baritone.behavior.PathingBehavior;
import baritone.pathing.movement.CalculationContext;
import baritone.pathing.movement.Movement;
import baritone.pathing.movement.MovementHelper;
import baritone.pathing.movement.movements.MovementAscend;
import baritone.pathing.movement.movements.MovementDescend;
import baritone.pathing.movement.movements.MovementDiagonal;
import baritone.pathing.movement.movements.MovementFall;
import baritone.pathing.movement.movements.MovementTraverse;
import baritone.utils.BlockStateInterface;
import baritone.utils.pathing.Avoidance;
import net.minecraft.core.BlockPos;
import net.minecraft.tags.BlockTags;
import net.minecraft.world.level.block.Blocks;
import net.minecraft.world.level.block.state.BlockState;
import net.minecraft.world.phys.Vec3;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * A {@link PathExecutor} overlaid with "beeline" pure-pursuit steering: instead of walking to the
 * center of every block on the calculated path, commit to the farthest upcoming path position
 * reachable in a straight line whose swept hitbox is re-verified walkable every tick, and steer
 * directly at it. The calculated path itself is never modified.
 *
 * <p>Control is exclusive, never shared. An explicit state machine governs who drives the player:
 * <ul>
 * <li>{@code OFF} — the movements drive, exactly as vanilla baritone; every tick the beeline
 * offers to take over by finding a verified aim.</li>
 * <li>{@code ENGAGED} — the beeline drives outright: rotation, movement keys, jumping, and
 * sprinting. The current movement is not ticked at all (via {@link #takeFullControl}), so nothing
 * computes rival steering or judges the player's intentionally off-grid position.</li>
 * <li>{@code COOLDOWN} — after a watchdog trip, the movements drive unassisted for a few seconds
 * so baritone's native recovery (exact positioning, timeouts, recalculation) gets an honest
 * chance; the beeline won't re-engage until it expires.</li>
 * </ul>
 */
public class BeelinePathExecutor extends PathExecutor {

    /**
     * Hard distance cap while a beeline is engaged. An engaged beeline re-verifies a straight
     * walkable line back to the path every tick, so the usual limits don't apply — cuts routinely
     * sit 2+ blocks from the nearest path position — but past this even a verified cut is fishy.
     */
    private static final double MAX_DIST_FROM_PATH_BEELINE = 6;

    /**
     * Corridor clearance tiers for steering, strict first (same idea as the elytra solver's
     * relaxation passes): prefer a line whose swept corridor is wider than the hitbox by this
     * margin on each side, so cuts keep daylight between the player and walls; if no aim passes,
     * relax to the exact hitbox before giving up. Relaxing only ever restores the baseline
     * corridor — never a narrower one — so safety is unchanged.
     */
    private static final double[] STEERING_MARGINS = {0.2, 0.0};

    /**
     * Extra half-width, beyond the hitbox, of the hazard-free zone every chord must sweep. The
     * walkability corridor is hitbox-exact, but the player's real trajectory drifts a few tenths
     * off the ideal line during hops and drops — acceptable against a wall (a scrape), lethal
     * against lava or fire. This never relaxes: no clearance tier, no direct-to-goal exemption.
     */
    private static final double HAZARD_CLEARANCE = 0.75;

    private enum State {
        OFF, ENGAGED, COOLDOWN
    }

    private State state = State.OFF;

    /**
     * The path position index of the committed aim; only meaningful while ENGAGED. Commitment is
     * what keeps the line stable: the fresh per-tick search may flicker, but the committed aim is
     * kept as long as its chord re-verifies walkable.
     */
    private int engagedAimIdx = -1;

    /**
     * The committed aim point; non-null exactly while ENGAGED. Written on the game thread, read
     * by the render thread for debug visualization and by {@link baritone.utils.PathRenderer}.
     */
    private volatile Vec3 beelineAim;

    /**
     * The predicted beeline trajectory (world coordinates, at path render height) for the
     * upcoming portion of the path, recomputed on a cadence. Null when beelining is disabled.
     */
    private volatile List<Vec3> beelineRenderPath;

    private int cooldownTicks;

    // TODO remove, temporary stall diagnostics
    private boolean lastJump;

    /**
     * Stall watchdog: the distance to the committed aim must keep shrinking. Speed is a poor
     * proxy for progress (water bobbing and wall-sliding register as motion), so measure actual
     * approach; no improvement for 30 ticks means we're jammed on something the corridor test
     * didn't see, and vanilla recovery should take over.
     */
    private Vec3 watchAim;
    private double bestAimDist;
    private int stallTicks;

    /**
     * Oscillation watchdog: the stall watchdog resets when the aim changes, so a cycle that flips
     * between aims (hop up a corner, slide back off, hop again) never trips it. Displacement is
     * aim-agnostic: engaged for 50 ticks and still standing basically where we started means a
     * loop, however busy the aims looked.
     */
    private Vec3 loopAnchorPos;
    private int loopWindowTicks;

    /**
     * The run end is needed several times per tick and walking the whole movement list to find it
     * isn't free; compute it once per game tick.
     */
    private int runEndCacheTick = -1;
    private int runEndCached;

    /**
     * The debug render path is a full greedy string-pull over the remaining run — by far the most
     * expensive thing here (every advance re-sweeps candidate chords block by block). It's only
     * eye candy, so recompute it on a cadence instead of every tick.
     */
    private int renderPathThrottle;

    /**
     * The #avoidance spheres (hostile mobs, mob spawners) A* priced its detours with, refreshed
     * once a second — building the list scans nearby entities, too heavy to redo per chord.
     * Empty whenever the avoidance setting is off.
     */
    private List<Avoidance> avoidances = Collections.emptyList();
    private int avoidanceCacheTick = Integer.MIN_VALUE;

    public BeelinePathExecutor(PathingBehavior behavior, IPath path) {
        super(behavior, path);
    }

    /**
     * @return The predicted beeline for debug rendering, or null
     */
    public List<Vec3> getBeelineRenderPath() {
        return beelineRenderPath;
    }

    /**
     * @return The committed aim point, or null when not engaged
     */
    public Vec3 getBeelineAim() {
        return beelineAim;
    }

    @Override
    protected PathExecutor createExecutor(IPath path) {
        return new BeelinePathExecutor(behavior, path);
    }

    // ------------------------------------------------------------------
    // state machine
    // ------------------------------------------------------------------

    /**
     * The single decision point, called by the base executor in place of ticking the movement.
     * Returns true exactly when ENGAGED, in which case {@link #drive} has fully steered the
     * player this tick and the movement must not be consulted.
     */
    @Override
    protected boolean takeFullControl(Movement movement) {
        if (!Baritone.settings().beeline.value) {
            disengage(false);
            return false;
        }
        if (--renderPathThrottle <= 0) {
            beelineRenderPath = computeBeelineRenderPath();
            renderPathThrottle = 5;
        }
        if (state == State.COOLDOWN) {
            if (--cooldownTicks <= 0) {
                state = State.OFF;
            }
            return false;
        }
        int aimIdx = computeAim(movement);
        if (aimIdx == -1) {
            disengage(false);
            return false;
        }
        state = State.ENGAGED;
        engagedAimIdx = aimIdx;
        BetterBlockPos pos = positionsAt(aimIdx);
        Vec3 aim = new Vec3(pos.x + 0.5, pos.y + 0.5, pos.z + 0.5);
        beelineAim = aim;
        if (watchdogsTripped(movement, aim)) {
            disengage(true);
            return false;
        }
        drive(movement, aim);
        return true;
    }

    private void disengage(boolean cooldown) {
        if (state == State.ENGAGED) {
            clearKeys(); // drop our forced inputs; whatever drives next sets its own
        }
        state = cooldown ? State.COOLDOWN : State.OFF;
        cooldownTicks = cooldown ? 60 : 0;
        engagedAimIdx = -1;
        beelineAim = null;
        watchAim = null;
        stallTicks = 0;
        loopAnchorPos = null;
        loopWindowTicks = 0;
    }

    /**
     * The aim to commit to this tick, or -1 to hand control to the movements. Prefers the
     * farthest fresh search result but keeps the currently committed aim when it's farther and
     * its chord still verifies — the fresh search flickering must not yank the line around.
     */
    private int computeAim(Movement movement) {
        if (!isBeelineable(movement)) {
            return -1;
        }
        if (MovementHelper.isLiquid(ctx, ctx.playerFeet())
                && !MovementHelper.isWater(BlockStateInterface.get(ctx, ctx.playerFeet()))) {
            return -1; // lava; water is fine to beeline through
        }
        // keep steering through the hop of a beelined 1-block step or drop, but a real fall
        // (past 1-block-drop speed) is the movements' problem
        if (!ctx.player().onGround() && ctx.player().getDeltaMovement().y < -0.6) {
            return -1;
        }
        int runEnd = beelineRunEndMovement();
        if (runEnd <= pathPosition) {
            return -1;
        }
        Vec3 playerPos = ctx.player().position();
        int feetY = ctx.playerFeet().y;
        // direct-to-goal's philosophy is maximum reach, and margins would multiply its long
        // bisection sweeps; the clearance tiers are for the bounded scan
        double[] margins = Baritone.settings().beelineDirectToGoal.value ? new double[]{0} : STEERING_MARGINS;
        int aimIdx = -1;
        for (double margin : margins) {
            aimIdx = farthestReachableIndex(playerPos, feetY, pathPosition, runEnd, margin);
            if (aimIdx != -1) {
                break;
            }
        }
        if (state == State.ENGAGED && engagedAimIdx > aimIdx && engagedAimIdx > pathPosition && engagedAimIdx <= runEnd) {
            BetterBlockPos committed = positionsAt(engagedAimIdx);
            if (Math.hypot(committed.x + 0.5 - playerPos.x, committed.z + 0.5 - playerPos.z) > 0.7
                    && reachable(playerPos, feetY, pathPosition, engagedAimIdx, true, 0)) {
                aimIdx = engagedAimIdx;
            }
        }
        if (aimIdx == -1) {
            return -1;
        }
        BetterBlockPos pos = positionsAt(aimIdx);
        if (Math.hypot(pos.x + 0.5 - playerPos.x, pos.z + 0.5 - playerPos.z) < (aimIdx == runEnd ? 0.7 : 0.5)) {
            // arrived at the end of the run, or nothing past the block underfoot verifies, and
            // steering at our own feet just jitters in place, so hand off to the movement
            return -1;
        }
        return aimIdx;
    }

    /**
     * @return True if either watchdog demands a cooldown handoff
     */
    private boolean watchdogsTripped(Movement movement, Vec3 aim) {
        Vec3 playerPos = ctx.player().position();
        if (watchAim == null || watchAim.distanceTo(aim) > 0.9) {
            watchAim = aim;
            bestAimDist = Double.MAX_VALUE;
            stallTicks = 0;
        }
        double distToAim = playerPos.distanceTo(aim);
        if (distToAim < bestAimDist - 0.03) {
            bestAimDist = distToAim;
            stallTicks = 0;
        } else if (++stallTicks > 30) {
            logDebug("Beeline stalled (no approach toward aim for " + stallTicks + " ticks), disengaging");
            logStall(movement, aim);
            return true;
        }
        if (loopAnchorPos == null) {
            loopAnchorPos = playerPos;
            loopWindowTicks = 0;
        } else if (++loopWindowTicks >= 50) {
            if (playerPos.distanceTo(loopAnchorPos) < 2) {
                logDebug("Beeline looping in place (50 ticks, no net displacement), disengaging");
                return true;
            }
            loopAnchorPos = playerPos;
            loopWindowTicks = 0;
        }
        return false;
    }

    // TODO remove, temporary stall diagnostics
    private void logStall(Movement movement, Vec3 aim) {
        Vec3 p = ctx.player().position();
        Vec3 v = ctx.player().getDeltaMovement();
        int feetY = ctx.playerFeet().y;
        logDebug(String.format("stall: pos=(%.3f, %.3f, %.3f) feetY=%d onGround=%b hColl=%b vel=(%.3f, %.3f, %.3f) jump=%b water=%b",
                p.x, p.y, p.z, feetY, ctx.player().onGround(), ctx.player().horizontalCollision, v.x, v.y, v.z, lastJump, ctx.player().isInWater()));
        logDebug("stall: aim=" + positionsAt(engagedAimIdx) + " idx=" + engagedAimIdx + " pathPos=" + pathPosition + " runEnd=" + beelineRunEndMovement()
                + " movement=" + movement.getClass().getSimpleName() + " " + movement.getSrc() + " -> " + movement.getDest());
        logDebug("stall: reachable m0.2=" + reachable(p, feetY, pathPosition, engagedAimIdx, true, 0.2)
                + " m0=" + reachable(p, feetY, pathPosition, engagedAimIdx, true, 0)
                + " jumpHeadroom=" + jumpHeadroomAbovePlayer(p) + " stepJump=" + shouldJumpForStep(p, aim));
        StringBuilder sb = new StringBuilder("stall: path");
        for (int i = Math.max(0, pathPosition - 1); i <= Math.min(path.length() - 1, engagedAimIdx + 1); i++) {
            BetterBlockPos q = positionsAt(i);
            sb.append(' ').append(i).append(':').append(q.x).append(',').append(q.y).append(',').append(q.z);
        }
        logDebug(sb.toString());
    }

    /**
     * Steer the player for this tick. The beeline is the sole driver while engaged — the movement
     * is not ticked — so every input is owned here: rotation, forward, jump (timed for steps,
     * held in water to swim and climb banks), and sprint.
     */
    private void drive(Movement movement, Vec3 aim) {
        Vec3 playerPos = ctx.player().position();
        int feetY = ctx.playerFeet().y;
        Rotation rotation = RotationUtils.calcRotationFromVec3d(
                ctx.playerHead(),
                aim,
                ctx.playerRotations()
        ).withPitch(ctx.playerRotations().getPitch());
        behavior.baritone.getLookBehavior().updateTarget(rotation, false);
        boolean jump;
        if (ctx.player().isInWater()) {
            // hold jump like the traverse movement would: stay at the surface and climb out at banks
            jump = true;
        } else {
            // time the jump for 1-block steps ourselves; with assumeStep (StepUp-style mods) no
            // jump is needed at all — just run through the ledge
            jump = !Baritone.settings().assumeStep.value
                    && ctx.player().onGround()
                    && (aim.y - 0.5 > feetY || movement instanceof MovementAscend)
                    && shouldJumpForStep(playerPos, aim);
        }
        behavior.baritone.getInputOverrideHandler().setInputForceState(Input.MOVE_FORWARD, true);
        behavior.baritone.getInputOverrideHandler().setInputForceState(Input.MOVE_BACK, false);
        behavior.baritone.getInputOverrideHandler().setInputForceState(Input.MOVE_LEFT, false);
        behavior.baritone.getInputOverrideHandler().setInputForceState(Input.MOVE_RIGHT, false);
        behavior.baritone.getInputOverrideHandler().setInputForceState(Input.SNEAK, false);
        behavior.baritone.getInputOverrideHandler().setInputForceState(Input.JUMP, jump);
        lastJump = jump;
        sprintNextTick = shouldSprintBeelining(aim);
        if (!sprintNextTick) {
            ctx.player().setSprinting(false);
        }
        Vec3 vel = ctx.player().getDeltaMovement();
        if (Math.hypot(vel.x, vel.z) > 0.05) {
            // actively moving along a verified beeline is never "taking too long", no matter how
            // far behind the nominal current movement is — long water crossings vastly exceed any
            // single movement's cost estimate
            ticksOnCurrent = 0;
        }
    }

    /**
     * Sprint whenever allowed and the aim direction is within beelineMaxSprintTurn degrees of the
     * current velocity — gentle direction changes are no reason to drop out of a sprint. This
     * replaces the per-movement sprint pessimism entirely while engaged.
     */
    private boolean shouldSprintBeelining(Vec3 aim) {
        if (!new CalculationContext(behavior.baritone, false).canSprint) {
            return false;
        }
        Vec3 vel = ctx.player().getDeltaMovement();
        double speed = Math.hypot(vel.x, vel.z);
        if (speed < 0.05) {
            return true; // barely moving; no momentum to misdirect
        }
        double dx = beelineAim.x - ctx.player().position().x;
        double dz = beelineAim.z - ctx.player().position().z;
        double len = Math.hypot(dx, dz);
        if (len < 0.01) {
            return false;
        }
        double cos = (vel.x * dx + vel.z * dz) / (speed * len);
        return cos >= Math.cos(Math.toRadians(Baritone.settings().beelineMaxSprintTurn.value));
    }

    // ------------------------------------------------------------------
    // base executor hooks
    // ------------------------------------------------------------------

    /**
     * When pursuit steering cuts corners, the player can enter the blocks of movements further
     * along the path without ever standing exactly on the intermediate destinations. Jump the path
     * position forward to the latest movement of the beelineable run whose valid positions contain
     * the player, so skipped movements don't stall waiting for a block we'll never stand on.
     */
    @Override
    protected void beforeTick() {
        if (!Baritone.settings().beeline.value) {
            return;
        }
        int runEnd = beelineRunEndMovement();
        if (state == State.ENGAGED) {
            // while engaged, anchor pathPosition to the run segment nearest the player (forward
            // only). On big cuts our feet may not touch a path block for a long time, and leaving
            // pathPosition on a long-passed movement makes the executor's checks judge a player
            // it no longer describes. Never anchor past the committed aim though: we're steering
            // toward it, so we can't legitimately be beyond it — without this cap, a path that
            // curls back near the player (a lake loop) lets the anchor leap across the loop to a
            // spatially-near-but-logically-far leg no chord ever verified.
            int cap = engagedAimIdx > pathPosition ? Math.min(runEnd, engagedAimIdx) : runEnd;
            int best = nearestRunSegment(ctx.player().position(), ctx.playerFeet().y, cap);
            if (best > pathPosition) {
                pathPosition = best;
                ticksOnCurrent = 0;
                // no clearKeys: clearing every advancement causes micro-stutters mid-line
            }
            return;
        }
        BetterBlockPos whereAmI = ctx.playerFeet();
        for (int i = runEnd - 1; i > pathPosition; i--) {
            if (((Movement) path.movements().get(i)).getValidPositions().contains(whereAmI)) {
                pathPosition = i;
                ticksOnCurrent = 0;
                clearKeys(); // normal movement transition
                break;
            }
        }
    }

    /**
     * While engaged the player is intentionally off-grid mid-cut; the position-recovery scans
     * must not treat that as being lost. When not engaged (including cooldown handoffs
     * mid-corridor) a small tolerance near the current destination smooths the transition; the
     * executor's distance-from-path checks remain in force throughout.
     */
    @Override
    protected boolean positionAcceptable(Movement movement, BetterBlockPos whereAmI) {
        if (!Baritone.settings().beeline.value || !isBeelineable(movement)) {
            return false;
        }
        BetterBlockPos dest = movement.getDest();
        if (Math.abs(whereAmI.y - dest.y) > 1) {
            return false;
        }
        if (state == State.ENGAGED) {
            return true;
        }
        return Math.hypot(ctx.player().position().x - (dest.x + 0.5), ctx.player().position().z - (dest.z + 0.5)) < 3;
    }

    /**
     * An engaged beeline re-verified a straight walkable line back to the path from where we
     * stand, so distance from the raw path doesn't mean we're lost.
     */
    @Override
    protected boolean offPathTolerated() {
        return state == State.ENGAGED;
    }

    @Override
    protected double maxDistFromPath() {
        if (state != State.ENGAGED) {
            return super.maxDistFromPath();
        }
        if (Baritone.settings().beelineDirectToGoal.value) {
            // direct-to-goal cuts may legitimately stray any distance from the path; the per-tick
            // walkability re-verification is the safety net there, not path proximity
            return Double.POSITIVE_INFINITY;
        }
        return Math.max(MAX_DIST_FROM_PATH_BEELINE, Baritone.settings().beelineMaxDeviation.value + 2);
    }

    // ------------------------------------------------------------------
    // aim search
    // ------------------------------------------------------------------

    /**
     * The farthest path position reachable from {@code from} in a straight verified-walkable line,
     * or -1 if not even the next position is. With beelineDirectToGoal the whole run is searched by
     * bisection (try the end, halve toward the player on failure, then refine upward between the
     * best success and nearest failure), ignoring the lookahead radius and deviation limit — the
     * walkability sweep is the only judge. Otherwise a linear scan bounded by beelineRadius and
     * beelineMaxDeviation. The position immediately ahead is always considered so beelining
     * degrades gracefully to per-block steering. Chords may rise or drop at most one level.
     */
    private int farthestReachableIndex(Vec3 from, int feetY, int fromIdx, int runEnd, double margin) {
        if (runEnd <= fromIdx) {
            return -1;
        }
        if (Baritone.settings().beelineDirectToGoal.value) {
            int candidate = runEnd;
            int lastFail = runEnd + 1;
            while (candidate > fromIdx + 1 && !reachable(from, feetY, fromIdx, candidate, true, margin)) {
                lastFail = candidate;
                candidate = (fromIdx + candidate) / 2;
            }
            if (candidate <= fromIdx + 1) {
                return reachable(from, feetY, fromIdx, fromIdx + 1, true, margin) ? fromIdx + 1 : -1;
            }
            // walkability isn't monotonic along the path, so bisection gives "at least this far";
            // refine upward between the known success and the nearest known failure
            int lo = candidate;
            int hi = lastFail;
            while (hi - lo > 1) {
                int mid = (lo + hi) / 2;
                if (reachable(from, feetY, fromIdx, mid, true, margin)) {
                    lo = mid;
                } else {
                    hi = mid;
                }
            }
            return lo;
        }
        double lookahead = Math.max(1, Baritone.settings().beelineRadius.value);
        for (int i = runEnd; i > fromIdx; i--) { // positions index i = dest of movement i-1
            BetterBlockPos pos = positionsAt(i);
            double px = pos.x + 0.5;
            double pz = pos.z + 0.5;
            double dist = Math.hypot(px - from.x, pz - from.z);
            if (dist < 0.5 && i < runEnd) {
                continue; // basically underfoot; aiming at it just tugs us in a circle
            }
            if (dist > lookahead && i > fromIdx + 1) {
                continue;
            }
            if (reachable(from, feetY, fromIdx, i, false, margin)) {
                return i;
            }
        }
        return -1;
    }

    private boolean reachable(Vec3 from, int feetY, int fromIdx, int i, boolean ignoreDeviation, double margin) {
        BetterBlockPos pos = positionsAt(i);
        if (Math.abs(pos.y - feetY) > 1) {
            return false;
        }
        double px = pos.x + 0.5;
        double pz = pos.z + 0.5;
        if (!ignoreDeviation && !chordNearPath(from.x, from.z, px, pz, fromIdx, i)) {
            return false;
        }
        if (!chordRespectsAvoidance(from, px, pz, feetY, fromIdx, i)) {
            return false;
        }
        return cutIsWalkable(from, px, pz, feetY, pos.y, margin);
    }

    /**
     * The #avoidance system prices detours around hostile mobs and spawners into the calculated
     * path; a cut must not undo them. A chord may pass an avoidance sphere no closer than the
     * path positions it replaces do (half a block of slack) — so when the path itself skirts or
     * even crosses a sphere the beeline still engages, but it never shortcuts inward toward the
     * threat. Applies in every mode, including direct-to-goal.
     */
    private boolean chordRespectsAvoidance(Vec3 from, double px, double pz, int feetY, int fromIdx, int toIdx) {
        List<Avoidance> list = currentAvoidances();
        for (int k = 0; k < list.size(); k++) {
            Avoidance a = list.get(k);
            if (a.coefficient() <= 1.0D) {
                continue; // neutral or deliberate attraction
            }
            if (Math.abs(feetY - a.centerY()) > a.radius() + 2) {
                continue; // vertically out of range of the sphere
            }
            double cx = a.centerX() + 0.5;
            double cz = a.centerZ() + 0.5;
            double chordDistSq = distSqPointToSegment(cx, cz, from.x, from.z, px, pz);
            if (chordDistSq >= a.radius() * a.radius()) {
                continue; // chord stays outside the sphere entirely
            }
            double pathMinSq = Double.MAX_VALUE;
            for (int j = fromIdx; j <= toIdx; j++) {
                BetterBlockPos p = positionsAt(j);
                double dx = p.x + 0.5 - cx;
                double dz = p.z + 0.5 - cz;
                pathMinSq = Math.min(pathMinSq, dx * dx + dz * dz);
            }
            double allowed = Math.max(0, Math.sqrt(pathMinSq) - 0.5);
            if (chordDistSq < allowed * allowed) {
                return false;
            }
        }
        return true;
    }

    private List<Avoidance> currentAvoidances() {
        int now = ctx.player().tickCount;
        if (now - avoidanceCacheTick >= 20) {
            avoidanceCacheTick = now;
            avoidances = Avoidance.create(ctx); // empty when the avoidance setting is off
        }
        return avoidances;
    }

    private static double distSqPointToSegment(double px, double pz, double x1, double z1, double x2, double z2) {
        double dx = x2 - x1;
        double dz = z2 - z1;
        double lenSq = dx * dx + dz * dz;
        double t = lenSq == 0 ? 0 : Math.max(0, Math.min(1, ((px - x1) * dx + (pz - z1) * dz) / lenSq));
        double ex = px - (x1 + t * dx);
        double ez = pz - (z1 + t * dz);
        return ex * ex + ez * ez;
    }

    /**
     * Whether every skipped path position stays within beelineMaxDeviation blocks of the straight
     * cut, bounding how far the beeline strays from the calculated path.
     */
    private boolean chordNearPath(double x1, double z1, double x2, double z2, int fromIdx, int toIdx) {
        double maxDeviation = Baritone.settings().beelineMaxDeviation.value;
        double maxDeviationSq = maxDeviation * maxDeviation;
        double dx = x2 - x1;
        double dz = z2 - z1;
        double lenSq = dx * dx + dz * dz;
        for (int j = fromIdx + 1; j < toIdx; j++) {
            BetterBlockPos p = positionsAt(j);
            double px = p.x + 0.5 - x1;
            double pz = p.z + 0.5 - z1;
            double t = lenSq == 0 ? 0 : Math.max(0, Math.min(1, (px * dx + pz * dz) / lenSq));
            double ex = px - t * dx;
            double ez = pz - t * dz;
            if (ex * ex + ez * ez > maxDeviationSq) {
                return false;
            }
        }
        return true;
    }

    /**
     * The run movement whose segment the player is nearest to, by XZ projection onto each
     * segment with height mismatch penalized. Unlike nearest-vertex anchoring this understands
     * being partway along (or past) a segment — if the player has cut ahead of a vertex, the
     * projection lands on the next segment and aim candidates stay strictly in front, instead of
     * steering back toward a point already passed.
     */
    private int nearestRunSegment(Vec3 playerPos, int feetY, int runEnd) {
        int best = pathPosition;
        double bestScore = Double.MAX_VALUE;
        for (int i = pathPosition; i < runEnd; i++) {
            BetterBlockPos a = positionsAt(i);
            BetterBlockPos b = positionsAt(i + 1);
            // never anchor onto a movement whose checks would judge us unreachable
            if (Math.abs(a.y - feetY) > 1 && Math.abs(b.y - feetY) > 1) {
                continue;
            }
            Movement m = (Movement) path.movements().get(i);
            if (m instanceof MovementAscend && m.getSrc().y > feetY) {
                continue;
            }
            double ax = a.x + 0.5;
            double az = a.z + 0.5;
            double dx = b.x - a.x;
            double dz = b.z - a.z;
            double lenSq = dx * dx + dz * dz;
            double t = lenSq == 0 ? 0 : Math.max(0, Math.min(1, ((playerPos.x - ax) * dx + (playerPos.z - az) * dz) / lenSq));
            double ex = playerPos.x - (ax + t * dx);
            double ez = playerPos.z - (az + t * dz);
            double dy = Math.min(Math.abs(a.y - feetY), Math.abs(b.y - feetY));
            double score = ex * ex + ez * ez + dy * dy;
            // <= so ties at a shared vertex prefer the later segment: progress, never regress
            if (score <= bestScore) {
                bestScore = score;
                best = i;
            }
        }
        return best;
    }

    /**
     * @return The exclusive end index of the run of consecutive beelineable movements
     * starting at pathPosition. Positions up to and including this index are covered by the run.
     */
    private int beelineRunEndMovement() {
        int now = ctx.player().tickCount;
        if (now == runEndCacheTick) {
            return runEndCached;
        }
        BlockStateInterface bsi = null;
        int i = pathPosition;
        while (i < path.movements().size()) {
            Movement m = (Movement) path.movements().get(i);
            if (m.toBreakCached == null || m.toPlaceCached == null || m.toWalkIntoCached == null) {
                // the executor only maintains these caches within ±10 of pathPosition; without
                // filling them in, every run would silently end ~10 movements out no matter how
                // far the terrain actually allows. Computed once, they stick until the ±10
                // window reaches and refreshes them — and the per-tick corridor verification is
                // the real safety net regardless.
                if (bsi == null) {
                    bsi = new BlockStateInterface(ctx);
                }
                m.toBreak(bsi);
                m.toPlace(bsi);
                m.toWalkInto(bsi);
            }
            if (!isBeelineable(m)) {
                break;
            }
            i++;
        }
        runEndCacheTick = now;
        runEndCached = i;
        return i;
    }

    private boolean isBeelineable(Movement movement) {
        boolean flat = (movement instanceof MovementTraverse || movement instanceof MovementDiagonal)
                && movement.getDirection().getY() == 0;
        boolean stepUp = movement instanceof MovementAscend && movement.getDirection().getY() == 1;
        // a descend before a genuinely risky edge is left to the movement's own careful slowing.
        // A 1-block MovementFall is included because that's how paths enter deeper water —
        // descend refuses those destinations — and shorelines must not break the run; the
        // corridor's swim branch verifies the water itself.
        boolean stepDown = (movement instanceof MovementDescend && movement.getDirection().getY() == -1
                && !descendRiskyForBeeline((MovementDescend) movement))
                || (movement instanceof MovementFall && movement.getDirection().getY() == -1);
        if (!flat && !stepUp && !stepDown) {
            return false;
        }
        // these caches are refreshed every tick for movements within 10 of pathPosition
        if (movement.toBreakCached == null || !movement.toBreakCached.isEmpty()
                || movement.toPlaceCached == null || !movement.toPlaceCached.isEmpty()
                || movement.toWalkIntoCached == null) {
            return false;
        }
        // walking into water is fine to beeline through; anything else isn't
        // (plain loop: this runs for every movement of the run and streams allocate)
        for (int i = 0; i < movement.toWalkIntoCached.size(); i++) {
            if (!MovementHelper.isWater(BlockStateInterface.get(ctx, movement.toWalkIntoCached.get(i)))) {
                return false;
            }
        }
        return true;
    }

    private BetterBlockPos positionsAt(int i) {
        return path.positions().get(i);
    }

    /**
     * {@link MovementDescend#safeMode()} treats overshooting into any fluid as risky — right for
     * vanilla sprinting, but it flags every shoreline descend (water is a fluid) and would break
     * the run at the water's edge, where beelines deliberately swim. Only non-water hazards past
     * the descend disqualify it here; the corridor and its hazard clearance ring re-verify
     * everything the beeline actually traverses each tick regardless.
     */
    private boolean descendRiskyForBeeline(MovementDescend movement) {
        if (movement.skipToAscend()) {
            return true; // overshoot could glitch into the one-block gap; leave it to the movement
        }
        BlockPos into = movement.getDest().subtract(movement.getSrc().below()).offset(movement.getDest());
        for (int y = 0; y <= 2; y++) {
            BlockState state = BlockStateInterface.get(ctx, into.above(y));
            if (!MovementHelper.isWater(state) && MovementHelper.avoidWalkingInto(state)) {
                return true;
            }
        }
        return false;
    }

    // ------------------------------------------------------------------
    // walkability verification
    // ------------------------------------------------------------------

    /**
     * Whether the straight line from {@code from} to the aim point sweeps only walkable columns.
     * When the endpoints differ by one level (a 1-block jump somewhere along the cut), each column
     * may be walkable at either level, but lower-level columns must also have jump headroom since
     * the jump can happen anywhere along the cut.
     *
     * @param margin extra corridor half-width beyond the hitbox (see {@link #STEERING_MARGINS})
     */
    private boolean cutIsWalkable(Vec3 from, double aimX, double aimZ, int yFrom, int yTo, double margin) {
        int yLow = Math.min(yFrom, yTo);
        int yHigh = Math.max(yFrom, yTo);
        if (yHigh - yLow > 1) {
            return false;
        }
        double halfWidth = 0.301 + margin;
        boolean stepped = yHigh != yLow;
        if (!chordClearOfHazards(from, aimX, aimZ, yLow, yHigh)) {
            return false;
        }
        // grandfather the columns the player currently stands across: barely-on-top of a block,
        // one of our own columns overhangs air and would fail the floor test, disengaging the
        // beeline while we're standing perfectly fine. Being here now is proof enough.
        // 0.299, not 0.301: pressed flush against a wall, a wider box would grandfather the wall
        int sMinX = (int) Math.floor(from.x - 0.299);
        int sMaxX = (int) Math.floor(from.x + 0.299);
        int sMinZ = (int) Math.floor(from.z - 0.299);
        int sMaxZ = (int) Math.floor(from.z + 0.299);
        // exact corridor test, column by column: a column is swept iff the segment enters its
        // square expanded by halfWidth. Unlike sampling points along the line, this can't skip
        // over a column the hitbox only grazes for a moment — exactly the corner clips that wedge
        // the player against blocks the sweep said were clear. (The square expansion is
        // conservative at the corners — rejecting a chord that shaves a solid corner that closely
        // is a feature.) Walk the chord one x strip at a time; within the strip the swept z range
        // is the segment's z extent over the strip's t interval, padded by halfWidth.
        double dx = aimX - from.x;
        double dz = aimZ - from.z;
        int minX = (int) Math.floor(Math.min(from.x, aimX) - halfWidth);
        int maxX = (int) Math.floor(Math.max(from.x, aimX) + halfWidth);
        for (int x = minX; x <= maxX; x++) {
            double t0 = 0;
            double t1 = 1;
            if (Math.abs(dx) < 1e-9) {
                if (from.x < x - halfWidth || from.x > x + 1 + halfWidth) {
                    continue;
                }
            } else {
                double ta = (x - halfWidth - from.x) / dx;
                double tb = (x + 1 + halfWidth - from.x) / dx;
                t0 = Math.max(0, Math.min(ta, tb));
                t1 = Math.min(1, Math.max(ta, tb));
                if (t0 > t1) {
                    continue; // strip not touched by the corridor
                }
            }
            double zA = from.z + dz * t0;
            double zB = from.z + dz * t1;
            int zLo = (int) Math.floor(Math.min(zA, zB) - halfWidth);
            int zHi = (int) Math.floor(Math.max(zA, zB) + halfWidth);
            for (int z = zLo; z <= zHi; z++) {
                if (x >= sMinX && x <= sMaxX && z >= sMinZ && z <= sMaxZ) {
                    // already standing across this column, so floor and body space are proven —
                    // but standing here proves nothing about the ceiling, and if this cut steps
                    // up we jump from right here. Still require the jump headroom.
                    if (stepped && yFrom == yLow && !columnHasJumpHeadroom(x, yLow, z)) {
                        return false;
                    }
                    continue;
                }
                boolean ok = stepped
                        ? columnIsWalkable(x, yLow, z, true) || columnIsWalkable(x, yHigh, z, false)
                        : columnIsWalkable(x, yLow, z, false);
                if (!ok) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Whether the chord's clearance zone — the corridor widened to {@link #HAZARD_CLEARANCE}
     * beyond the hitbox — is entirely free of touch hazards, from one below the feet (a lava pool
     * beside a hole we could drift into) to one above the head. Uses baritone's own
     * {@link MovementHelper#avoidWalkingInto} hazard list (lava, fire, cactus, cobwebs, magma per
     * its setting...), minus water, which beelines legitimately swim through. Same strip walk as
     * the walkability sweep, wider, and with no grandfathering: standing next to lava is not
     * proof that cutting past it is fine.
     */
    private boolean chordClearOfHazards(Vec3 from, double aimX, double aimZ, int yLow, int yHigh) {
        double halfWidth = 0.301 + HAZARD_CLEARANCE;
        double dx = aimX - from.x;
        double dz = aimZ - from.z;
        int minX = (int) Math.floor(Math.min(from.x, aimX) - halfWidth);
        int maxX = (int) Math.floor(Math.max(from.x, aimX) + halfWidth);
        for (int x = minX; x <= maxX; x++) {
            double t0 = 0;
            double t1 = 1;
            if (Math.abs(dx) < 1e-9) {
                if (from.x < x - halfWidth || from.x > x + 1 + halfWidth) {
                    continue;
                }
            } else {
                double ta = (x - halfWidth - from.x) / dx;
                double tb = (x + 1 + halfWidth - from.x) / dx;
                t0 = Math.max(0, Math.min(ta, tb));
                t1 = Math.min(1, Math.max(ta, tb));
                if (t0 > t1) {
                    continue;
                }
            }
            double zA = from.z + dz * t0;
            double zB = from.z + dz * t1;
            int zLo = (int) Math.floor(Math.min(zA, zB) - halfWidth);
            int zHi = (int) Math.floor(Math.max(zA, zB) + halfWidth);
            for (int z = zLo; z <= zHi; z++) {
                for (int y = yLow - 1; y <= yHigh + 1; y++) {
                    BlockState state = BlockStateInterface.get(ctx, new BetterBlockPos(x, y, z));
                    if (!MovementHelper.isWater(state) && MovementHelper.avoidWalkingInto(state)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    private boolean columnIsWalkable(int x, int y, int z, boolean jumpHeadroom) {
        BetterBlockPos feet = new BetterBlockPos(x, y, z);
        BlockState feetState = BlockStateInterface.get(ctx, feet);
        BlockState headState = BlockStateInterface.get(ctx, feet.above());
        if (beelineImpeding(feetState) || beelineImpeding(headState)) {
            return false;
        }
        if (MovementHelper.isWater(feetState)) {
            // swimmable: it's very valid to beeline through water. No floor and no jump headroom
            // needed, just somewhere for the head (air or more water to swim in).
            return MovementHelper.isWater(headState)
                    || MovementHelper.canWalkThrough(ctx, feet.above());
        }
        return MovementHelper.canWalkThrough(ctx, feet)
                && MovementHelper.canWalkThrough(ctx, feet.above())
                && (!jumpHeadroom || columnHasJumpHeadroom(x, y, z))
                && !MovementHelper.avoidWalkingInto(feetState)
                && !MovementHelper.avoidWalkingInto(headState)
                // frost walker freezes still water underfoot as we go, so with the boots on a
                // water floor is walkable ground and chords cross the surface instead of swimming
                && (MovementHelper.canWalkOn(ctx, feet.below())
                        || MovementHelper.canUseFrostWalker(ctx, feet.below()));
    }

    private boolean columnHasJumpHeadroom(int x, int feetY, int z) {
        BetterBlockPos above = new BetterBlockPos(x, feetY + 2, z);
        return MovementHelper.canWalkThrough(ctx, above)
                && !beelineImpeding(BlockStateInterface.get(ctx, above));
    }

    /**
     * Passable per canWalkThrough, but touching it latches or swallows the player (climbables
     * clamp motion the moment the hitbox clips them, powder snow sinks you in). A beeline routed
     * through one jams instead of walking; leave these to the movements that know their costs.
     */
    private static boolean beelineImpeding(BlockState state) {
        return state.is(BlockTags.CLIMBABLE) || state.is(Blocks.POWDER_SNOW);
    }

    // ------------------------------------------------------------------
    // jumping
    // ------------------------------------------------------------------

    /**
     * Physics-timed jumps for beelined steps. With vanilla jump physics the feet clear +1.0 blocks
     * three ticks after takeoff (0.42, 0.75, 1.00), so the perfect moment to jump is when the step
     * face is about three ticks of horizontal travel away — earlier wastes the hop short of the
     * step, later bumps the face and costs sprint momentum.
     */
    private boolean shouldJumpForStep(Vec3 playerPos, Vec3 aim) {
        if (!jumpHeadroomAbovePlayer(playerPos)) {
            return false; // we'd bonk our head before clearing the step
        }
        if (ctx.player().horizontalCollision) {
            return true; // already pressed against the step
        }
        Vec3 vel = ctx.player().getDeltaMovement();
        double speed = Math.hypot(vel.x, vel.z);
        double dirX;
        double dirZ;
        if (speed > 0.08) {
            dirX = vel.x / speed;
            dirZ = vel.z / speed;
        } else {
            double dx = aim.x - playerPos.x;
            double dz = aim.z - playerPos.z;
            double len = Math.hypot(dx, dz);
            if (len < 0.001) {
                return false;
            }
            dirX = dx / len;
            dirZ = dz / len;
        }
        int feetY = ctx.playerFeet().y;
        // distance the hitbox edge travels in the three ticks the jump needs to clear one block
        double reach = Math.max(0.3, speed * 3) + 0.05;
        // scan along our motion for the first obstruction at feet level and jump only once it's
        // a landable step within jumping reach. Three rays across the hitbox width, not just the
        // center: a step corner clipping the edge of the hitbox stops the player just as dead,
        // but a center-only ray never sees it and the jump never comes.
        double perpX = -dirZ;
        double perpZ = dirX;
        for (double side = -0.25; side <= 0.25; side += 0.25) {
            double originX = playerPos.x + perpX * side;
            double originZ = playerPos.z + perpZ * side;
            for (double d = 0.05; d <= reach; d += 0.05) {
                BetterBlockPos ahead = new BetterBlockPos(
                        (int) Math.floor(originX + dirX * (0.3 + d)),
                        feetY,
                        (int) Math.floor(originZ + dirZ * (0.3 + d)));
                if (!MovementHelper.canWalkThrough(ctx, ahead)) {
                    if (MovementHelper.canWalkOn(ctx, ahead)
                            && MovementHelper.canWalkThrough(ctx, ahead.above())
                            && MovementHelper.canWalkThrough(ctx, ahead.above(2))) {
                        return true; // this ray's first obstruction is a landable step
                    }
                    break; // wall on this ray; the other rays may still find a step
                }
            }
        }
        return false;
    }

    /**
     * Whether every column the player's hitbox currently overlaps has passable space two above the
     * feet — i.e. a 1-block jump from right here won't bonk on a ceiling.
     */
    private boolean jumpHeadroomAbovePlayer(Vec3 playerPos) {
        int feetY = ctx.playerFeet().y;
        int minX = (int) Math.floor(playerPos.x - 0.301);
        int maxX = (int) Math.floor(playerPos.x + 0.301);
        int minZ = (int) Math.floor(playerPos.z - 0.301);
        int maxZ = (int) Math.floor(playerPos.z + 0.301);
        for (int x = minX; x <= maxX; x++) {
            for (int z = minZ; z <= maxZ; z++) {
                if (!MovementHelper.canWalkThrough(ctx, new BetterBlockPos(x, feetY + 2, z))) {
                    return false;
                }
            }
        }
        return true;
    }

    // ------------------------------------------------------------------
    // debug rendering
    // ------------------------------------------------------------------

    /**
     * Predicts the trajectory pursuit steering will take, for debug rendering: a greedy
     * string-pull along the beelineable run using the same walkability corridor test as the live
     * steering. Corners drawn as cut are ones that will actually be cut.
     */
    private List<Vec3> computeBeelineRenderPath() {
        if (!Baritone.settings().beeline.value || !Baritone.settings().renderBeeline.value) {
            return null;
        }
        int runEnd = beelineRunEndMovement();
        if (runEnd <= pathPosition) {
            return null;
        }
        int curY = ctx.playerFeet().y;
        List<Vec3> points = new ArrayList<>();
        Vec3 cur = ctx.player().position();
        points.add(new Vec3(cur.x, curY + 0.5, cur.z));
        int idx = pathPosition;
        // cap the segments drawn: each iteration re-sweeps chords block by block, and predicting
        // the trajectory 30+ cuts ahead is pure cost with no informational value. Hitbox-exact
        // tier only, for the same reason.
        while (idx < runEnd && points.size() < 24) {
            int advanced = farthestReachableIndex(cur, curY, idx, runEnd, 0);
            if (advanced == -1) {
                advanced = idx + 1;
            }
            BetterBlockPos pos = positionsAt(advanced);
            cur = new Vec3(pos.x + 0.5, pos.y + 0.5, pos.z + 0.5);
            curY = pos.y;
            points.add(cur);
            idx = advanced;
        }
        return points;
    }
}
