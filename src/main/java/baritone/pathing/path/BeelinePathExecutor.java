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
import baritone.api.IBaritone;
import baritone.api.pathing.calc.IPath;
import baritone.api.pathing.path.IPathExecutor;
import baritone.api.utils.BetterBlockPos;
import baritone.api.utils.Rotation;
import baritone.api.utils.RotationUtils;
import baritone.api.utils.input.Input;
import baritone.behavior.PathingBehavior;
import baritone.pathing.movement.CalculationContext;
import baritone.pathing.movement.Movement;
import baritone.pathing.movement.MovementHelper;
import baritone.pathing.movement.MovementState;
import baritone.pathing.movement.movements.MovementAscend;
import baritone.pathing.movement.movements.MovementDescend;
import baritone.pathing.movement.movements.MovementDiagonal;
import baritone.pathing.movement.movements.MovementTraverse;
import baritone.utils.BlockStateInterface;
import net.minecraft.tags.BlockTags;
import net.minecraft.world.level.block.Blocks;
import net.minecraft.world.level.block.state.BlockState;
import net.minecraft.world.phys.Vec3;
import java.util.ArrayList;
import java.util.List;

/**
 * A {@link PathExecutor} overlaid with "beeline" pure-pursuit steering: instead of walking to the
 * center of every block on the calculated path, aim at the farthest upcoming path position
 * reachable in a straight line whose swept hitbox is re-verified walkable every tick. The
 * calculated path itself is never modified; when any safety gate fails, control falls back to the
 * movement's own exact steering. All beeline state, search, verification, and the relaxations of
 * the base executor's recovery checks live here, wired in through the protected hooks of
 * {@link PathExecutor}.
 */
public class BeelinePathExecutor extends PathExecutor {

    /**
     * Hard distance cap while a beeline is engaged. An engaged beeline re-verifies a straight
     * walkable line back to the path every tick, so the usual limits don't apply — cuts routinely
     * sit 2+ blocks from the nearest path position — but past this even a verified cut is fishy.
     */
    private static final double MAX_DIST_FROM_PATH_BEELINE = 6;

    /**
     * The aim point beelining targeted this tick, or null if it didn't
     * engage. Written on the game thread, read by the render thread for debug visualization.
     */
    private volatile Vec3 beelineAim;

    /**
     * The predicted beeline trajectory (world coordinates, at path render height) for the
     * upcoming portion of the path, recomputed each tick. Null when beelining is disabled.
     */
    private volatile List<Vec3> beelineRenderPath;

    /**
     * Progress watchdog: an engaged beeline relaxes all the executor's stuck-recovery checks, so
     * if the player physically jams (wedged on a trunk, a jump we refuse to make, pushed by a
     * current) nothing would ever break the deadlock. Track the best distance to the current aim;
     * if it stops shrinking, disengage and hand back to vanilla movement for a cooldown.
     */
    private Vec3 beelineWatchAim;
    private double beelineBestAimDist;
    private int beelineStallTicks;
    private int beelineCooldown;

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
     * @return The aim point beelining targeted this tick, or null if it didn't engage
     */
    public Vec3 getBeelineAim() {
        return beelineAim;
    }

    /**
     * Whether the primary executor is actively steering along a verified beeline right now. For
     * movements to relax their own position sanity checks — mid-cut the player is intentionally
     * somewhere the movement wouldn't normally accept.
     */
    public static boolean beelineEngaged(IBaritone baritone) {
        if (!Baritone.settings().beeline.value) {
            return false;
        }
        IPathExecutor current = ((PathingBehavior) baritone.getPathingBehavior()).getCurrent();
        return current instanceof BeelinePathExecutor && ((BeelinePathExecutor) current).getBeelineAim() != null;
    }

    @Override
    protected PathExecutor createExecutor(IPath path) {
        return new BeelinePathExecutor(behavior, path);
    }

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
        if (beelineAim != null) {
            // while a beeline is engaged, anchor pathPosition to the run vertex nearest the
            // player (forward only). On big cuts our feet may not touch a path block for a long
            // time, and leaving pathPosition on a long-passed movement makes its checks judge a
            // player it no longer describes — the per-movement timeout and unreachable checks
            // would cancel a perfectly healthy beeline and force a recalculation.
            int best = nearestRunSegment(ctx.player().position(), ctx.playerFeet().y, runEnd);
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
     * While pursuit steering cuts across blocks that aren't on the path, the player's feet can
     * briefly be in a column no movement claims as a valid position. That's expected — the cut was
     * verified walkable — so don't let the position-recovery scans treat it as being lost, as long
     * as we're at path height and still near the current movement's destination. The executor's
     * distance-from-path checks remain in force.
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
        if (beelineAim != null) {
            // an engaged beeline re-verified a walkable line to the path from right here; don't
            // snap the steering back to the grid just because the current movement's dest is far
            return true;
        }
        return Math.hypot(ctx.player().position().x - (dest.x + 0.5), ctx.player().position().z - (dest.z + 0.5)) < 3;
    }

    /**
     * An engaged beeline (aim found last tick) re-verified a straight walkable line back to the
     * path from where we stand, so distance from the raw path doesn't mean we're lost — cuts
     * routinely exceed the normal limits.
     */
    @Override
    protected boolean offPathTolerated() {
        return Baritone.settings().beeline.value && beelineAim != null;
    }

    @Override
    protected double maxDistFromPath() {
        if (!offPathTolerated()) {
            return super.maxDistFromPath();
        }
        if (Baritone.settings().beelineDirectToGoal.value) {
            // direct-to-goal cuts may legitimately stray any distance from the path; the per-tick
            // walkability re-verification is the safety net there, not path proximity
            return Double.POSITIVE_INFINITY;
        }
        return Math.max(MAX_DIST_FROM_PATH_BEELINE, Baritone.settings().beelineMaxDeviation.value + 2);
    }

    @Override
    protected void onMovementTick(Movement movement) {
        beelineSteering(movement);
        if (!sprintNextTick && beelineSprintKept()) {
            // gentle beeline direction changes are no reason to drop out of a sprint —
            // stopping to rotate a few degrees defeats the point of the straight line
            sprintNextTick = true;
        }
        if (--renderPathThrottle <= 0) {
            beelineRenderPath = computeBeelineRenderPath();
            renderPathThrottle = 5;
        }
        if (beelineAim != null) {
            Vec3 vel = ctx.player().getDeltaMovement();
            if (Math.hypot(vel.x, vel.z) > 0.05) {
                // actively moving along a verified beeline is never "taking too long", no
                // matter how far behind the nominal current movement is — long water
                // crossings vastly exceed any single movement's cost estimate
                ticksOnCurrent = 0;
            }
        }
    }

    /**
     * Pure-pursuit steering: aim at the farthest upcoming path position that is within the
     * lookahead radius and reachable in a straight line whose swept hitbox is verified walkable.
     * This melts corners and straightens zigzag runs instead of walking to the center of every
     * block. Only applies while plainly walking flat traverse/diagonal movements and 1-block
     * ascends/descends; if any condition fails we fall back to the movement's own exact steering
     * for that tick.
     */
    private void beelineSteering(Movement movement) {
        Vec3 previousAim = beelineAim;
        beelineAim = null;
        if (!Baritone.settings().beeline.value) {
            return;
        }
        if (beelineCooldown > 0) {
            // recently stalled against something; let the movement's own steering and the
            // executor's normal recovery checks (timeout, off-path, recalculation) work unimpeded
            beelineCooldown--;
            return;
        }
        if (!isBeelineable(movement)) {
            return;
        }
        MovementState.MovementTarget target = movement.getState().getTarget();
        if (!target.getRotation().isPresent() || target.hasToForceRotations()) {
            return; // breaking, placing, or interacting; the movement needs its exact rotations
        }
        if (MovementHelper.isLiquid(ctx, ctx.playerFeet())
                && !MovementHelper.isWater(BlockStateInterface.get(ctx, ctx.playerFeet()))) {
            return; // lava; water is fine to beeline through
        }
        // keep steering through the hop of a beelined 1-block step or drop — releasing the aim
        // mid-air lets the movement's own steering yank the trajectory toward its block center and
        // we land off the line. Only a real fall (past 1-block-drop speed) disengages.
        if (!ctx.player().onGround() && ctx.player().getDeltaMovement().y < -0.6) {
            return;
        }
        int runEnd = beelineRunEndMovement();
        if (runEnd <= pathPosition) {
            return;
        }
        Vec3 playerPos = ctx.player().position();
        int feetY = ctx.playerFeet().y;
        Vec3 aim = null;
        int aimIdx = farthestReachableIndex(playerPos, feetY, pathPosition, runEnd);
        if (aimIdx != -1) {
            BetterBlockPos pos = positionsAt(aimIdx);
            aim = new Vec3(pos.x + 0.5, pos.y + 0.5, pos.z + 0.5);
        } else if (previousAim != null) {
            // don't snap back to the grid path over a transient failure (mid-hop level change,
            // sampling flicker): if last tick's aim is still directly reachable, keep beelining
            // toward it from where we actually stand
            int prevY = (int) Math.floor(previousAim.y - 0.5);
            if (Math.abs(prevY - feetY) <= 1
                    && Math.hypot(previousAim.x - playerPos.x, previousAim.z - playerPos.z) > 0.7
                    && cutIsWalkable(playerPos, previousAim.x, previousAim.z, feetY, prevY)) {
                aim = previousAim;
            }
        }
        if (aim == null) {
            return;
        }
        // progress watchdog: distance to the aim must keep shrinking. Speed is a poor proxy here
        // (water bobbing and wall-sliding register as motion), so measure actual approach.
        if (beelineWatchAim == null || beelineWatchAim.distanceTo(aim) > 0.9) {
            beelineWatchAim = aim;
            beelineBestAimDist = Double.MAX_VALUE;
            beelineStallTicks = 0;
        }
        double distToAim = playerPos.distanceTo(aim);
        if (distToAim < beelineBestAimDist - 0.03) {
            beelineBestAimDist = distToAim;
            beelineStallTicks = 0;
        } else if (++beelineStallTicks > 30) {
            logDebug("Beeline stalled (no approach toward aim for " + beelineStallTicks + " ticks), disengaging");
            beelineWatchAim = null;
            beelineStallTicks = 0;
            beelineCooldown = 60;
            clearKeys(); // drop any forced jump/movement inputs the beeline was holding
            return;
        }
        Rotation rotation = RotationUtils.calcRotationFromVec3d(
                ctx.playerHead(),
                aim,
                ctx.playerRotations()
        ).withPitch(ctx.playerRotations().getPitch());
        // last updateTarget call in the tick wins, overriding the aim the movement just set
        behavior.baritone.getLookBehavior().updateTarget(rotation, false);
        beelineAim = aim;
        // ascends approached at an angle won't trigger the movement's own jump logic, so time the
        // jump ourselves; the corridor check already verified headroom for it. With assumeStep
        // (StepUp-style mods) no jump is needed at all — just run through the ledge.
        if (!Baritone.settings().assumeStep.value
                && ctx.player().onGround()
                && (aim.y - 0.5 > feetY || movement instanceof MovementAscend)
                && shouldJumpForStep(playerPos, aim)) {
            behavior.baritone.getInputOverrideHandler().setInputForceState(Input.JUMP, true);
        }
    }

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
        // a landable step within jumping reach
        for (double d = 0.05; d <= reach; d += 0.05) {
            BetterBlockPos ahead = new BetterBlockPos(
                    (int) Math.floor(playerPos.x + dirX * (0.3 + d)),
                    feetY,
                    (int) Math.floor(playerPos.z + dirZ * (0.3 + d)));
            if (!MovementHelper.canWalkThrough(ctx, ahead)) {
                return MovementHelper.canWalkOn(ctx, ahead)
                        && MovementHelper.canWalkThrough(ctx, ahead.above())
                        && MovementHelper.canWalkThrough(ctx, ahead.above(2));
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

    /**
     * The farthest path position reachable from {@code from} in a straight verified-walkable line,
     * or -1 if not even the next position is. With beelineDirectToGoal the whole run is searched by
     * bisection (try the end, halve toward the player on failure, then refine upward between the
     * best success and nearest failure), ignoring the lookahead radius and deviation limit — the
     * walkability sweep is the only judge. Otherwise a linear scan bounded by beelineRadius and
     * beelineMaxDeviation. The position immediately ahead is always considered so beelining
     * degrades gracefully to per-block steering. Chords may rise or drop at most one level.
     */
    private int farthestReachableIndex(Vec3 from, int feetY, int fromIdx, int runEnd) {
        if (runEnd <= fromIdx) {
            return -1;
        }
        if (Baritone.settings().beelineDirectToGoal.value) {
            int candidate = runEnd;
            int lastFail = runEnd + 1;
            while (candidate > fromIdx + 1 && !reachable(from, feetY, fromIdx, candidate, true)) {
                lastFail = candidate;
                candidate = (fromIdx + candidate) / 2;
            }
            if (candidate <= fromIdx + 1) {
                return reachable(from, feetY, fromIdx, fromIdx + 1, true) ? fromIdx + 1 : -1;
            }
            // walkability isn't monotonic along the path, so bisection gives "at least this far";
            // refine upward between the known success and the nearest known failure
            int lo = candidate;
            int hi = lastFail;
            while (hi - lo > 1) {
                int mid = (lo + hi) / 2;
                if (reachable(from, feetY, fromIdx, mid, true)) {
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
            if (reachable(from, feetY, fromIdx, i, false)) {
                return i;
            }
        }
        return -1;
    }

    /**
     * Whether the engaged beeline justifies keeping the sprint: the aim direction is within
     * beelineMaxSprintTurn degrees of our current velocity, so the turn is gentle enough to take
     * at full speed. This overrides the executor's usual per-movement sprint pessimism (e.g.
     * descend-into-turn combos it would slow down for).
     */
    private boolean beelineSprintKept() {
        if (beelineAim == null) {
            return false;
        }
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

    private boolean reachable(Vec3 from, int feetY, int fromIdx, int i, boolean ignoreDeviation) {
        BetterBlockPos pos = positionsAt(i);
        if (Math.abs(pos.y - feetY) > 1) {
            return false;
        }
        double px = pos.x + 0.5;
        double pz = pos.z + 0.5;
        if (!ignoreDeviation && !chordNearPath(from.x, from.z, px, pz, fromIdx, i)) {
            return false;
        }
        return cutIsWalkable(from, px, pz, feetY, pos.y);
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
     * @return The exclusive end index of the run of consecutive beelineable movements
     * starting at pathPosition. Positions up to and including this index are covered by the run.
     */
    private int beelineRunEndMovement() {
        int now = ctx.player().tickCount;
        if (now == runEndCacheTick) {
            return runEndCached;
        }
        int i = pathPosition;
        while (i < path.movements().size() && isBeelineable((Movement) path.movements().get(i))) {
            i++;
        }
        runEndCacheTick = now;
        runEndCached = i;
        return i;
    }

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
        // the trajectory 30+ cuts ahead is pure cost with no informational value
        while (idx < runEnd && points.size() < 24) {
            int advanced = farthestReachableIndex(cur, curY, idx, runEnd);
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

    private BetterBlockPos positionsAt(int i) {
        return path.positions().get(i);
    }

    private boolean isBeelineable(Movement movement) {
        boolean flat = (movement instanceof MovementTraverse || movement instanceof MovementDiagonal)
                && movement.getDirection().getY() == 0;
        boolean stepUp = movement instanceof MovementAscend && movement.getDirection().getY() == 1;
        // a descend in safe mode is deliberately slowing before a risky edge; leave it alone
        boolean stepDown = movement instanceof MovementDescend && movement.getDirection().getY() == -1
                && !((MovementDescend) movement).safeMode();
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

    /**
     * Whether the straight line from {@code from} to the aim point sweeps only walkable columns.
     * When the endpoints differ by one level (a 1-block jump somewhere along the cut), each column
     * may be walkable at either level, but lower-level columns must also have jump headroom since
     * the jump can happen anywhere along the cut.
     */
    private boolean cutIsWalkable(Vec3 from, double aimX, double aimZ, int yFrom, int yTo) {
        int yLow = Math.min(yFrom, yTo);
        int yHigh = Math.max(yFrom, yTo);
        if (yHigh - yLow > 1) {
            return false;
        }
        boolean stepped = yHigh != yLow;
        // grandfather the columns the player currently stands across: barely-on-top of a block,
        // one of our own columns overhangs air and would fail the floor test, disengaging the
        // beeline while we're standing perfectly fine. Being here now is proof enough.
        int sMinX = (int) Math.floor(from.x - 0.301);
        int sMaxX = (int) Math.floor(from.x + 0.301);
        int sMinZ = (int) Math.floor(from.z - 0.301);
        int sMaxZ = (int) Math.floor(from.z + 0.301);
        double dx = aimX - from.x;
        double dz = aimZ - from.z;
        int steps = Math.max(1, (int) Math.ceil(Math.hypot(dx, dz) / 0.25));
        for (int i = 0; i <= steps; i++) {
            double px = from.x + dx * i / steps;
            double pz = from.z + dz * i / steps;
            // every block column the player's 0.6 wide hitbox overlaps at this point on the line
            int minX = (int) Math.floor(px - 0.301);
            int maxX = (int) Math.floor(px + 0.301);
            int minZ = (int) Math.floor(pz - 0.301);
            int maxZ = (int) Math.floor(pz + 0.301);
            for (int x = minX; x <= maxX; x++) {
                for (int z = minZ; z <= maxZ; z++) {
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
                && MovementHelper.canWalkOn(ctx, feet.below());
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
}
