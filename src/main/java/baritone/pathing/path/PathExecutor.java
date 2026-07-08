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
import baritone.api.pathing.movement.ActionCosts;
import baritone.api.pathing.movement.IMovement;
import baritone.api.pathing.movement.MovementStatus;
import baritone.api.pathing.path.IPathExecutor;
import baritone.api.utils.*;
import baritone.api.utils.input.Input;
import baritone.behavior.PathingBehavior;
import baritone.pathing.calc.AbstractNodeCostSearch;
import baritone.pathing.movement.CalculationContext;
import baritone.pathing.movement.Movement;
import baritone.pathing.movement.MovementHelper;
import baritone.pathing.movement.MovementState;
import baritone.pathing.movement.movements.*;
import baritone.utils.BlockStateInterface;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Vec3i;
import net.minecraft.util.Tuple;
import net.minecraft.world.phys.Vec3;
import java.util.*;

import static baritone.api.pathing.movement.MovementStatus.*;

/**
 * Behavior to execute a precomputed path
 *
 * @author leijurv
 */
public class PathExecutor implements IPathExecutor, Helper {

    private static final double MAX_MAX_DIST_FROM_PATH = 3;
    private static final double MAX_DIST_FROM_PATH = 2;

    /**
     * Hard distance cap while a beeline is engaged. An engaged beeline re-verifies a straight
     * walkable line back to the path every tick, so the usual limits don't apply — cuts routinely
     * sit 2+ blocks from the nearest path position — but past this even a verified cut is fishy.
     */
    private static final double MAX_DIST_FROM_PATH_BEELINE = 6;

    /**
     * Default value is equal to 10 seconds. It's find to decrease it, but it must be at least 5.5s (110 ticks).
     * For more information, see issue #102.
     *
     * @see <a href="https://github.com/cabaletta/baritone/issues/102">Issue #102</a>
     * @see <a href="https://i.imgur.com/5s5GLnI.png">Anime</a>
     */
    private static final double MAX_TICKS_AWAY = 200;

    private final IPath path;
    private int pathPosition;
    private int ticksAway;
    private int ticksOnCurrent;
    private Double currentMovementOriginalCostEstimate;
    private Integer costEstimateIndex;
    private boolean failed;
    private boolean recalcBP = true;
    private HashSet<BlockPos> toBreak = new HashSet<>();
    private HashSet<BlockPos> toPlace = new HashSet<>();
    private HashSet<BlockPos> toWalkInto = new HashSet<>();

    private final PathingBehavior behavior;
    private final IPlayerContext ctx;

    private boolean sprintNextTick;

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

    public PathExecutor(PathingBehavior behavior, IPath path) {
        this.behavior = behavior;
        this.ctx = behavior.ctx;
        this.path = path;
        this.pathPosition = 0;
    }

    /**
     * Tick this executor
     *
     * @return True if a movement just finished (and the player is therefore in a "stable" state, like,
     * not sneaking out over lava), false otherwise
     */
    public boolean onTick() {
        if (pathPosition == path.length() - 1) {
            pathPosition++;
        }
        if (pathPosition >= path.length()) {
            return true; // stop bugging me, I'm done
        }
        advanceThroughBeeline();
        Movement movement = (Movement) path.movements().get(pathPosition);
        BetterBlockPos whereAmI = ctx.playerFeet();
        if (!movement.getValidPositions().contains(whereAmI) && !withinBeelineCorridor(movement, whereAmI)) {
            for (int i = 0; i < pathPosition && i < path.length(); i++) {//this happens for example when you lag out and get teleported back a couple blocks
                if (((Movement) path.movements().get(i)).getValidPositions().contains(whereAmI)) {
                    int previousPos = pathPosition;
                    pathPosition = i;
                    for (int j = pathPosition; j <= previousPos; j++) {
                        path.movements().get(j).reset();
                    }
                    onChangeInPathPosition();
                    onTick();
                    return false;
                }
            }
            for (int i = pathPosition + 3; i < path.length() - 1; i++) { //dont check pathPosition+1. the movement tells us when it's done (e.g. sneak placing)
                // also don't check pathPosition+2 because reasons
                if (((Movement) path.movements().get(i)).getValidPositions().contains(whereAmI)) {
                    if (i - pathPosition > 2) {
                        logDebug("Skipping forward " + (i - pathPosition) + " steps, to " + i);
                    }
                    //System.out.println("Double skip sundae");
                    pathPosition = i - 1;
                    onChangeInPathPosition();
                    onTick();
                    return false;
                }
            }
        }
        Tuple<Double, BlockPos> status = closestPathPos(path);
        // an engaged beeline (aim found last tick) re-verified a straight walkable line back to
        // the path from where we stand, so distance from the raw path doesn't mean we're lost —
        // cuts routinely exceed the normal limits. Judge against the beeline instead: engaged
        // means fine (within a hard cap), disengaged means the normal strictness applies.
        boolean beelining = Baritone.settings().beeline.value && beelineAim != null;
        if (possiblyOffPath(status, MAX_DIST_FROM_PATH)) {
            if (beelining) {
                ticksAway = 0;
            } else {
                ticksAway++;
                System.out.println("FAR AWAY FROM PATH FOR " + ticksAway + " TICKS. Current distance: " + status.getA() + ". Threshold: " + MAX_DIST_FROM_PATH);
                if (ticksAway > MAX_TICKS_AWAY) {
                    logDebug("Too far away from path for too long, cancelling path");
                    cancel();
                    return false;
                }
            }
        } else {
            ticksAway = 0;
        }
        double beelineCap = Math.max(MAX_DIST_FROM_PATH_BEELINE, Baritone.settings().beelineMaxDeviation.value + 2);
        if (possiblyOffPath(status, beelining ? beelineCap : MAX_MAX_DIST_FROM_PATH)) { // ok, stop right away, we're way too far.
            logDebug("too far from path");
            cancel();
            return false;
        }
        //long start = System.nanoTime() / 1000000L;
        BlockStateInterface bsi = new BlockStateInterface(ctx);
        for (int i = pathPosition - 10; i < pathPosition + 10; i++) {
            if (i < 0 || i >= path.movements().size()) {
                continue;
            }
            Movement m = (Movement) path.movements().get(i);
            List<BlockPos> prevBreak = m.toBreak(bsi);
            List<BlockPos> prevPlace = m.toPlace(bsi);
            List<BlockPos> prevWalkInto = m.toWalkInto(bsi);
            m.resetBlockCache();
            if (!prevBreak.equals(m.toBreak(bsi))) {
                recalcBP = true;
            }
            if (!prevPlace.equals(m.toPlace(bsi))) {
                recalcBP = true;
            }
            if (!prevWalkInto.equals(m.toWalkInto(bsi))) {
                recalcBP = true;
            }
        }
        if (recalcBP) {
            HashSet<BlockPos> newBreak = new HashSet<>();
            HashSet<BlockPos> newPlace = new HashSet<>();
            HashSet<BlockPos> newWalkInto = new HashSet<>();
            for (int i = pathPosition; i < path.movements().size(); i++) {
                Movement m = (Movement) path.movements().get(i);
                newBreak.addAll(m.toBreak(bsi));
                newPlace.addAll(m.toPlace(bsi));
                newWalkInto.addAll(m.toWalkInto(bsi));
            }
            toBreak = newBreak;
            toPlace = newPlace;
            toWalkInto = newWalkInto;
            recalcBP = false;
        }
        /*long end = System.nanoTime() / 1000000L;
        if (end - start > 0) {
            System.out.println("Recalculating break and place took " + (end - start) + "ms");
        }*/
        if (pathPosition < path.movements().size() - 1) {
            IMovement next = path.movements().get(pathPosition + 1);
            if (!behavior.baritone.bsi.worldContainsLoadedChunk(next.getDest().x, next.getDest().z)) {
                logDebug("Pausing since destination is at edge of loaded chunks");
                clearKeys();
                return true;
            }
        }
        boolean canCancel = movement.safeToCancel();
        if (costEstimateIndex == null || costEstimateIndex != pathPosition) {
            costEstimateIndex = pathPosition;
            // do this only once, when the movement starts, and deliberately get the cost as cached when this path was calculated, not the cost as it is right now
            currentMovementOriginalCostEstimate = movement.getCost();
            for (int i = 1; i < Baritone.settings().costVerificationLookahead.value && pathPosition + i < path.length() - 1; i++) {
                if (((Movement) path.movements().get(pathPosition + i)).calculateCost(behavior.secretInternalGetCalculationContext()) >= ActionCosts.COST_INF && canCancel) {
                    logDebug("Something has changed in the world and a future movement has become impossible. Cancelling.");
                    cancel();
                    return true;
                }
            }
        }
        double currentCost = movement.recalculateCost(behavior.secretInternalGetCalculationContext());
        if (currentCost >= ActionCosts.COST_INF && canCancel) {
            logDebug("Something has changed in the world and this movement has become impossible. Cancelling.");
            cancel();
            return true;
        }
        if (!movement.calculatedWhileLoaded() && currentCost - currentMovementOriginalCostEstimate > Baritone.settings().maxCostIncrease.value && canCancel) {
            // don't do this if the movement was calculated while loaded
            // that means that this isn't a cache error, it's just part of the path interfering with a later part
            logDebug("Original cost " + currentMovementOriginalCostEstimate + " current cost " + currentCost + ". Cancelling.");
            cancel();
            return true;
        }
        if (shouldPause()) {
            logDebug("Pausing since current best path is a backtrack");
            clearKeys();
            return true;
        }
        MovementStatus movementStatus = movement.update();
        if (movementStatus == UNREACHABLE || movementStatus == FAILED) {
            logDebug("Movement returns status " + movementStatus);
            cancel();
            return true;
        }
        if (movementStatus == SUCCESS) {
            //System.out.println("Movement done, next path");
            pathPosition++;
            onChangeInPathPosition();
            onTick();
            return true;
        } else {
            sprintNextTick = shouldSprintNextTick();
            if (!sprintNextTick) {
                ctx.player().setSprinting(false); // letting go of control doesn't make you stop sprinting actually
            }
            beelineSteering(movement);
            beelineRenderPath = computeBeelineRenderPath();
            ticksOnCurrent++;
            if (ticksOnCurrent > currentMovementOriginalCostEstimate + Baritone.settings().movementTimeoutTicks.value) {
                // only cancel if the total time has exceeded the initial estimate
                // as you break the blocks required, the remaining cost goes down, to the point where
                // ticksOnCurrent is greater than recalculateCost + 100
                // this is why we cache cost at the beginning, and don't recalculate for this comparison every tick
                logDebug("This movement has taken too long (" + ticksOnCurrent + " ticks, expected " + currentMovementOriginalCostEstimate + "). Cancelling.");
                cancel();
                return true;
            }
        }
        return canCancel; // movement is in progress, but if it reports cancellable, PathingBehavior is good to cut onto the next path
    }

    private Tuple<Double, BlockPos> closestPathPos(IPath path) {
        double best = -1;
        BlockPos bestPos = null;
        for (IMovement movement : path.movements()) {
            for (BlockPos pos : ((Movement) movement).getValidPositions()) {
                double dist = VecUtils.entityDistanceToCenter(ctx.player(), pos);
                if (dist < best || best == -1) {
                    best = dist;
                    bestPos = pos;
                }
            }
        }
        return new Tuple<>(best, bestPos);
    }

    private boolean shouldPause() {
        Optional<AbstractNodeCostSearch> current = behavior.getInProgress();
        if (!current.isPresent()) {
            return false;
        }
        if (!ctx.player().onGround()) {
            return false;
        }
        if (!MovementHelper.canWalkOn(ctx, ctx.playerFeet().below())) {
            // we're in some kind of sketchy situation, maybe parkouring
            return false;
        }
        if (!MovementHelper.canWalkThrough(ctx, ctx.playerFeet()) || !MovementHelper.canWalkThrough(ctx, ctx.playerFeet().above())) {
            // suffocating?
            return false;
        }
        if (!path.movements().get(pathPosition).safeToCancel()) {
            return false;
        }
        Optional<IPath> currentBest = current.get().bestPathSoFar();
        if (!currentBest.isPresent()) {
            return false;
        }
        List<BetterBlockPos> positions = currentBest.get().positions();
        if (positions.size() < 3) {
            return false; // not long enough yet to justify pausing, its far from certain we'll actually take this route
        }
        // the first block of the next path will always overlap
        // no need to pause our very last movement when it would have otherwise cleanly exited with MovementStatus SUCCESS
        positions = positions.subList(1, positions.size());
        return positions.contains(ctx.playerFeet());
    }

    private boolean possiblyOffPath(Tuple<Double, BlockPos> status, double leniency) {
        double distanceFromPath = status.getA();
        if (distanceFromPath > leniency) {
            // when we're midair in the middle of a fall, we're very far from both the beginning and the end, but we aren't actually off path
            if (path.movements().get(pathPosition) instanceof MovementFall) {
                BlockPos fallDest = path.positions().get(pathPosition + 1); // .get(pathPosition) is the block we fell off of
                return VecUtils.entityFlatDistanceToCenter(ctx.player(), fallDest) >= leniency; // ignore Y by using flat distance
            } else {
                return true;
            }
        } else {
            return false;
        }
    }

    /**
     * Regardless of current path position, snap to the current player feet if possible
     *
     * @return Whether or not it was possible to snap to the current player feet
     */
    public boolean snipsnapifpossible() {
        if (!ctx.player().onGround() && ctx.world().getFluidState(ctx.playerFeet()).isEmpty()) {
            // if we're falling in the air, and not in water, don't splice
            return false;
        } else {
            // we are either onGround or in liquid
            if (ctx.player().getDeltaMovement().y < -0.1) {
                // if we are strictly moving downwards (not stationary)
                // we could be falling through water, which could be unsafe to splice
                return false; // so don't
            }
        }
        int index = path.positions().indexOf(ctx.playerFeet());
        if (index == -1) {
            return false;
        }
        pathPosition = index; // jump directly to current position
        clearKeys();
        return true;
    }

    private boolean shouldSprintNextTick() {
        boolean requested = behavior.baritone.getInputOverrideHandler().isInputForcedDown(Input.SPRINT);

        // we'll take it from here, no need for minecraft to see we're holding down control and sprint for us
        behavior.baritone.getInputOverrideHandler().setInputForceState(Input.SPRINT, false);

        // first and foremost, if allowSprint is off, or if we don't have enough hunger, don't try and sprint
        if (!new CalculationContext(behavior.baritone, false).canSprint) {
            return false;
        }
        IMovement current = path.movements().get(pathPosition);

        // traverse requests sprinting, so we need to do this check first
        if (current instanceof MovementTraverse && pathPosition < path.length() - 3) {
            IMovement next = path.movements().get(pathPosition + 1);
            if (next instanceof MovementAscend && sprintableAscend(ctx, (MovementTraverse) current, (MovementAscend) next, path.movements().get(pathPosition + 2))) {
                if (skipNow(ctx, current)) {
                    logDebug("Skipping traverse to straight ascend");
                    pathPosition++;
                    onChangeInPathPosition();
                    onTick();
                    behavior.baritone.getInputOverrideHandler().setInputForceState(Input.JUMP, true);
                    return true;
                } else {
                    logDebug("Too far to the side to safely sprint ascend");
                }
            }
        }

        // if the movement requested sprinting, then we're done
        if (requested) {
            return true;
        }

        // however, descend and ascend don't request sprinting, because they don't know the context of what movement comes after it
        if (current instanceof MovementDescend) {

            if (pathPosition < path.length() - 2) {
                // keep this out of onTick, even if that means a tick of delay before it has an effect
                IMovement next = path.movements().get(pathPosition + 1);
                if (MovementHelper.canUseFrostWalker(ctx, next.getDest().below())) {
                    // frostwalker only works if you cross the edge of the block on ground so in some cases we may not overshoot
                    // Since MovementDescend can't know the next movement we have to tell it
                    if (next instanceof MovementTraverse || next instanceof MovementParkour) {
                        boolean couldPlaceInstead = Baritone.settings().allowPlace.value && behavior.baritone.getInventoryBehavior().hasGenericThrowaway() && next instanceof MovementParkour; // traverse doesn't react fast enough
                        // this is true if the next movement does not ascend or descends and goes into the same cardinal direction (N-NE-E-SE-S-SW-W-NW) as the descend
                        // in that case current.getDirection() is e.g. (0, -1, 1) and next.getDirection() is e.g. (0, 0, 3) so the cross product of (0, 0, 1) and (0, 0, 3) is taken, which is (0, 0, 0) because the vectors are colinear (don't form a plane)
                        // since movements in exactly the opposite direction (e.g. descend (0, -1, 1) and traverse (0, 0, -1)) would also pass this check we also have to rule out that case
                        // we can do that by adding the directions because traverse is always 1 long like descend and parkour can't jump through current.getSrc().down()
                        boolean sameFlatDirection = !current.getDirection().above().offset(next.getDirection()).equals(BlockPos.ZERO)
                                && current.getDirection().above().cross(next.getDirection()).equals(BlockPos.ZERO); // here's why you learn maths in school
                        if (sameFlatDirection && !couldPlaceInstead) {
                            ((MovementDescend) current).forceSafeMode();
                        }
                    }
                }
            }
            if (((MovementDescend) current).safeMode() && !((MovementDescend) current).skipToAscend()) {
                logDebug("Sprinting would be unsafe");
                return false;
            }

            if (pathPosition < path.length() - 2) {
                IMovement next = path.movements().get(pathPosition + 1);
                if (next instanceof MovementAscend && current.getDirection().above().equals(next.getDirection().below())) {
                    // a descend then an ascend in the same direction
                    pathPosition++;
                    onChangeInPathPosition();
                    onTick();
                    // okay to skip clearKeys and / or onChangeInPathPosition here since this isn't possible to repeat, since it's asymmetric
                    logDebug("Skipping descend to straight ascend");
                    return true;
                }
                if (canSprintFromDescendInto(ctx, current, next)) {

                    if (next instanceof MovementDescend && pathPosition < path.length() - 3) {
                        IMovement next_next = path.movements().get(pathPosition + 2);
                        if (next_next instanceof MovementDescend && !canSprintFromDescendInto(ctx, next, next_next)) {
                            return false;
                        }

                    }
                    if (ctx.playerFeet().equals(current.getDest())) {
                        pathPosition++;
                        onChangeInPathPosition();
                        onTick();
                    }

                    return true;
                }
                //logDebug("Turning off sprinting " + movement + " " + next + " " + movement.getDirection() + " " + next.getDirection().down() + " " + next.getDirection().down().equals(movement.getDirection()));
            }
        }
        if (current instanceof MovementAscend && pathPosition != 0) {
            IMovement prev = path.movements().get(pathPosition - 1);
            if (prev instanceof MovementDescend && prev.getDirection().above().equals(current.getDirection().below())) {
                BlockPos center = current.getSrc().above();
                // playerFeet adds 0.1251 to account for soul sand
                // farmland is 0.9375
                // 0.07 is to account for farmland
                if (ctx.player().position().y >= center.getY() - 0.07) {
                    behavior.baritone.getInputOverrideHandler().setInputForceState(Input.JUMP, false);
                    return true;
                }
            }
            if (pathPosition < path.length() - 2 && prev instanceof MovementTraverse && sprintableAscend(ctx, (MovementTraverse) prev, (MovementAscend) current, path.movements().get(pathPosition + 1))) {
                return true;
            }
        }
        if (current instanceof MovementFall) {
            Tuple<Vec3, BlockPos> data = overrideFall((MovementFall) current);
            if (data != null) {
                BetterBlockPos fallDest = new BetterBlockPos(data.getB());
                if (!path.positions().contains(fallDest)) {
                    throw new IllegalStateException(String.format(
                            "Fall override at %s %s %s returned illegal destination %s %s %s",
                            current.getSrc(), fallDest));
                }
                if (ctx.playerFeet().equals(fallDest)) {
                    pathPosition = path.positions().indexOf(fallDest);
                    onChangeInPathPosition();
                    onTick();
                    return true;
                }
                clearKeys();
                behavior.baritone.getLookBehavior().updateTarget(RotationUtils.calcRotationFromVec3d(ctx.playerHead(), data.getA(), ctx.playerRotations()), false);
                behavior.baritone.getInputOverrideHandler().setInputForceState(Input.MOVE_FORWARD, true);
                return true;
            }
        }
        return false;
    }

    private Tuple<Vec3, BlockPos> overrideFall(MovementFall movement) {
        Vec3i dir = movement.getDirection();
        if (dir.getY() < -3) {
            return null;
        }
        if (!movement.toBreakCached.isEmpty()) {
            return null; // it's breaking
        }
        Vec3i flatDir = new Vec3i(dir.getX(), 0, dir.getZ());
        int i;
        outer:
        for (i = pathPosition + 1; i < path.length() - 1 && i < pathPosition + 3; i++) {
            IMovement next = path.movements().get(i);
            if (!(next instanceof MovementTraverse)) {
                break;
            }
            if (!flatDir.equals(next.getDirection())) {
                break;
            }
            for (int y = next.getDest().y; y <= movement.getSrc().y + 1; y++) {
                BlockPos chk = new BlockPos(next.getDest().x, y, next.getDest().z);
                if (!MovementHelper.fullyPassable(ctx, chk)) {
                    break outer;
                }
            }
            if (!MovementHelper.canWalkOn(ctx, next.getDest().below())) {
                break;
            }
        }
        i--;
        if (i == pathPosition) {
            return null; // no valid extension exists
        }
        double len = i - pathPosition - 0.4;
        return new Tuple<>(
                new Vec3(flatDir.getX() * len + movement.getDest().x + 0.5, movement.getDest().y, flatDir.getZ() * len + movement.getDest().z + 0.5),
                movement.getDest().offset(flatDir.getX() * (i - pathPosition), 0, flatDir.getZ() * (i - pathPosition)));
    }

    private static boolean skipNow(IPlayerContext ctx, IMovement current) {
        double offTarget = Math.abs(current.getDirection().getX() * (current.getSrc().z + 0.5D - ctx.player().position().z)) + Math.abs(current.getDirection().getZ() * (current.getSrc().x + 0.5D - ctx.player().position().x));
        if (offTarget > 0.1) {
            return false;
        }
        // we are centered
        BlockPos headBonk = current.getSrc().subtract(current.getDirection()).above(2);
        if (MovementHelper.fullyPassable(ctx, headBonk)) {
            return true;
        }
        // wait 0.3
        double flatDist = Math.abs(current.getDirection().getX() * (headBonk.getX() + 0.5D - ctx.player().position().x)) + Math.abs(current.getDirection().getZ() * (headBonk.getZ() + 0.5 - ctx.player().position().z));
        return flatDist > 0.8;
    }

    private static boolean sprintableAscend(IPlayerContext ctx, MovementTraverse current, MovementAscend next, IMovement nextnext) {
        if (!Baritone.settings().sprintAscends.value) {
            return false;
        }
        if (!current.getDirection().equals(next.getDirection().below())) {
            return false;
        }
        if (nextnext.getDirection().getX() != next.getDirection().getX() || nextnext.getDirection().getZ() != next.getDirection().getZ()) {
            return false;
        }
        if (!MovementHelper.canWalkOn(ctx, current.getDest().below())) {
            return false;
        }
        if (!MovementHelper.canWalkOn(ctx, next.getDest().below())) {
            return false;
        }
        if (!next.toBreakCached.isEmpty()) {
            return false; // it's breaking
        }
        for (int x = 0; x < 2; x++) {
            for (int y = 0; y < 3; y++) {
                BlockPos chk = current.getSrc().above(y);
                if (x == 1) {
                    chk = chk.offset(current.getDirection());
                }
                if (!MovementHelper.fullyPassable(ctx, chk)) {
                    return false;
                }
            }
        }
        if (MovementHelper.avoidWalkingInto(ctx.world().getBlockState(current.getSrc().above(3)))) {
            return false;
        }
        return !MovementHelper.avoidWalkingInto(ctx.world().getBlockState(next.getDest().above(2))); // codacy smh my head
    }

    private static boolean canSprintFromDescendInto(IPlayerContext ctx, IMovement current, IMovement next) {
        if (next instanceof MovementDescend && next.getDirection().equals(current.getDirection())) {
            return true;
        }
        if (!MovementHelper.canWalkOn(ctx, current.getDest().offset(current.getDirection()))) {
            return false;
        }
        if (next instanceof MovementTraverse && next.getDirection().equals(current.getDirection())) {
            return true;
        }
        return next instanceof MovementDiagonal && Baritone.settings().allowOvershootDiagonalDescend.value;
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
        beelineAim = null;
        if (!Baritone.settings().beeline.value) {
            return;
        }
        if (!isBeelineable(movement)) {
            return;
        }
        MovementState.MovementTarget target = movement.getState().getTarget();
        if (!target.getRotation().isPresent() || target.hasToForceRotations()) {
            return; // breaking, placing, or interacting; the movement needs its exact rotations
        }
        if (MovementHelper.isLiquid(ctx, ctx.playerFeet())) {
            return;
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
        Vec3 aim = pursuitAim(playerPos, runEnd);
        if (aim == null) {
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
        // jump ourselves; the corridor check already verified headroom for it
        if (ctx.player().onGround()
                && (aim.y - 0.5 > ctx.playerFeet().y || movement instanceof MovementAscend)
                && shouldJumpForStep(playerPos, aim)) {
            behavior.baritone.getInputOverrideHandler().setInputForceState(Input.JUMP, true);
        }
    }

    /**
     * Jump timing for beelined steps: jump when a 1-high step face is imminent along our actual
     * motion, instead of waiting for the collision — bumping the step first costs sprint momentum
     * and mistimes the hop when running up slopes at an angle.
     */
    private boolean shouldJumpForStep(Vec3 playerPos, Vec3 aim) {
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
        // probe just beyond the hitbox edge along our motion for a step we can land on
        for (double lead : new double[]{0.45, 0.75}) {
            BetterBlockPos ahead = new BetterBlockPos(
                    (int) Math.floor(playerPos.x + dirX * lead),
                    feetY,
                    (int) Math.floor(playerPos.z + dirZ * lead));
            if (!MovementHelper.canWalkThrough(ctx, ahead)
                    && MovementHelper.canWalkOn(ctx, ahead)
                    && MovementHelper.canWalkThrough(ctx, ahead.above())
                    && MovementHelper.canWalkThrough(ctx, ahead.above(2))) {
                return true;
            }
        }
        return false;
    }

    /**
     * The farthest path position (as a centered aim point) within the lookahead radius that can be
     * reached from the player in a straight verified-walkable line, or null if not even the next
     * position can. The position immediately ahead is always considered regardless of radius so
     * beelining degrades gracefully to per-block steering. Chords may rise or drop at most one
     * level, and must stay near the calculated path so the executor's distance-from-path safety
     * checks can't trip on a beeline.
     */
    private Vec3 pursuitAim(Vec3 from, int runEndMovement) {
        double lookahead = Math.max(1, Baritone.settings().beelineRadius.value);
        int feetY = ctx.playerFeet().y;
        for (int i = runEndMovement; i > pathPosition; i--) { // positions index i = dest of movement i-1
            BetterBlockPos pos = positionsAt(i);
            if (Math.abs(pos.y - feetY) > 1) {
                continue;
            }
            double px = pos.x + 0.5;
            double pz = pos.z + 0.5;
            if (Math.hypot(px - from.x, pz - from.z) > lookahead && i > pathPosition + 1) {
                continue;
            }
            if (!chordNearPath(from.x, from.z, px, pz, pathPosition, i)) {
                continue;
            }
            if (cutIsWalkable(from, px, pz, feetY, pos.y)) {
                return new Vec3(px, pos.y + 0.5, pz);
            }
        }
        return null;
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
     * starting at pathPosition, capped 20 movements ahead. Positions up to and including this
     * index are covered by the run.
     */
    private int beelineRunEndMovement() {
        int i = pathPosition;
        while (i < path.movements().size() && isBeelineable((Movement) path.movements().get(i))) {
            i++;
        }
        return i;
    }

    /**
     * While pursuit steering cuts across blocks that aren't on the path, the player's feet can
     * briefly be in a column no movement claims as a valid position. That's expected — the cut was
     * verified walkable — so don't let the position-recovery scans treat it as being lost, as long
     * as we're at path height and still near the current movement's destination. The executor's
     * distance-from-path checks remain in force.
     */
    private boolean withinBeelineCorridor(Movement movement, BetterBlockPos whereAmI) {
        if (!Baritone.settings().beeline.value || !isBeelineable(movement)) {
            return false;
        }
        BetterBlockPos dest = movement.getDest();
        if (Math.abs(whereAmI.y - dest.y) > 1) {
            return false;
        }
        return Math.hypot(ctx.player().position().x - (dest.x + 0.5), ctx.player().position().z - (dest.z + 0.5)) < 3;
    }

    /**
     * When pursuit steering cuts corners, the player can enter the blocks of movements further
     * along the path without ever standing exactly on the intermediate destinations. Jump the path
     * position forward to the latest movement of the beelineable run whose valid positions contain
     * the player, so skipped movements don't stall waiting for a block we'll never stand on.
     */
    private void advanceThroughBeeline() {
        if (!Baritone.settings().beeline.value) {
            return;
        }
        BetterBlockPos whereAmI = ctx.playerFeet();
        int runEnd = beelineRunEndMovement();
        for (int i = runEnd - 1; i > pathPosition; i--) {
            if (((Movement) path.movements().get(i)).getValidPositions().contains(whereAmI)) {
                pathPosition = i;
                onChangeInPathPosition();
                break;
            }
        }
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
        double lookahead = Math.max(1, Baritone.settings().beelineRadius.value);
        List<Vec3> points = new ArrayList<>();
        Vec3 cur = ctx.player().position();
        points.add(new Vec3(cur.x, curY + 0.5, cur.z));
        int idx = pathPosition;
        while (idx < runEnd) {
            int advanced = idx + 1;
            for (int i = runEnd; i > idx; i--) {
                BetterBlockPos pos = positionsAt(i);
                if (Math.abs(pos.y - curY) > 1) {
                    continue;
                }
                double px = pos.x + 0.5;
                double pz = pos.z + 0.5;
                if (Math.hypot(px - cur.x, pz - cur.z) > lookahead && i > idx + 1) {
                    continue;
                }
                if (!chordNearPath(cur.x, cur.z, px, pz, idx, i)) {
                    continue;
                }
                if (cutIsWalkable(cur, px, pz, curY, pos.y)) {
                    advanced = i;
                    break;
                }
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
        return movement.toBreakCached != null && movement.toBreakCached.isEmpty()
                && movement.toPlaceCached != null && movement.toPlaceCached.isEmpty()
                && movement.toWalkIntoCached != null && movement.toWalkIntoCached.isEmpty();
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
        return MovementHelper.canWalkThrough(ctx, feet)
                && MovementHelper.canWalkThrough(ctx, feet.above())
                && (!jumpHeadroom || MovementHelper.canWalkThrough(ctx, feet.above(2)))
                && !MovementHelper.avoidWalkingInto(BlockStateInterface.get(ctx, feet))
                && !MovementHelper.avoidWalkingInto(BlockStateInterface.get(ctx, feet.above()))
                && MovementHelper.canWalkOn(ctx, feet.below());
    }

    private void onChangeInPathPosition() {
        clearKeys();
        ticksOnCurrent = 0;
    }

    private void clearKeys() {
        // i'm just sick and tired of this snippet being everywhere lol
        behavior.baritone.getInputOverrideHandler().clearAllKeys();
    }

    private void cancel() {
        clearKeys();
        behavior.baritone.getInputOverrideHandler().getBlockBreakHelper().stopBreakingBlock();
        pathPosition = path.length() + 3;
        failed = true;
    }

    @Override
    public int getPosition() {
        return pathPosition;
    }

    public PathExecutor trySplice(PathExecutor next) {
        if (next == null) {
            return cutIfTooLong();
        }
        return SplicedPath.trySplice(path, next.path, false).map(path -> {
            if (!path.getDest().equals(next.getPath().getDest())) {
                throw new IllegalStateException(String.format(
                        "Path has end %s instead of %s after splicing",
                        path.getDest(), next.getPath().getDest()));
            }
            PathExecutor ret = new PathExecutor(behavior, path);
            ret.pathPosition = pathPosition;
            ret.currentMovementOriginalCostEstimate = currentMovementOriginalCostEstimate;
            ret.costEstimateIndex = costEstimateIndex;
            ret.ticksOnCurrent = ticksOnCurrent;
            return ret;
        }).orElseGet(this::cutIfTooLong); // dont actually call cutIfTooLong every tick if we won't actually use it, use a method reference
    }

    private PathExecutor cutIfTooLong() {
        if (pathPosition > Baritone.settings().maxPathHistoryLength.value) {
            int cutoffAmt = Baritone.settings().pathHistoryCutoffAmount.value;
            CutoffPath newPath = new CutoffPath(path, cutoffAmt, path.length() - 1);
            if (!newPath.getDest().equals(path.getDest())) {
                throw new IllegalStateException(String.format(
                        "Path has end %s instead of %s after trimming its start",
                        newPath.getDest(), path.getDest()));
            }
            logDebug("Discarding earliest segment movements, length cut from " + path.length() + " to " + newPath.length());
            PathExecutor ret = new PathExecutor(behavior, newPath);
            ret.pathPosition = pathPosition - cutoffAmt;
            ret.currentMovementOriginalCostEstimate = currentMovementOriginalCostEstimate;
            if (costEstimateIndex != null) {
                ret.costEstimateIndex = costEstimateIndex - cutoffAmt;
            }
            ret.ticksOnCurrent = ticksOnCurrent;
            return ret;
        }
        return this;
    }

    @Override
    public IPath getPath() {
        return path;
    }

    public boolean failed() {
        return failed;
    }

    public boolean finished() {
        return pathPosition >= path.length();
    }

    public Set<BlockPos> toBreak() {
        return Collections.unmodifiableSet(toBreak);
    }

    public Set<BlockPos> toPlace() {
        return Collections.unmodifiableSet(toPlace);
    }

    public Set<BlockPos> toWalkInto() {
        return Collections.unmodifiableSet(toWalkInto);
    }

    public boolean isSprinting() {
        return sprintNextTick;
    }
}
