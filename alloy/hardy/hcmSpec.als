module hcmSpec

/*
 * Specification of the Hardy Cross method of moment distribution
 *
 * For a detailed description, see:
 *
 *   Models of Scientific Software: A State-Based Approach, submitted
 *     John Baugh, Tristan Dyer, and Alper Altuntas
 *
 * Date: January 29, 2019
 * Alloy Analyzer 5.0.0
 *
 */

-- Let joints be fixed or not, and balanced or not, include a single
-- kind of pending operation (carryover, to model data movement), and
-- assume that release and distribute are combined into an atomic
-- operation.  Then, a carryover operation, when processed, makes an
-- adjacent joint unbalanced.

open util/graph [Joint]

sig Joint { neighbors: some Joint }

-- minimal topological requirements for representing a building
--   structure (since some cannot be realized in practice, this is an
--   over-approximation)
fact topology {
   noSelfLoops[neighbors] and undirected[neighbors]
      and stronglyConnected[neighbors]
}

sig Fixed in Joint {}            -- some joints may be fixed

sig State {
   balanced: set Joint,          -- joints that are balanced
   pending: Joint -> Joint       -- a pending carry over
}

-- can carry over moments to neighbors only
fact eligible { all s: State | s.pending in neighbors }

-- start with no moments to carry over
pred init [s: State] { no s.pending }

-- release a joint, carry over a moment, or stutter
pred step [s, s': State] {
   (some u: Joint | u not in Fixed and release[u, s, s'])
      or (some u, v: Joint | carryover[u, v, s, s'])
         or stutter[s, s']       -- leave state unchanged
}

-- release and balance a joint u, set up carry overs
pred release [u: Joint, s, s': State] {
   u not in s.balanced and no s.pending[u]
   s'.balanced = s.balanced + u
   s'.pending = s.pending + u <: neighbors
}

-- carry a moment from u over to v, making v unbalanced
pred carryover [u, v: Joint, s, s': State] {
   u->v in s.pending
   s'.balanced = s.balanced - v
   s'.pending = s.pending - u->v
}

-- leave state unchanged
pred stutter [s, s': State] {
   s'.balanced = s.balanced and s'.pending = s.pending
}

-- fixed joints do not carry over moments to other joints
pred inv [s: State] {
   no u, v: Joint | u->v in s.pending and u in Fixed
}

-- show that inv is an inductive invariant
assert check_inv {
   all s, s': State {
      init[s] => inv[s]
      inv[s] and step[s, s'] => inv[s']
   }
}

check check_inv for 10
