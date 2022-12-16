module hcmRefSim

/*
 * A refinement with communicating processes: a process for each joint
 *   and communication between them using synchronous message passing
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

open hcmSpec
open hcmRef
open util/ordering [State_R] as ro

pred show {
  init_R[ro/first]
  all s: State_R - ro/last | step_R[s, s.ro/next]
}

run show for 12 but 3 Joint, 10 State_R, 20 State

-- for convenience, define the abstraction function as an Alloy function

fun af [r: State_R]: State - State_R {
  { s: State - State_R | s.pending = r.pending and s.balanced = r.balanced }
}

-- populate the set of states the abstraction function maps to
--   (see 5.3 Unbounded Universal quantification in Jackson 2012)

fact { all r: State_R | some af[r] }

-- simulate spec S and ref R in tandem to show how they are related

one sig A, B, C in Joint {}       -- use the example from Baugh/Liu

pred example {
   #Joint = 3
   A = Fixed
   A->B in neighbors
   B->C in neighbors
   A->C not in neighbors
   init[af[ro/first]] and init_R[ro/first]
   no af[ro/first].balanced and no ro/first.balanced
}

pred step_RS {
  example
  let r0 = ro/first, r1 = r0.ro/next, r2 = r1.ro/next, r3 = r2.ro/next,
    r4 = r3.ro/next, r5 = r4.ro/next, r6 = r5.ro/next, r7 = r6.ro/next,
    r8 = r7.ro/next {

      -- release B, send to A & C
      test[B, r0, r1] and release[B, af[r0], af[r1]]

      -- let A enter receive mode
      test[A, r1, r2] and af[r1] = af[r2]           -- spec stutter

      -- let C enter receive mode
      test[C, r2, r3] and af[r2] = af[r3]           -- spec stutter

      -- pass message from B to C
      synch[B, C, r3, r4] and carryover[B, C, af[r3], af[r4]]

      -- C returns to test
      leave_receive[C, r4, r5] and af[r4] = af[r5]  -- spec stutter

      -- release C, send to B
      test[C, r5, r6] and release[C, af[r5], af[r6]]

      -- pass message from B to A
      synch[B, A, r6, r7] and carryover[B, A, af[r6], af[r7]]

      -- B returns to test
      leave_send[B, r7, r8] and af[r7] = af[r8]     -- spec stutter
  }
}

run step_RS for 3 Joint, 3 Counter, 9 State_R, 14 State
