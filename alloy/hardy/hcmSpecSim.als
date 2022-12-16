module hcmSpecSim

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

open hcmSpec
open util/ordering [State] as so

pred show {
   init[so/first]
   all s: State - so/last | step[s, s.so/next]
}

run show for 5

pred show3 {
   #Joint = 3 and #neighbors = 4
   show
}

-- simulate a 3-joint structure for up to 40 steps
run show3 for 40 but exactly 3 Joint
