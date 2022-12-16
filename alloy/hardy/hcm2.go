
// hcm2.go -- runs until convergence
//         -- uses termination detection from EWD 840
//         -- sends a signal to all processes telling them to print their
//            moments and terminate
//         -- uses a WaitGroup to signal main when all goroutines complete

// EWD 840: Derivation of a termination detection algorithm for
//          distributed computations
//          Information Processing Letters 16: 217-219, 1983.
// https://www.cs.utexas.edu/users/EWD/ewd08xx/EWD840.PDF

package main

import "fmt"
import "sync"

var ab chan float64 = make(chan float64)     // channel from A to B
var ba chan float64 = make(chan float64)     // channel from B to A
var bc chan float64 = make(chan float64)     // channel from B to C
var cb chan float64 = make(chan float64)     // channel from C to B
	
type State int

const (	WHITE State = iota
	BLACK
	OTHER )

var anext chan State = make(chan State)      // anext = c
var bnext chan State = make(chan State)      // bnext = a
var cnext chan State = make(chan State)      // cnext = b
    
var acounter int = 0	        // number of times A, B, and C are called
var bcounter int = 0
var ccounter int = 0
var pc int = 0		        // number of times a probe is performed

var wg sync.WaitGroup		// wait for goroutines to finish

func main() {
	fmt.Printf("main\n")

	wg.Add(3)

	go A(-172.8, WHITE, OTHER)
	go B(115.2, -416.7, WHITE, WHITE)    // let B initiate probe
	go C(416.7, WHITE, OTHER)

	wg.Wait()
}

func A(x float64, s, t State) {	             // joint A and its moment x
	acounter++
	select {
	case b := <- ba:		     // recv carryover from B
		A(x + b, s, t)
	case u := <- bnext:                  // recv token, check termination
		if u == OTHER {
			fmt.Printf("A(%f) ... %d calls\n", x, acounter)
			anext <- OTHER
			defer wg.Done()
		} else {
			A(x, s, u)
		}
	case sguard(t != OTHER, anext) <- color(s, t):
		A(x, WHITE, OTHER)
	}
}

func B(x, y float64, s, t State) {	     // joint B and its moments x, y
	bcounter++
	z := -(x + y)/2	                     // amount distributed to x, y
	select {
	case a := <- ab:		     // recv carryover from A
		B(x + a, y, s, t)
	case c := <- cb:		     // recv carryover from B
		B(x, y + c, s, t)
	case u := <- cnext:	             // recv token, check termination
		pc++
		if u == WHITE {
			fmt.Printf("Number of probes performed: %d\n", pc)
			fmt.Printf("B(%f, %f) ... %d calls\n", x, y, bcounter)
			bnext <- OTHER
			defer wg.Done()
		} else {
			B(x, y, s, u)
		}
	case guard(z != 0, ba) <- z/2:	     // send carryover to A then B
		bc <- z/2
		B(x + z, y + z, BLACK, t)
	case sguard(z == 0 && t != OTHER, bnext) <- WHITE:  // converged
		B(x, y, WHITE, OTHER)
	}
}

func C(x float64, s, t State) {		     // joint C and its moment x
	ccounter++
	select {
	case b := <- bc:		     // recv carryover from B
		C(x + b, s, t)
	case u := <- anext:
		if u == OTHER {
			fmt.Printf("C(%f) ... %d calls\n", x, ccounter)
			// cnext <- OTHER (no need since a has been terminated)
			defer wg.Done()
		} else {
			C(x, s, u)
		}
	case guard(x != 0, cb) <- - x/2:     // send carryover to B
		C(0, BLACK, t)
	case sguard(x == 0 && t != OTHER, cnext) <- color(s, t): // converged
		C(x, WHITE, OTHER)
	}
}

func color(s State, t State) State {
	if s == WHITE { 
		return t 
	} else { // if s == BLACK
		return BLACK
	}
}

func str(s State) string {
	if s == WHITE { 
		return "WHITE"
	} else if s == BLACK {
		return "BLACK"
	} else {
		return "--"
	}
}

// a guard allows us to use a select in Go in the style of CSP, e.g.,
//
//   B(b) = ab -> B(False)
//	 [] cb -> B(False)
//	 [] not b & ba -> bc -> B(True)
//	 [] not b & ba -> bc -> B(True)
//
// where & allows a process in an external choice to be guarded, e.g.,
// if B and C are Boolean expressions and P and Q are processes we might
// have: B & P [] C & Q
//
func guard(b bool, c chan float64) chan float64 {
	if b { return c } else { return nil }
}

func sguard(b bool, c chan State) chan State {
	if b { return c } else { return nil }
}

/*

$ ./mdm
main
Number of probes performed: 6
B(406.542857, -406.542857) ... 49 calls
A(-27.128571) ... 31 calls
C(0.000000) ... 50 calls

*/
