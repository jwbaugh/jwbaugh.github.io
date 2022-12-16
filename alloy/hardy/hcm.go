
// hcm.go -- the Hardy Cross method in Go using parallel goroutines and
//           message passing, solves example 16.5.1 on p. 534 in West

package main

import "fmt"

var ab chan float64 = make(chan float64)     // channel from A to B
var ba chan float64 = make(chan float64)     // channel from B to A
var bc chan float64 = make(chan float64)     // channel from B to C
var cb chan float64 = make(chan float64)     // channel from C to B
	
func main() {
	fmt.Printf("main\n")

	go A(-172.8)			     // start joint processes and
	go B(115.2, -416.7)		     //	  let them run in parallel
	go C(416.7)

	var input string		     // let program run until all the
	fmt.Scanln(&input)		     //	  goroutines become idle, user
	fmt.Println("done")		     //	  exits with carriage return
}

func A(x float64) {			     // joint A and its moment x
	fmt.Printf("A %f\n", x)
	b := <- ba			     // recv carryover from B
	A(x + b)
}

func B(x, y float64) {			     // joint B and its moments x, y
	fmt.Printf("B %f %f\n", x, y)
	z := -(x + y)/2			     // amount distributed to x, y
	select {
	case a := <- ab:		     // recv carryover from A
		B(x + a, y)
	case c := <- cb:		     // recv carryover from B
		B(x, y + c)
	case guard(z != 0, ba) <- z/2:	     // send carryover to A then B
		bc <- z/2
		B(x + z, y + z)
	case guard(z != 0, bc) <- z/2:	     // send carryover to B then A
		ba <- z/2
		B(x + z, y + z)
	}
}

func C(x float64) {			     // joint C and its moment x
	fmt.Printf("C %f\n", x)
	select {
	case b := <- bc:		     // recv carryover from B
		C(x + b)
	case guard(x != 0, cb) <- - x/2:     // send carryover to B
		C(0)
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

/*

$ ./mdm 
main
A -172.800000
B 115.200000 -416.700000
A -97.425000
C 416.700000
C 492.075000
B 265.950000 -265.950000
B 265.950000 -511.987500
A -35.915625
C 0.000000
C 61.509375
B 388.968750 -388.968750
B 388.968750 -419.723437
A -28.226953
C 0.000000
C 7.688672
B 404.346094 -404.346094
B 404.346094 -408.190430
A -27.265869
C 0.000000
C 0.961084
B 406.268262 -406.268262
B 406.268262 -406.748804
C 0.000000
A -27.145734
B 406.508533 -406.508533
C 0.120135
C 0.000000
B 406.508533 -406.568600
B 406.538567 -406.538567
C 0.015017
C 0.000000
B 406.538567 -406.546075
A -27.130717
A -27.128840
C 0.001877
B 406.542321 -406.542321
B 406.542321 -406.543259
A -27.128605
C 0.000000
C 0.000235
B 406.542790 -406.542790
B 406.542790 -406.542907
A -27.128576
C 0.000000
C 0.000029
B 406.542849 -406.542849
B 406.542849 -406.542863
A -27.128572
C 0.000000
C 0.000004
B 406.542856 -406.542856
B 406.542856 -406.542858
A -27.128571
C 0.000000
C 0.000000
B 406.542857 -406.542857
B 406.542857 -406.542857
A -27.128571
C 0.000000
C 0.000000
B 406.542857 -406.542857
B 406.542857 -406.542857
A -27.128571
C 0.000000
C 0.000000
B 406.542857 -406.542857
B 406.542857 -406.542857
A -27.128571
C 0.000000
C 0.000000
B 406.542857 -406.542857
B 406.542857 -406.542857
A -27.128571
C 0.000000
C 0.000000
B 406.542857 -406.542857
B 406.542857 -406.542857
A -27.128571
C 0.000000
C 0.000000
B 406.542857 -406.542857
B 406.542857 -406.542857
A -27.128571
C 0.000000
C 0.000000
B 406.542857 -406.542857
B 406.542857 -406.542857
A -27.128571
C 0.000000
C 0.000000
B 406.542857 -406.542857
C 0.000000
B 406.542857 -406.542857
B 406.542857 -406.542857
C 0.000000
A -27.128571
B 406.542857 -406.542857
C 0.000000

*/
