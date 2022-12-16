// Moment.java  -- moment distribution: sequential and concurrent versions

import java.rmi.*;

public class Moment {

  public static Joint[] problem1(RemoteConstructor rc) throws RemoteException {

/*
Example 16.5.1 from Analysis of Structures by H.H. West, p. 534

ab -27.12
ba 406.54
bc -406.54
cb .00
*/
    Joint a = rc.makeJoint("a");
    Joint b = rc.makeJoint("b");
    Joint c = rc.makeJoint("c");

    Joint[] j = {a, b, c};

    Member.make(rc.makeEnd(a, 0.0, -172.8), rc.makeEnd(b, 0.5, 115.2));
    Member.make(rc.makeEnd(b, 0.5, -416.7), rc.makeEnd(c, 1.0, 416.7));

    return j;
  }

  public static void jprint(Joint j[]) throws RemoteException {
    for (int i = 0; i < j.length; i++)
      j[i].print();
  }

  public static void sequential(Joint j[]) throws RemoteException {
    double ubm;
    boolean done;

    do {
      done = true;
      for (int i = 0; i < j.length; i++)
	if (j[i].anyNonzeroDFs()) {
	  if (Math.abs(ubm = j[i].unbalancedMoment()) >= 0.0001) {
	    done = false;
	    j[i].unclamp(ubm);
	  }
	}
      jprint(j);
    } while (!done);
  }

  public static void main(String args[]) throws Exception {

    RemoteConstructor rc = (RemoteConstructor)
                               Naming.lookup("RemoteConstructor");

    sequential(problem1(rc));
  }
}
