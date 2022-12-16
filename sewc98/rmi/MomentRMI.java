// MomentRMI.java  -- moment distribution: RMI version

import java.text.DecimalFormat;
import java.util.Vector;
import java.util.Enumeration;

import java.rmi.*;

public class MomentRMI {

  public static Joint[] problem1() {

    try {
      Joint a = (Joint) Naming.lookup("/home/jwb/JointA");
      Joint b = (Joint) Naming.lookup("/home/jwb/JointB");
      Joint c = (Joint) Naming.lookup("/home/jwb/JointC");

      Joint[] j = {a, b, c};

      Member.make(new End(a, 0.0, -172.8), new End(b, 0.5, 115.2));
      Member.make(new End(b, 0.5, -416.7), new End(c, 1.0, 416.7));

      a.print();
      b.print();
      c.print();

      //      jprint(j);

      return j;

    } catch (Exception e) {
      System.out.println("MomentRMI (problem1): " + e.getMessage());
      e.printStackTrace();
    }

    return null;
  }

  public static void jprint(Joint j[]) {
    try {
      for (int i = 0; i < j.length; i++)
	j[i].print();
    } catch (RemoteException e) {
      System.out.println("MomentRMI (jprint): " + e.getMessage());
      e.printStackTrace();
    }
  }

  public static void sequential(Joint j[]) {
    double ubm;
    boolean done;

    try {

      do {
	done = true;
	for (int i = 0; i < j.length; i++)
	  if (j[i].anyNonzeroDFs()) {
	    if (Math.abs(ubm = j[i].unbalancedMoment()) >= 0.0001) {
	      done = false;
	      j[i].unclamp(ubm);
	    }
	  }
	jprint(j); System.out.println();
      } while (!done);
      
    } catch (RemoteException e) {
      System.out.println("MomentRMI (sequential): " + e.getMessage());
      e.printStackTrace();
    }

  }

  public static void main(String args[]) {

    Joint j[] = problem1();

    sequential(j);

  }
}
