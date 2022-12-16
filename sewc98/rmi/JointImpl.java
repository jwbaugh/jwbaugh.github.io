// JointImpl.java -- a joint server

import java.text.DecimalFormat;
import java.util.Vector;
import java.util.Enumeration;

import java.rmi.*;
import java.rmi.server.UnicastRemoteObject;

public class JointImpl extends UnicastRemoteObject implements Joint {
  final public String name;
  private Vector members = new Vector();

  public JointImpl(String s) throws RemoteException {
    System.out.println("JointImpl " + s);
    name = s;
  }

  public String getName() throws RemoteException {
    return name;
  }

  public void addMember(Member m) throws RemoteException {
    System.out.println(name + " added member " + m.name);
    System.out.println("  end1 moment = " + m.e1.getMoment());
    members.addElement(m);
  }

  public boolean anyNonzeroDFs () throws RemoteException {
    for (Enumeration e = members.elements(); e.hasMoreElements(); )
      if (((Member) e.nextElement()).e1.distribution_factor > 0)
	return true;
    return false;
  }

  public double unbalancedMoment() throws RemoteException {
    double moment = 0.0;
    for (Enumeration e = members.elements(); e.hasMoreElements(); )
      moment += ((Member) e.nextElement()).e1.getMoment();
    return moment;
  }

  public void unclamp(double moment) throws RemoteException {
    for (Enumeration e = members.elements(); e.hasMoreElements(); )
      ((Member) e.nextElement()).distribute(name, moment);
  }

  public void run() throws RemoteException {
    double moment;
    synchronized (this) {
      while (Math.abs(moment = unbalancedMoment()) < 0.0001) {
	try {
	  wait();
	} catch (InterruptedException e) {}
      }
    }
    unclamp(moment);
    run();
  }

  public void print() throws RemoteException {
    System.out.println("\nJoint Impl print(): " + name);
    for (Enumeration e = members.elements(); e.hasMoreElements(); ) {
      Member m = (Member) e.nextElement();
      System.out.println("  member " + m.name);
      System.out.println("  moment " + m.e1.getMoment());

      //      System.out.println(m.name + " " + m);
    }
  }

  public static void main(String args[]) {

    // Create and install a security manager
    System.setSecurityManager(new RMISecurityManager());

    try {
      JointImpl a = new JointImpl("A");
      Naming.rebind("/home/jwb/JointA", a);
      System.out.println("JointA bound in registry");

      JointImpl b = new JointImpl("B");
      Naming.rebind("/home/jwb/JointB", b);
      System.out.println("JointB bound in registry");

      JointImpl c = new JointImpl("C");
      Naming.rebind("/home/jwb/JointC", c);
      System.out.println("JointC bound in registry");

    } catch (Exception e) {
      System.out.println("JointImpl err: " + e.getMessage());
      e.printStackTrace();
    }
  }
}

