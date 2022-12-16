
import java.util.Vector;
import java.util.Enumeration;

import java.rmi.*;
import java.rmi.server.UnicastRemoteObject;

public class JointImpl extends UnicastRemoteObject implements Joint {
  final public String name;
  private Vector members = new Vector();

  public JointImpl(String s) throws RemoteException {
    System.out.println("Joint " + s);
    name = s;
  }

  public String getName() throws RemoteException {
    return name;
  }

  public void addMember(Member m) throws RemoteException {
    members.addElement(m);
  }

  public boolean anyNonzeroDFs () throws RemoteException {
    for (Enumeration e = members.elements(); e.hasMoreElements(); )
      if (((Member) e.nextElement()).e1.getDistributionFactor() > 0)
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
    for (Enumeration e = members.elements(); e.hasMoreElements(); ) {
      Member m = (Member) e.nextElement();
      System.out.println(m.name + " " + m.e1.getMoment());
    }
  }
}
