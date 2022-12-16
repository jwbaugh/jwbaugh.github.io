// Member.java

import java.text.DecimalFormat;
import java.util.Vector;
import java.util.Enumeration;

import java.rmi.*;
import java.rmi.server.UnicastRemoteObject;

import java.io.*;

public class Member implements Serializable {
  final public String name;
  final public End e1, e2;

  final DecimalFormat df = new DecimalFormat("###,###.00");

  private Member(String s, End e1, End e2) {
    name = s;
    this.e1 = e1;
    this.e2 = e2;
  }

  public String toString() {
    return df.format(e1.getMoment()) + "\t";
  }

  public static void make(End e1, End e2) {
    try {

      String n1 = e1.joint.getName();
      String n2 = e2.joint.getName();
      e1.joint.addMember(new Member(n1 + n2, e1, e2));
      e2.joint.addMember(new Member(n2 + n1, e2, e1));

    } catch (Exception e) {
      System.out.println("Member (make): " + e.getMessage());
      e.printStackTrace();
    }
  }

  public void distribute(String s, double value) {
    double my_share = e1.distribution_factor * value;
    e1.decrMoment(my_share);
    e2.decrMoment(e1.carry_over * my_share);
    synchronized (e2.joint) {
      e2.joint.notify();
    }
  }
}
