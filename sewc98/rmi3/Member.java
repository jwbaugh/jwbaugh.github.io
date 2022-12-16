
import java.text.DecimalFormat;

import java.rmi.*;
import java.io.*;

public class Member implements Serializable {
  public String name;
  public End e1, e2;

  final DecimalFormat df = new DecimalFormat("###,###.00");

  private Member(String s, End e1, End e2) {
    name = s;
    this.e1 = e1;
    this.e2 = e2;
  }

  public String toString() {
    try {
      return df.format(e1.getMoment()) + "\t";
    } catch (Exception e) {}
    return "xx\t";
  }

  public static void make(End e1, End e2) throws RemoteException {
    String n1 = e1.getJoint().getName();
    String n2 = e2.getJoint().getName();
    e1.getJoint().addMember(new Member(n1 + n2, e1, e2));
    e2.getJoint().addMember(new Member(n2 + n1, e2, e1));
  }

  public void distribute(String s, double value) throws RemoteException {
    double my_share = e1.getDistributionFactor() * value;
    e1.decrMoment(my_share);
    e2.decrMoment(e1.getCarryOver() * my_share);
  }
}
