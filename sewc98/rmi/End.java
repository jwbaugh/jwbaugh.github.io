// End.java

import java.text.DecimalFormat;
import java.util.Vector;
import java.util.Enumeration;

import java.rmi.*;
import java.rmi.server.UnicastRemoteObject;

import java.io.*;

public class End implements Serializable {
  final public Joint joint;
  final public double distribution_factor;
  final public double carry_over;
  private double moment;

  public End(Joint j, double d, double m, double c) {
    joint = j;
    distribution_factor = d;
    moment = m;
    carry_over = c;
  }

  public End(Joint j, double d, double m) {
    //    this(j, d, m, 0.5);
    joint = j;
    distribution_factor = d;
    moment = m;
    carry_over = 0.5;
  }

  synchronized public void decrMoment(double dm) {
    moment -= dm;
  }

  public double getMoment() {
    return moment;
  }
}
