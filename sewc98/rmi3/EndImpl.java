
import java.rmi.*;
import java.rmi.server.UnicastRemoteObject;

class EndImpl extends UnicastRemoteObject implements End {
  final public Joint joint;
  final public double distribution_factor;
  final public double carry_over;
  private double moment;

  public EndImpl(Joint j, double d, double m, double c) throws RemoteException {
    System.out.println("End added to " + j.getName());
    joint = j;
    distribution_factor = d;
    moment = m;
    carry_over = c;
  }

  public EndImpl(Joint j, double d, double m) throws RemoteException {
    //    this(j, d, m, 0.5);
    System.out.println("End added to " + j.getName());
    joint = j;
    distribution_factor = d;
    moment = m;
    carry_over = 0.5;
  }

  public Joint getJoint() {
    return joint;
  }

  public double getDistributionFactor() throws RemoteException {
    return distribution_factor;
  }

  public double getCarryOver() throws RemoteException {
    return carry_over;
  }

  public void decrMoment(double dm) throws RemoteException {
    moment -= dm;
  }

  public double getMoment() throws RemoteException {
    return moment;
  }
}
