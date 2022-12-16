import java.rmi.*;


public interface End extends Remote {
  void decrMoment(double dm) throws RemoteException;
  public Joint getJoint() throws RemoteException;
  public double getDistributionFactor() throws RemoteException;
  public double getCarryOver() throws RemoteException;
  double getMoment() throws RemoteException;
}
