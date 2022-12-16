import java.rmi.*;

public interface Joint extends Remote {
  public String getName() throws RemoteException;
  public void addMember(Member m) throws RemoteException;
  public boolean anyNonzeroDFs() throws RemoteException;
  public double unbalancedMoment() throws RemoteException;
  public void unclamp(double moment) throws RemoteException;
  public void run() throws RemoteException;
  public void print() throws RemoteException;
}

