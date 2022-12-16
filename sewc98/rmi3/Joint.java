import java.rmi.*;

public interface Joint extends Remote {
  String getName() throws RemoteException;
  void addMember(Member m) throws RemoteException;
  boolean anyNonzeroDFs() throws RemoteException;
  double unbalancedMoment() throws RemoteException;
  void unclamp(double moment) throws RemoteException;
  void run() throws RemoteException;
  void print() throws RemoteException;
}
