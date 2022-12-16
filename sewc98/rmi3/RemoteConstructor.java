import java.rmi.*;

public interface RemoteConstructor extends Remote {
  Joint makeJoint(String name) throws RemoteException;
  End makeEnd(Joint j, double d, double m) throws RemoteException;
  End makeEnd(Joint j, double d, double m, double c) throws RemoteException;
}
