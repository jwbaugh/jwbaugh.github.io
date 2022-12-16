import java.rmi.*;
import java.rmi.server.UnicastRemoteObject;

public class RemoteConstructorImpl extends UnicastRemoteObject
                                   implements RemoteConstructor {

  public RemoteConstructorImpl() throws RemoteException {
    super();
  }

  public Joint makeJoint(String name) throws RemoteException {
    return new JointImpl(name);
  }

  public End makeEnd(Joint j, double d, double m) throws RemoteException {
    return new EndImpl(j, d, m);
  }

  public End makeEnd(Joint j, double d, double m, double c)
       throws RemoteException {
    return new EndImpl(j, d, m, c);
  }

  public static void main(String args[]) {

    // Create and install a security manager
    System.setSecurityManager(new RMISecurityManager());

    try {
      RemoteConstructorImpl jfi = new RemoteConstructorImpl();
      System.out.println("RemoteConstructor instantiated.");
      Naming.rebind("RemoteConstructor", jfi);
      System.out.println("RemoteConstructor bound in registry");
    } catch (Exception e) {
      System.out.println("RemoteConstructor error: " + e.getMessage());
      e.printStackTrace();
    }
  }
}
