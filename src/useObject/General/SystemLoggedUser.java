package useObject.General;

import useObject.utenze.Elettore;
import useObject.utenze.Impiegato;
import useObject.utenze.Utente;

public class SystemLoggedUser {
	
	
	private static SystemLoggedUser instance;
	
	private SystemLoggedUser() {}
	
	/*@ requires instance == null;
	 @ assignable instance;
	 @ 
	 @ also
	 @ 
	 @ ensures \result == instance;
	 @*/
	public static SystemLoggedUser getInstance() {
		if (instance==null)
			instance = new SystemLoggedUser();
		return instance;
	}
	

	private Utente utenteLoggato;
	
	/*@ requires user != null;
	 @ assignable utenteLoggato;
	 @ ensures utenteLoggato = user;
	 @*/
	public void setUtenteLoggato (Utente user) {
		utenteLoggato = user;
	}
	
	public boolean isElettore() {
		if(utenteLoggato instanceof Elettore)
			return true;
		return false;
	}
	
	public boolean isImpiegato() {
		if(utenteLoggato instanceof Impiegato)
			return true;
		return false;
	}
	
	/*@ ensures \result == utenteLoggato;
	 @*/
	public Utente getUtenteLoggato() {
		return utenteLoggato;
	}
	

}
