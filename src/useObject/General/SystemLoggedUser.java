package useObject.General;

import useObject.utenze.Elettore;
import useObject.utenze.Impiegato;
import useObject.utenze.Utente;

public class SystemLoggedUser {
	
	
	private static SystemLoggedUser instance;
	
	private SystemLoggedUser() {}
	
	public static SystemLoggedUser getInstance() {
		if (instance==null)
			instance = new SystemLoggedUser();
		return instance;
	}
	

	private Utente utenteLoggato;
	
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

	public Utente getUtenteLoggato() {
		return utenteLoggato;
	}
	

}
