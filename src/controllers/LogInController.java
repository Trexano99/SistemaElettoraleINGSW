package controllers;


import com.mysql.cj.exceptions.FeatureNotAvailableException;

import javaFX.GraphicControllers.LogInViewController;
import useObject.utenze.Elettore;
import useObject.utenze.Impiegato;


/**
 * Questa classe mette a disposizione le funzionalita richiamabili durante la fase di login.
 * <p>
 * Esso rappresenta la parte Controller del paradigma MVC, ricevendo la view come parametro
 * che utilizza (in seguito alla comunicazione col DB) per restituire i risultati.
 * 
 * @author Massimiliano Visconti
 *
 */
public class LogInController {

	/**
	 * Enumeratore estendibile nel caso di nuove figure che si vuole inserire
	 * @author Massimiliano Visconti
	 *
	 */
	enum LogInType {
		  Elettore,
		  Impiegato
		}
		
	/**
	 * Permette di eseguire il login con le credenziali da Elettore nel sistema di voto.
	 * Nel caso il LogIn avesse successo verr� invocata la funzione @see LogInView#confirmLogin()
	 * altrimenti @see LogInView#denyLogin().
	 * Nel caso di errori verr� invocata la funzione @see LogInView#signalError(String, String) 
	 * con le specifiche dell'errore.
	 * 
	 * @param username 		CodiceFiscale elettore registrato
	 * @param password		Password elettore registrato
	 * @param logView		La view della login sulla quale verr� segnalato l'errore
	 */
	public static void attemptElettoreLogin(String username, String password, LogInViewController logView) {
		try {		
			attemptGenericLogin (username, password, logView ,LogInType.Elettore);
		}catch (IllegalArgumentException e){
			logView.signalError("CREDENTIALS FORMAT ERROR", "Username or password cannot be blank or whiteSpaces");
		}
	}
	
	/**
	 * Permette di eseguire il login con le credenziali da Impiegato nel sistema di voto.
	 * Nel caso il LogIn avesse successo verr� invocata la funzione @see LogInView#confirmLogin()
	 * altrimenti @see LogInView#denyLogin().
	 * Nel caso di errori verr� invocata la funzione @see LogInView#signalError(String, String) 
	 * con le specifiche dell'errore.
	 * 
	 * @param username 		Username impiegato registrato
	 * @param password		Password impiegato registrato
	 * @param logView		La view della login sulla quale verr� segnalato l'errore
	 */
	public static void attemptImpiegatoLogin(String username, String password, LogInViewController logView) {
		
		try {		
			attemptGenericLogin (username, password, logView ,LogInType.Impiegato);
		}catch (IllegalArgumentException e){
			logView.signalError("CREDENTIALS FORMAT ERROR", "Username or password cannot be blank or whiteSpaces");
		}
	}
	
	private static void attemptGenericLogin(String username, String password, LogInViewController logView, LogInType type) {

		
		if(logView == null)
			throw new IllegalArgumentException("La view non puo essere nulla");
		
		try {
			Boolean loginSuccess = null;
			switch(type) {
			case Elettore:
				loginSuccess = Elettore.login(username, password);
				break; 
			case Impiegato:
				loginSuccess =  Impiegato.login(username, password);
				break;
			default:
				throw new FeatureNotAvailableException("Type not supported");	
			}
			if(loginSuccess)
				logView.confirmLogin();
			else
				logView.denyLogin();
		} catch (Exception e) {
			logView.signalError("SERVERSIDE ERROR", e.getStackTrace().toString());
		}

	}
	
	

}