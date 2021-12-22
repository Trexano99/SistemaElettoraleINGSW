package Controllers;

import java.sql.SQLException;

import com.mysql.cj.exceptions.FeatureNotAvailableException;

import SEModels.LogInMapper;
import ViewElements.LogInView;


/**
 * Questa classe mette a disposizione le funzionalità richiamabili durante la fase di login
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
	 * Nel caso il LogIn avesse successo verrà invocata la funzione @see LogInView#confirmLogin()
	 * altrimenti @see LogInView#denyLogin().
	 * Nel caso di errori verrà invocata la funzione @see LogInView#signalError(String, String) 
	 * con le specifiche dell'errore.
	 * 
	 * @param username 		CodiceFiscale elettore registrato
	 * @param password		Password elettore registrato
	 * @param logView		La view della login sulla quale verrà segnalato l'errore
	 */
	public void attemptElettoreLogin(String username, String password, LogInView logView) {
		attemptGenericLogin (username, password, logView ,LogInType.Elettore);
	}
	
	/**
	 * Permette di eseguire il login con le credenziali da Impiegato nel sistema di voto.
	 * Nel caso il LogIn avesse successo verrà invocata la funzione @see LogInView#confirmLogin()
	 * altrimenti @see LogInView#denyLogin().
	 * Nel caso di errori verrà invocata la funzione @see LogInView#signalError(String, String) 
	 * con le specifiche dell'errore.
	 * 
	 * @param username 		Username impiegato registrato
	 * @param password		Password impiegato registrato
	 * @param logView		La view della login sulla quale verrà segnalato l'errore
	 */
	public void attemptImpiegatoLogin(String username, String password, LogInView logView) {
		attemptGenericLogin (username, password, logView ,LogInType.Impiegato);
	}
	
	private void attemptGenericLogin(String username, String password, LogInView logView, LogInType type) {
		if(logView == null)
			throw new IllegalArgumentException("La view non può essere nulla");
		if(username.isBlank())
			logView.signalError("USERNAME FORMAT ERROR", "Username cannot be blank or whiteSpaces");
		if(password.isBlank())
			logView.signalError("PASSWORD FORMAT ERROR", "Password cannot be blank or whiteSpaces");
		
		try {
			boolean result = false;
			switch(type) {
			case Elettore:
				result = LogInMapper.loginElettore(username, password);
				break; 
			case Impiegato:
				result = LogInMapper.loginImpiegato(username, password);
				break;
			default:
				throw new FeatureNotAvailableException("Type not supported");	
			}
			if(result)
				logView.confirmLogin();
			else
				logView.denyLogin();
		} catch (SQLException e) {
			logView.signalError("SERVERSIDE ERROR", e.getStackTrace().toString());
		}
		
	}
	
	

}
