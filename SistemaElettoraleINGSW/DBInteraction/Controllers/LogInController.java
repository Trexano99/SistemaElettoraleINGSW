package Controllers;

import java.sql.SQLException;

import com.mysql.cj.exceptions.FeatureNotAvailableException;

import SEModels.LogInMapper;
import ViewElements.LogInView;

public class LogInController {

	enum LogInType {
		  Elettore,
		  Impiegato
		}
		
	//attemptElettoreLogin
	public void attemptElettoreLogin(String username, String password, LogInView logView) {
		attemptGenericLogin (username, password, logView ,LogInType.Elettore);
	}
	
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
