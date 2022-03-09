package daoModels.ImplTablesDao;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

import auditing.LogElement;
import auditing.LogHistory;
import dBUtility.DBConnector;
import daoModels.DbTablesRapresentation.GenericUser_TB;
import daoModels.InterfaceTablesDao.IGenericUserDao;

/**
 * 
 * Questa classe implementa l'interfaccia {@link IGenericUserDao}
 * secondo una implementazione che mira la comunicazione con il DB
 * MYSQL utilizzando le procedure che mette a disposizione.
 * <p>
 * Rappresenta l'implementazione dell'interfaccia astratta seguendo
 * il modello DAO richiesto.
 * 
 * @author Massimiliano Visconti
 *
 */

public class GenericUserDao implements IGenericUserDao {

	/**
	 * Permette di eseguire il login da elettore. 
	 * La password può essere passata in chiaro poichè l'hashing della
	 * stessa viene fatto lato mysql dalla storedProcedure loginElettore.
	 * 
	 * @param utente 	Le credenziali utente del quale si vuole fare il login
	 * @return				{@code true} se il login e avvenuto con successo, 
	 * {@code false} altrimenti
	 */
	public String loginElettore(GenericUser_TB utente) {
		LogHistory.getInstance().addLog(new LogElement(this, " loginElettore", "Login Elettore verso il DB"));
		return baseLogin("SELECT sistemaelettoraleingsw.loginElettore(?, ?);",utente.getUsername(), utente.getPassword());
	}
	
	/**
	 * Permette di eseguire il login da Impiegato.
	 * La password può essere passata in chiaro poichè l'hashing della
	 * stessa viene fatto lato mysql dalla storedProcedure loginImpiegato.
	 * 
	 * @param utente 	Le credenziali utente del quale si vuole fare il login
	 * @return				{@code true} se il login e avvenuto con successo, 
	 * {@code false} altrimenti
	 * 
	 */
	public String loginImpiegato(GenericUser_TB utente) {
		LogHistory.getInstance().addLog(new LogElement(this, " loginElettore", "Login Impiegato verso il DB"));
		return baseLogin("SELECT sistemaelettoraleingsw.loginImpiegato(?, ?);",utente.getUsername(), utente.getPassword());
	}
	
	private static String baseLogin(String query ,String username, String password ) {
		Connection dbConn = DBConnector.getDbConnection();
		
		try {
		
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, username);
			preparedStmt.setString(2, password);
			
			ResultSet reSet = preparedStmt.executeQuery();
			
			reSet.next();
			
			return reSet.getString(1);
			
		} catch (SQLException e) {
			
			e.printStackTrace();
			
		}
		
		return null;
	
	}

}
