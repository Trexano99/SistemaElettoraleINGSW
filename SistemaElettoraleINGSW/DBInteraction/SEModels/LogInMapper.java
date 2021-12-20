package SEModels;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

public class LogInMapper {

	/*public static void addNewElettore(
	String codiceFiscale, 
	String nome,
	String cognome, 
	Date dataNascita,
	String password
	) {

	Connection dbConn = DBConnector.getDbConnection();
	String query = "CALL `sistemaelettoraleingsw`.`addElettore`(?, ?, ?, ?, ?);";
	
	try {
	
		PreparedStatement preparedStmt = dbConn.prepareStatement(query);
		preparedStmt.setString(1, codiceFiscale);
		preparedStmt.setString(2, nome);
		preparedStmt.setString(3, cognome);
		preparedStmt.setDate(4, dataNascita);
		preparedStmt.setString(5, password);
		
		preparedStmt.execute();
		
	} catch (SQLException e) {
		
		e.printStackTrace();
		
	}
	
	}*/
	
	public static boolean loginElettore(
		String username, 
		String password
		) throws SQLException {
	
	return baseLogin("SELECT sistemaelettoraleingsw.loginElettore(?, ?);",username, password);
	
	}
	
	public static boolean loginImpiegato(
		String username, 
		String password
		) throws SQLException {
	
	return baseLogin("SELECT sistemaelettoraleingsw.loginImpiegato(?, ?);",username, password);
	
	}
	
	private static boolean baseLogin(String query ,String username, String password ) {
	Connection dbConn = DBConnector.getDbConnection();
	
	try {
	
		PreparedStatement preparedStmt = dbConn.prepareStatement(query);
		preparedStmt.setString(1, username);
		preparedStmt.setString(2, password);
		
		ResultSet reSet = preparedStmt.executeQuery();
		
		reSet.next();
		
		return reSet.getBoolean(1);
		
	} catch (SQLException e) {
		
		e.printStackTrace();
		
	}
	return false;
	
	}

	
}
