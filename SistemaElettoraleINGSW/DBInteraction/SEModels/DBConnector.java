package SEModels;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;

public class DBConnector {
	
	private final static String url = "jdbc:mysql://localhost/sistemaelettoraleingsw";
	private final static String username = "_";
	private final static String password = "_!";
	
	private static Connection dbConnection;
	
	/**
	 * Permette di ottenere la connessione aperta col Database.
	 * 
	 * @throws IllegalStateException nel caso la connessione non sia stata aperta. 
	 * Per aprirla vedi {@link #openConnection()}.
	 * 
	 * @return Connessione al DB
	 */
	public static Connection getDbConnection() {
		try {
			if(dbConnection == null || dbConnection.isClosed())
				throw new SQLException();
		} catch (SQLException e) {
			throw new IllegalStateException("Server seems not to be started");
		}
		return dbConnection;
	}
	
	public static void openConnection() throws SQLException {
		dbConnection = DriverManager.getConnection(url, username, password);
	}

}
