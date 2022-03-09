package dBUtility;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;

import auditing.LogElement;
import auditing.LogHistory;

/**
 * Questa classe mette a disposizione i metodi per gestire la connessione con il DB
 * e richiamare la stessa per l'utilizzo.
 * <p>
 * Questa classe è stata creata per semplificare e mantenere raggruppati gli elementi
 * di connessione al DB.
 * 
 * @author Massimiliano Visconti
 *
 */
public class DBConnector {
	
	private final static String url = "jdbc:mysql://localhost/sistemaelettoraleingsw";
	private final static String username = "root";
	private final static String password = "M1SqL1ngP455!";
	
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
			LogHistory.getInstance().addLog(new LogElement(DBConnector.class, "gettingDbConnection", "Provando ad ottenere la connessione con il DB",true));
			throw new IllegalStateException("Server seems not to be started");
		}
		return dbConnection;
	}
	
	/**
	 * Permette di aprire la connessione con il Database locale Mysql
	 * @throws SQLException Nel caso ci siano errori di comunicazione con il DB
	 */
	public static void openConnection() throws SQLException {
		LogHistory.getInstance().addLog(new LogElement(DBConnector.class, "openConnection", "Provando ad aprire la connessione con il DB"));
		dbConnection = DriverManager.getConnection(url, username, password);
		LogHistory.getInstance().addLog(new LogElement(DBConnector.class, "openConnection", "Connessione con il DB aperta con successo"));
	}

	/**
	 * Permette di chiudere la connessione al DB se � aperta
	 */
	public static void closeConnection() {
		try {
			if(dbConnection!=null && !dbConnection.isClosed())
				dbConnection.close();
			LogHistory.getInstance().addLog(new LogElement(DBConnector.class, "closeConnection", "Chiusa la connessione con il DB"));
		} catch (SQLException e) {
			e.printStackTrace();
		}
	}
}