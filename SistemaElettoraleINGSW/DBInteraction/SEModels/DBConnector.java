package SEModels;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;

public class DBConnector {
	
	private final static String url = "jdbc:mysql://localhost/sistemaelettoraleingsw";
	private final static String username = "root";
	private final static String password = "M1SqL1ngP455!";
	
	private static Connection dbConnection;
	
	public static Connection getDbConnection() {
		try {
			if(dbConnection == null || dbConnection.isClosed())
				throw new SQLException();
		} catch (SQLException e) {
			throw new IllegalStateException("Server seems not to be started");
		}
		return dbConnection;
	}
	
	public static void logIn() throws SQLException {
		dbConnection = DriverManager.getConnection(url, username, password);
	}

}
