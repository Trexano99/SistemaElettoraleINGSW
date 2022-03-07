package daoModels.ImplTablesDao;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

import auditing.LogElement;
import auditing.LogHistory;
import daoModels.DBConnector;
import daoModels.DbTablesRapresentation.Elettore_TB;
import daoModels.InterfaceTablesDao.IElettoreDao;

public class ElettoreDao implements IElettoreDao {
	
	@Override
	public Elettore_TB get(String elettoreId) {
		LogHistory.getInstance().addLog(new LogElement(this, " get", "Richiesta DB dati elettore"));
		final String query = "SELECT * FROM `sistemaelettoraleingsw`.`elettore` e WHERE e.CodiceFiscale = ?;";
		Connection dbConn = DBConnector.getDbConnection();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, elettoreId);
			
			ResultSet reSet = preparedStmt.executeQuery();
			
			reSet.next();
			
			return new Elettore_TB(elettoreId, reSet.getString(2), reSet.getString(3));
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}
}
