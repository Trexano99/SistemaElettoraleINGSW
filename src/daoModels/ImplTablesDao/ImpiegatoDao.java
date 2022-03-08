package daoModels.ImplTablesDao;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

import auditing.LogElement;
import auditing.LogHistory;
import daoModels.DBConnector;
import daoModels.DbTablesRapresentation.Impiegato_TB;
import daoModels.InterfaceTablesDao.IImpiegatoDao;

public class ImpiegatoDao implements IImpiegatoDao {

	@Override
	public Impiegato_TB get(String impiegatoId) {
		LogHistory.getInstance().addLog(new LogElement(this, " get", "Richiesta DB dati impiegato"));
		final String query = "SELECT * FROM `sistemaelettoraleingsw`.`impiegato` i WHERE i.idimpiegato = ?";
		Connection dbConn = DBConnector.getDbConnection();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, impiegatoId);
			
			ResultSet reSet = preparedStmt.executeQuery();
			
			reSet.next();
			
			reSet.getString(2);
			
			return new Impiegato_TB(impiegatoId, reSet.getString(2), reSet.getString(3));
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}

}
