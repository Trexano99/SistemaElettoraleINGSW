package daoModels.ImplTablesDao;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.List;

import auditing.LogElement;
import auditing.LogHistory;
import daoModels.DBConnector;
import daoModels.DbTablesRapresentation.Candidato_TB;
import daoModels.DbTablesRapresentation.Partito_TB;
import daoModels.InterfaceTablesDao.IPartitoDao;
import useObject.voteElements.Elezione;

public class PartitoDao implements IPartitoDao {

	@Override
	public List<Partito_TB> getAllPartiti() {
		final String query = "SELECT * FROM sistemaelettoraleingsw.partito;";
		Connection dbConn = DBConnector.getDbConnection();
		
		List<Partito_TB> tuttiPartiti = new ArrayList<Partito_TB>();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
	
			ResultSet reSet = preparedStmt.executeQuery();
		
			while(reSet.next()) {
				tuttiPartiti.add(new Partito_TB(
						reSet.getInt(1),
						reSet.getString(2)));
			}
			
			return tuttiPartiti;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}

	@Override
	public List<Partito_TB> getAllPartitiElezione(Elezione elezione) {
		final String query = "SELECT p.* FROM sistemaelettoraleingsw.partito p JOIN partitielezione pe ON p.id = pe.partito_fk WHERE p.id = ?;";
		Connection dbConn = DBConnector.getDbConnection();
		
		List<Partito_TB> tuttiPartiti = new ArrayList<Partito_TB>();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
	
			ResultSet reSet = preparedStmt.executeQuery();
		
			while(reSet.next()) {
				tuttiPartiti.add(new Partito_TB(
						reSet.getInt(1),
						reSet.getString(2)));
			}
			
			return tuttiPartiti;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}

}
