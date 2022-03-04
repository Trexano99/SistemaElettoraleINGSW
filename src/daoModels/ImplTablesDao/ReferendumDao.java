package daoModels.ImplTablesDao;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import auditing.LogElement;
import auditing.LogHistory;
import daoModels.DBConnector;
import daoModels.NewReferendum;
import daoModels.ReferendumUpdater;
import daoModels.DbTablesRapresentation.Referendum_TB;
import daoModels.InterfaceTablesDao.IReferendumDao;
import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione.TipologiaElezione;

public class ReferendumDao implements IReferendumDao {


	@Override
	public boolean addNewReferendum(NewReferendum referendum) {
		final String query = "INSERT INTO `sistemaelettoraleingsw`.`referendum` (`nomeBreve`, `quesito`, `withQuorum`, `isClosed`, `isFinished`, `tipoElezione_fk`) VALUES (?, ?, ?, ?, ?, ?);";
		Connection dbConn = DBConnector.getDbConnection();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, referendum.getNomeBreve());
			preparedStmt.setString(2, referendum.getQuesito());
			preparedStmt.setBoolean(3, referendum.getWithQuorum());
			preparedStmt.setBoolean(3, referendum.getIsClosed());
			preparedStmt.setBoolean(4, referendum.getIsFinished());
			preparedStmt.setInt(5, Arrays.asList(TipologiaElezione.values()).indexOf(TipologiaElezione.Referendum));
			
			preparedStmt.executeQuery();
			
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public boolean removeReferendum(Referendum referendum) {
		final String query = "DELETE FROM `sistemaelettoraleingsw`.`referendum` r WHERE r.id = ?;";
		Connection dbConn = DBConnector.getDbConnection();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setInt(1, referendum.getId());
			
			preparedStmt.executeQuery();
			
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public boolean updateReferendum(ReferendumUpdater referendum) {
			
		final String query = "UPDATE `sistemaelettoraleingsw`.`referendum` SET `nomeBreve` = ?, `quesito` = ?, `withQuorum` = ?, `isClosed` = ?, `isFinished` = ? WHERE `id` = ?;";
		Connection dbConn = DBConnector.getDbConnection();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, referendum.getNome());
			preparedStmt.setString(1, referendum.getQuesito());
			preparedStmt.setBoolean(2, referendum.getWithQuorum());
			preparedStmt.setBoolean(3, referendum.isClosed());
			preparedStmt.setBoolean(4, referendum.isFinished());
			preparedStmt.setInt(5, referendum.getId());
			
			preparedStmt.executeQuery();
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}

		
		return false;
	}

	@Override
	public List<Referendum_TB> getAllReferendums() {
		final String query = "SELECT * FROM `sistemaelettoraleingsw`.`referendum`;";
		Connection dbConn = DBConnector.getDbConnection();
		
		List<Referendum_TB> tuttiReferendum = new ArrayList<Referendum_TB>();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
	
			ResultSet reSet = preparedStmt.executeQuery();
			
			while(reSet.next()) {
				tuttiReferendum.add(new Referendum_TB(
						reSet.getInt(1),
						reSet.getString(2),
						reSet.getString(3),
						reSet.getBoolean(4),
						reSet.getBoolean(5),
						reSet.getBoolean(6),
						TipologiaElezione.values()[reSet.getInt(7)]));
			}
			
			return tuttiReferendum;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}

}
