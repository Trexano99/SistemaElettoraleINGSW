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
import daoModels.ElezioneUpdater;
import daoModels.NewElezione;
import daoModels.DbTablesRapresentation.Elezione_TB;
import daoModels.InterfaceTablesDao.IElezioneDao;
import useObject.voteElements.Elezione;
import useObject.voteElements.Votazione.TipologiaElezione;

public class ElezioneDao implements IElezioneDao {

	@Override
	public boolean addNewElezione(NewElezione elezione) {
		final String query = "INSERT INTO `sistemaelettoraleingsw`.`elezione`(`nomeBreve`,`maggioranzaAssoluta`,`isClosed`,`isFinished`,`tipoElezione_fk`) VALUES (?,?,?,?,?);";
		Connection dbConn = DBConnector.getDbConnection();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, elezione.getNomeBreve());
			preparedStmt.setBoolean(2, elezione.getMaggioranzaAssoluta());
			preparedStmt.setBoolean(3, elezione.getIsClosed());
			preparedStmt.setBoolean(4, elezione.getIsFinished());
			preparedStmt.setInt(5, elezione.getTipoElezione().ordinal());
			
			preparedStmt.executeQuery();
			
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public boolean removeElezione(Elezione elezione) {
		final String query = "DELETE FROM `sistemaelettoraleingsw`.`elezione` e WHERE e.id = ?;";
		Connection dbConn = DBConnector.getDbConnection();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setInt(1, elezione.getId());
			
			preparedStmt.executeQuery();
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public boolean updateElezione(ElezioneUpdater elezione) {
		final String query = "UPDATE `sistemaelettoraleingsw`.`elezione` SET `nomeBreve`=?,`maggioranzaAssoluta`=?,`isClosed`=?,`isFinished`=?,`tipoElezione_fk`=? WHERE `id` = ?;";
		Connection dbConn = DBConnector.getDbConnection();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, elezione.getNome());
			preparedStmt.setBoolean(2, elezione.getMaggioranzaAssoluta());
			preparedStmt.setBoolean(3, elezione.isClosed());
			preparedStmt.setBoolean(4, elezione.isFinished());
			if(elezione.getTipoElezione()==TipologiaElezione.Referendum){
				LogHistory.getInstance().addLog(new LogElement(this, "UpdatingElezioneError", "Trasformazione di elezione in referendum", true));
				throw new IllegalStateException("Non si può trasformare una elezione in un referendum");
			}
			preparedStmt.setInt(5, elezione.getTipoElezione().ordinal());
			preparedStmt.setInt(6, elezione.getId());
	
			
			preparedStmt.executeQuery();
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public List<Elezione_TB> getAllElezioni() {
		final String query = "SELECT * FROM `sistemaelettoraleingsw`.`elezione`;";
		Connection dbConn = DBConnector.getDbConnection();
		
		List<Elezione_TB> tutteElezioni = new ArrayList<Elezione_TB>();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
	
			ResultSet reSet = preparedStmt.executeQuery();
			
			while(reSet.next()) {
				tutteElezioni.add(new Elezione_TB(
						reSet.getInt(1),
						reSet.getString(2),
						reSet.getBoolean(3),
						reSet.getBoolean(4),
						reSet.getBoolean(5),
						TipologiaElezione.values()[reSet.getInt(6)]));
			}
			
			return tutteElezioni;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}

}
