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
import daoModels.DbTablesRapresentation.Referendum_TB;
import daoModels.InterfaceTablesDao.ICandidatoDao;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;
import useObject.voteElements.Votazione.TipologiaElezione;

public class CandidatoDao implements ICandidatoDao {

	@Override
	public List<Candidato_TB> getAllCandidati() {
		LogHistory.getInstance().addLog(new LogElement(this, "getAllCandidati", "Richiesta DB tutti candidati"));
		final String query = "SELECT * FROM sistemaelettoraleingsw.candidato;";
		Connection dbConn = DBConnector.getDbConnection();
		
		List<Candidato_TB> tuttiCandidati = new ArrayList<Candidato_TB>();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
	
			ResultSet reSet = preparedStmt.executeQuery();
			
			while(reSet.next()) {
				tuttiCandidati.add(new Candidato_TB(
						reSet.getInt(1),
						reSet.getString(2),
						reSet.getString(3),
						reSet.getDate(4),
						reSet.getInt(5)));
			}
			
			return tuttiCandidati;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}

	@Override
	public List<Candidato_TB> getCandidatiPartito(Partito partito) {
		LogHistory.getInstance().addLog(new LogElement(this, "getCandidatiPartito", "Richiesta DB candidati partito"));
		final String query = "SELECT * FROM sistemaelettoraleingsw.candidato WHERE partitoAppartenenza_fk = ?;";
		Connection dbConn = DBConnector.getDbConnection();
		
		List<Candidato_TB> tuttiCandidati = new ArrayList<Candidato_TB>();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			
			preparedStmt.setInt(1, partito.getId());
	
			ResultSet reSet = preparedStmt.executeQuery();
		
			while(reSet.next()) {
				tuttiCandidati.add(new Candidato_TB(
						reSet.getInt(1),
						reSet.getString(2),
						reSet.getString(3),
						reSet.getDate(4),
						reSet.getInt(5)));
			}
			
			return tuttiCandidati;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}

	@Override
	public List<Candidato_TB> getCandidatiElezione(Elezione elezione) {
		LogHistory.getInstance().addLog(new LogElement(this, "getCandidatiElezione", "Richiesta DB candidati elezione"));
		final String query = "SELECT c.* FROM sistemaelettoraleingsw.candidato c JOIN candidatielezione ce ON ce.candidato_fk = c.id WHERE ce.elezione_fk = ?;";
		Connection dbConn = DBConnector.getDbConnection();
		
		List<Candidato_TB> tuttiCandidati = new ArrayList<Candidato_TB>();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			
			preparedStmt.setInt(1, elezione.getId());
	
			ResultSet reSet = preparedStmt.executeQuery();
		
			while(reSet.next()) {
				tuttiCandidati.add(new Candidato_TB(
						reSet.getInt(1),
						reSet.getString(2),
						reSet.getString(3),
						reSet.getDate(4),
						reSet.getInt(5)));
			}
			
			return tuttiCandidati;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}

	@Override
	public List<Candidato_TB> getAllCandidatiVotatiVoto(int idVoto) {
		LogHistory.getInstance().addLog(new LogElement(this, "getAllCandidatiVotatiVoto", "Richiesta DB candidati votati nel voto"));
		final String query = "SELECT c.* FROM sistemaelettoraleingsw.candidativotati cv JOIN candidato c ON cv.candidato_fk = c.id WHERE cv.votoElezione_fk = ?;";
Connection dbConn = DBConnector.getDbConnection();
		
		List<Candidato_TB> tuttiCandidati = new ArrayList<Candidato_TB>();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			
			preparedStmt.setInt(1, idVoto);
	
			ResultSet reSet = preparedStmt.executeQuery();
		
			while(reSet.next()) {
				tuttiCandidati.add(new Candidato_TB(
						reSet.getInt(1),
						reSet.getString(2),
						reSet.getString(3),
						reSet.getDate(4),
						reSet.getInt(5)));
			}
			
			return tuttiCandidati;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}

}
