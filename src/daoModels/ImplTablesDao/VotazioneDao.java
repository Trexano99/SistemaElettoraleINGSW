package daoModels.ImplTablesDao;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

import auditing.LogElement;
import auditing.LogHistory;
import daoModels.DBConnector;
import daoModels.ElezioneVote_Categorico;
import daoModels.ElezioneVote_CategoricoConPref;
import daoModels.ElezioneVote_Ordinale;
import daoModels.ReferendumVote;
import daoModels.InterfaceTablesDao.IVotazioneDao;
import useObject.General.SystemLoggedUser;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;

public class VotazioneDao implements IVotazioneDao {

	@Override
	public boolean addElezioneVote(ElezioneVote_Categorico referVote) {
		final String query = "CALL `sistemaelettoraleingsw`.`addElectionVote_categorico`(?, ?, ?, ?);";
		Connection dbConn = DBConnector.getDbConnection();
		
		if(!SystemLoggedUser.getInstance().isElettore()) {
			LogHistory.getInstance().addLog(new LogElement(this, "InstanceError", "Non ci si aspetta un impiegato al voto",true));
			throw new IllegalStateException("Impiegato cannot vote");
		}
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, SystemLoggedUser.getInstance().getUtenteLoggato().getId());
			preparedStmt.setInt(2, referVote.getElezione().getId());
			preparedStmt.setInt(3, referVote.getCandidato().getId());
			preparedStmt.setInt(4, referVote.getPartito().getId());
			
			preparedStmt.executeQuery();
			
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public boolean addElezioneVote(ElezioneVote_CategoricoConPref referVote) {
		final String query = "CALL `sistemaelettoraleingsw`.`addElectionVote_categoricoConPref`(?, ?, ?, ?);";
		Connection dbConn = DBConnector.getDbConnection();
		
		if(!SystemLoggedUser.getInstance().isElettore()) {
			LogHistory.getInstance().addLog(new LogElement(this, "InstanceError", "Non ci si aspetta un impiegato al voto",true));
			throw new IllegalStateException("Impiegato cannot vote");
		}
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, SystemLoggedUser.getInstance().getUtenteLoggato().getId());
			preparedStmt.setInt(2, referVote.getElezione().getId());
			preparedStmt.setInt(3, referVote.getPartito().getId());
			preparedStmt.setString(4, referVote.getListaCandidatiDbFormat());
			
			preparedStmt.executeQuery();
			
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public boolean addElezioneVote(ElezioneVote_Ordinale referVote) {
		final String query = "CALL `sistemaelettoraleingsw`.`addElectionVote_ordinale`(?, ?, ?, ?);";
		Connection dbConn = DBConnector.getDbConnection();
		
		if(!SystemLoggedUser.getInstance().isElettore()) {
			LogHistory.getInstance().addLog(new LogElement(this, "InstanceError", "Non ci si aspetta un impiegato al voto",true));
			throw new IllegalStateException("Impiegato cannot vote");
		}
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, SystemLoggedUser.getInstance().getUtenteLoggato().getId());
			preparedStmt.setInt(2, referVote.getElezione().getId());
			preparedStmt.setString(3, referVote.getListaPartitiDbFormat());
			preparedStmt.setString(4, referVote.getListaCandidatiDbFormat());
			
			preparedStmt.executeQuery();
			
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public boolean addReferendumVote(ReferendumVote referVote) {
		final String query = "CALL `sistemaelettoraleingsw`.`addReferendumVote`(?, ?, ?);";
		Connection dbConn = DBConnector.getDbConnection();
		
		if(!SystemLoggedUser.getInstance().isElettore()) {
			LogHistory.getInstance().addLog(new LogElement(this, "InstanceError", "Non ci si aspetta un impiegato al voto",true));
			throw new IllegalStateException("Impiegato cannot vote");
		}
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, SystemLoggedUser.getInstance().getUtenteLoggato().getId());
			preparedStmt.setInt(2, referVote.getReferendum().getId());
			preparedStmt.setBoolean(3, referVote.isVote());
			
			preparedStmt.executeQuery();
			
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public Boolean hasElettoreVotedForRef(Referendum ref) {
		final String query = "`sistemaelettoraleingsw`.`hasElettoreVotedElez`(?, ?);";
		Connection dbConn = DBConnector.getDbConnection();
		
		if(!SystemLoggedUser.getInstance().isElettore()) {
			LogHistory.getInstance().addLog(new LogElement(this, "InstanceError", "Non ci si aspetta un impiegato al voto",true));
			throw new IllegalStateException("Impiegato cannot vote");
		}
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, SystemLoggedUser.getInstance().getUtenteLoggato().getId());
			preparedStmt.setInt(2, ref.getId());
			
			ResultSet rs = preparedStmt.executeQuery();
			
			rs.next();
			
			
			return rs.getBoolean(0);
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}

	@Override
	public Boolean hasElettoreVotedForElez(Elezione ele) {
		final String query = "`sistemaelettoraleingsw`.`hasElettoreVotedElez`(?, ?);";
		Connection dbConn = DBConnector.getDbConnection();
		
		if(!SystemLoggedUser.getInstance().isElettore()) {
			LogHistory.getInstance().addLog(new LogElement(this, "InstanceError", "Non ci si aspetta un impiegato al voto",true));
			throw new IllegalStateException("Impiegato cannot vote");
		}
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, SystemLoggedUser.getInstance().getUtenteLoggato().getId());
			preparedStmt.setInt(2, ele.getId());
			
			preparedStmt.executeQuery();
			
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}


}
