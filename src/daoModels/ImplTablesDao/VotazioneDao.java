package daoModels.ImplTablesDao;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.SQLType;
import java.util.ArrayList;
import java.util.List;

import auditing.LogElement;
import auditing.LogHistory;
import daoModels.DBConnector;
import daoModels.ElezioneVote;
import daoModels.ElezioneVote_Categorico;
import daoModels.ElezioneVote_CategoricoConPref;
import daoModels.ElezioneVote_Ordinale;
import daoModels.ReferendumVote;
import daoModels.DbTablesRapresentation.Candidato_TB;
import daoModels.DbTablesRapresentation.Elezione_TB;
import daoModels.DbTablesRapresentation.Partito_TB;
import daoModels.DbTablesRapresentation.VotoElezione_TB;
import daoModels.DbTablesRapresentation.VotoReferendum_TB;
import daoModels.InterfaceTablesDao.IVotazioneDao;
import useObject.General.SystemLoggedUser;
import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione.TipologiaElezione;

public class VotazioneDao implements IVotazioneDao {

	@Override
	public boolean addElezioneVote(ElezioneVote_Categorico referVote) {
		LogHistory.getInstance().addLog(new LogElement(this, " addElezioneVote", "Aggiunta voto categorico nel DB"));
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
			if(referVote.getCandidato()!=null)
				preparedStmt.setInt(3, referVote.getCandidato().getId());
			else
				preparedStmt.setNull(3,java.sql.Types.INTEGER);
			if(referVote.getPartito()!=null)
				preparedStmt.setInt(4, referVote.getPartito().getId());
			else
				preparedStmt.setNull(4,java.sql.Types.INTEGER);
			
			preparedStmt.executeQuery();
			
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public boolean addElezioneVote(ElezioneVote_CategoricoConPref referVote) {
		LogHistory.getInstance().addLog(new LogElement(this, " addElezioneVote", "Aggiunta voto categorico con Preferenza nel DB"));
		final String query = "CALL `sistemaelettoraleingsw`.`addElectionVote_categoricoConPref`(?, ?, ?, ?);";
		Connection dbConn = DBConnector.getDbConnection();
		
		if(!SystemLoggedUser.getInstance().isElettore()) {
			LogHistory.getInstance().addLog(new LogElement(this, "InstanceError", "Non ci si aspetta un impiegato al voto",true));
			throw new IllegalStateException("Impiegato cannot vote");
		}
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, SystemLoggedUser.getInstance().getUtenteLoggato().getId());
			if(referVote.getElezione()!= null)
				preparedStmt.setInt(2, referVote.getElezione().getId());
			else
				preparedStmt.setNull(2,java.sql.Types.INTEGER);
			if(referVote.getPartito()!=null)
				preparedStmt.setInt(3, referVote.getPartito().getId());
			else
				preparedStmt.setNull(3,java.sql.Types.INTEGER);
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
		LogHistory.getInstance().addLog(new LogElement(this, " addElezioneVote", "Aggiunta voto ordinale nel DB"));
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
		LogHistory.getInstance().addLog(new LogElement(this, " addElezioneVote", "Aggiunta voto referendum nel DB"));
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
			if(referVote.isVote()!=null)
				preparedStmt.setBoolean(3, referVote.isVote());
			else
				preparedStmt.setNull(3,java.sql.Types.INTEGER);
			
			preparedStmt.executeQuery();
			
			return true;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public Boolean hasElettoreVotedForRef(Referendum ref) {
		LogHistory.getInstance().addLog(new LogElement(this, " hasElettoreVotedForRef", "Check elettore ha votato per Referendum da DB"));
		final String query = "SELECT `sistemaelettoraleingsw`.`hasElettoreVotedRef`(?, ?);";
		Connection dbConn = DBConnector.getDbConnection();

		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, SystemLoggedUser.getInstance().getUtenteLoggato().getId());
			preparedStmt.setInt(2, ref.getId());
			
			ResultSet rs = preparedStmt.executeQuery();
			
			rs.next();
			
			
			return rs.getBoolean(1);
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}

	@Override
	public Boolean hasElettoreVotedForElez(Elezione ele) {
		LogHistory.getInstance().addLog(new LogElement(this, " hasElettoreVotedForElez", "Check elettore ha votato per Elezione da DB"));
		final String query = "SELECT `sistemaelettoraleingsw`.`hasElettoreVotedElez`(?, ?);";
		Connection dbConn = DBConnector.getDbConnection();
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setString(1, SystemLoggedUser.getInstance().getUtenteLoggato().getId());
			preparedStmt.setInt(2, ele.getId());
			
			ResultSet rs = preparedStmt.executeQuery();

			rs.next();
			
			return rs.getBoolean(1);
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return false;
	}

	@Override
	public List<VotoReferendum_TB> getVotiReferendum(Referendum referendum) {
		LogHistory.getInstance().addLog(new LogElement(this, " getVotiReferendum", "Ottenimento voti referendum da DB"));
		final String query = "SELECT * FROM sistemaelettoraleingsw.votoreferendum v WHERE v.referendumId_fk = ?;";
		Connection dbConn = DBConnector.getDbConnection();
		
		if(!SystemLoggedUser.getInstance().isElettore()) {
			LogHistory.getInstance().addLog(new LogElement(this, "InstanceError", "Non ci si aspetta un elettore con queste funzioni",true));
			throw new IllegalStateException("Elettore cannot ask voti");
		}
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setInt(1, referendum.getId());
			
			ResultSet reSet = preparedStmt.executeQuery();
			
			List<VotoReferendum_TB> voti = new ArrayList<VotoReferendum_TB>();
			
			while(reSet.next()) {
				voti.add(new VotoReferendum_TB(
						reSet.getInt(1),
						reSet.getBoolean(2),
						reSet.getBoolean(3),
						referendum.getId()
						));
			}
			
			return voti;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
		
	}

	@Override
	public List<ElezioneVote> getVotiElezione(Elezione elezione) {
		LogHistory.getInstance().addLog(new LogElement(this, " getVotiElezione", "Ottenimento voti elezione da DB"));
		
		List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		
		if(!SystemLoggedUser.getInstance().isElettore()) {
			LogHistory.getInstance().addLog(new LogElement(this, "InstanceError", "Non ci si aspetta un elettore con queste funzioni",true));
			throw new IllegalStateException("Elettore cannot ask voti");
		}
				
		List<VotoElezione_TB> votazioni = getVotiElezioneTb(elezione);
		for (VotoElezione_TB votoElezione_TB : votazioni) {
			List<Partito> partiti = Partito.getAllPartitiVotatiInVoto(votoElezione_TB.getId());
			List<Candidato> candidati = Candidato.getAllCandidatiVoto(votoElezione_TB.getId());
			votiElezione.add(new ElezioneVote(elezione, candidati, partiti));
		}
		
		return votiElezione;
	}
	
	private List<VotoElezione_TB> getVotiElezioneTb(Elezione elezione){
		
		final String query = "SELECT * FROM sistemaelettoraleingsw.votoelezione WHERE elezione_fk = ?;";
		Connection dbConn = DBConnector.getDbConnection();
		
		if(!SystemLoggedUser.getInstance().isElettore()) {
			LogHistory.getInstance().addLog(new LogElement(this, "InstanceError", "Non ci si aspetta un elettore con queste funzioni",true));
			throw new IllegalStateException("Elettore cannot ask voti");
		}
		
		try {
			
			PreparedStatement preparedStmt = dbConn.prepareStatement(query);
			preparedStmt.setInt(1, elezione.getId());
			
			ResultSet reSet = preparedStmt.executeQuery();
			
			List<VotoElezione_TB> voti = new ArrayList<VotoElezione_TB>();
			
			while(reSet.next()) {
				voti.add(new VotoElezione_TB(
						reSet.getInt(1),
						reSet.getBoolean(2),
						reSet.getInt(3)));
			}
			
			return voti;
			
		} catch (SQLException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "SQLException", e.getSQLState(), true));
		}
		
		return null;
	}
	
	


}
