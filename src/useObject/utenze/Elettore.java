package useObject.utenze;

import java.util.ArrayList;
import java.util.List;

import auditing.LogElement;
import auditing.LogHistory;
import daoModels.ElezioneVote_Categorico;
import daoModels.ElezioneVote_CategoricoConPref;
import daoModels.ElezioneVote_Ordinale;
import daoModels.ReferendumVote;
import daoModels.DbTablesRapresentation.Elettore_TB;
import daoModels.DbTablesRapresentation.GenericUser_TB;
import daoModels.ImplTablesDao.ElettoreDao;
import daoModels.ImplTablesDao.GenericUserDao;
import daoModels.ImplTablesDao.VotazioneDao;
import useObject.General.SystemLoggedUser;
import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione;
import useObject.voteElements.Votazione.TipologiaElezione;

public class Elettore extends Utente{
	
	/*
	 @ assignable id;
	 @ assignable nome;
	 @ assignable cognome;
	 @*/
	private Elettore(String id, String nome, String cognome) {
		super(id, nome, cognome);
	}

	
	public static Boolean login(String username, String password) {
		GenericUser_TB utente = new GenericUser_TB(username, password);
		String userId = new GenericUserDao().loginElettore(utente);
		if(userId==null) {
			LogHistory.getInstance().addLog(new LogElement(Elettore.class, "LoginFailed", "Failed login for user: "+username));
			return false;
		}
		LogHistory.getInstance().addLog(new LogElement(Elettore.class, "LoginSuccess", "Success login for user: "+username+"; His id is: "+userId));
		
		Elettore_TB elettoreTB = new ElettoreDao().get(userId);
				
		SystemLoggedUser.getInstance().setUtenteLoggato(new Elettore(elettoreTB.getCodiceFiscale(), elettoreTB.getNome(),elettoreTB.getCognome()));
		
		return true;
	}

	@Override
	public List<Votazione> getAllVotazioni() {
		LogHistory.getInstance().addLog(new LogElement(this, "VotationRequest", "Asked for Votation"));
		
		List<Votazione> votazioni = new ArrayList<>();
		votazioni.addAll(Elezione.getAllElezioni());
		votazioni.addAll(Referendum.getAllReferendums());
		return votazioni;
	}

	public boolean voteRef(Referendum r, Boolean vote) {
		LogHistory.getInstance().addLog(new LogElement(this, "voteReferendum", "Votation for referendum"));
		ReferendumVote rv = new ReferendumVote(r, vote);
		return (new VotazioneDao()).addReferendumVote(rv);
	} 
	
	public boolean voteElez_Categorico(Elezione e, Candidato c, Partito p) {
		if(!e.getTipoElezione().equals(TipologiaElezione.VotazioneCategorica))
		{
			LogHistory.getInstance().addLog(new LogElement(this,"voteElez_Categorico" , "Voto non ammesso per questa elezione",true));
			throw new IllegalStateException("Inconsistent vote for this election");
		}
		ElezioneVote_Categorico votoCat = new ElezioneVote_Categorico(e, c, p);
		return (new VotazioneDao()).addElezioneVote(votoCat);
		
	}
	
	public boolean voteElez_CategoricoConPref(Elezione e, Partito p, List<Candidato> candidati) {
		if(!e.getTipoElezione().equals(TipologiaElezione.VotazioneCategoricaConPref))
		{
			LogHistory.getInstance().addLog(new LogElement(this,"voteElez_CategoricoConPref" , "Voto non ammesso per questa elezione",true));
			throw new IllegalStateException("Inconsistent vote for this election");
		}
		ElezioneVote_CategoricoConPref votoCatP = new ElezioneVote_CategoricoConPref(e, p, candidati);
		return (new VotazioneDao()).addElezioneVote(votoCatP);
		
	}
	
	public boolean voteElez_Ordinale(Elezione e, List<Partito> partiti, List<Candidato> candidati) {
		if(!e.getTipoElezione().equals(TipologiaElezione.VotazioneOrdinale))
		{
			LogHistory.getInstance().addLog(new LogElement(this,"voteElez_Ordinale" , "Voto non ammesso per questa elezione",true));
			throw new IllegalStateException("Inconsistent vote for this election");
		}
		ElezioneVote_Ordinale votoOrd = new ElezioneVote_Ordinale(e, partiti, candidati);
		return (new VotazioneDao()).addElezioneVote(votoOrd);
		
	}

}
