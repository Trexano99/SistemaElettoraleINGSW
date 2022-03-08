package useObject.utenze;

import java.util.ArrayList;
import java.util.List;

import auditing.LogElement;
import auditing.LogHistory;
import daoModels.ElezioneUpdater;
import daoModels.NewElezione;
import daoModels.NewReferendum;
import daoModels.ReferendumUpdater;
import daoModels.DbTablesRapresentation.GenericUser_TB;
import daoModels.DbTablesRapresentation.Impiegato_TB;
import daoModels.ImplTablesDao.ElezioneDao;
import daoModels.ImplTablesDao.GenericUserDao;
import daoModels.ImplTablesDao.ImpiegatoDao;
import daoModels.ImplTablesDao.ReferendumDao;
import useObject.General.SystemLoggedUser;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione;

public class Impiegato extends Utente {

	private Impiegato(String id, String nome, String cognome) {
		super(id, nome, cognome);
	}

	public static Boolean login(String username, String password) {

		GenericUser_TB utente = new GenericUser_TB(username, password);
		String userId = new GenericUserDao().loginImpiegato(utente);
		if(userId==null) {
			LogHistory.getInstance().addLog(new LogElement(Impiegato.class, "LoginError", "Error login for user: "+username));
			return false;
		}
		LogHistory.getInstance().addLog(new LogElement(Impiegato.class, "LoginSuccess", "Success login for user: "+username+"; His id is: "+userId));
		
		Impiegato_TB impTb =  new ImpiegatoDao().get(userId);

		SystemLoggedUser.getInstance().setUtenteLoggato(new Impiegato(impTb.getId(), impTb.getNome(), impTb.getCognome()));
		
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
	
	public Boolean modificaElezione(ElezioneUpdater modificheElezione) {
		LogHistory.getInstance().addLog(new LogElement(this, "modificaElezione", "Updating votation with id: "+modificheElezione.getId()));
		return new ElezioneDao().updateElezione(modificheElezione);
	}

	public Boolean eliminaElezione(Elezione elezioneDaEliminare) {
		LogHistory.getInstance().addLog(new LogElement(this, "getInstance", "Erasing votation with id: "+elezioneDaEliminare.getId()));
		return new ElezioneDao().removeElezione(elezioneDaEliminare);
	}
	
	public Boolean inserisciElezione(NewElezione elezioneDaInserire) {
		LogHistory.getInstance().addLog(new LogElement(this, "inserisciElezione", "Adding new votation"));
		return new ElezioneDao().addNewElezione(elezioneDaInserire);
	}
	
	public Boolean modificaReferendum(ReferendumUpdater modificheReferendum) {
		LogHistory.getInstance().addLog(new LogElement(this, "modificaReferendum", "Updating votation with id: "+modificheReferendum.getId()));
		return new ReferendumDao().updateReferendum(modificheReferendum);
	}

	public Boolean eliminaReferendum(Referendum referendumDaEliminare) {
		LogHistory.getInstance().addLog(new LogElement(this, "eliminaReferendum", "Erasing referendum with id: "+referendumDaEliminare.getId()));
		return new ReferendumDao().removeReferendum(referendumDaEliminare);
	}
	
	public Boolean inserisciReferendum(NewReferendum referendumDaInserire) {
		LogHistory.getInstance().addLog(new LogElement(this, "inserisciReferendum", "Adding new referendum"));
		return new ReferendumDao().addNewReferendum(referendumDaInserire);
	}	
	
	
	
}
