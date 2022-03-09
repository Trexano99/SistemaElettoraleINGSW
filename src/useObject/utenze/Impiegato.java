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
	/*@ assignable id;
	 @ assignable nome;
	 @ assignable cognome;
	 @*/
	private Impiegato(String id, String nome, String cognome) {
		super(id, nome, cognome);
	}
	/*{context Impiegato :: login(username : String, password : String): Boolean
	 * if GenericUserDao().loginImpiegato(utente) result = false
	 * 		else result = true
	 * 	endif
	 *}*/
	
	/*@ requires username != null;
	 @ requires password != null;
	 @ ensures (GenericUserDao().loginImpiegato(utente) != null && \result == false) ||
	 @ 				(GenericUserDao().loginImpiegato(utente) == null && \result == false);
	 @*/
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
	/*{context Impiegato :: getAllVotazioni(): List<Votazione>
	 * 	inv votazioni: self.getAllVotazioni()
	 *	votazioni -> collect(Elezione.getAllElezioni() and collect(Referendum.getAllReferendums())
	 *	post: result = votazioni
	 *}*/
	/*@ "votazioni = new getAllVotazioni()";
	 @ assignable votazioni;
	 @ ensures votazioni  == \old(votazioni) + Elezione.getAllElezioni() +Referendum.getAllReferendums();
	 @ ensures \result == votazioni;
	 @*/
	@Override
	public List<Votazione> getAllVotazioni() {
		LogHistory.getInstance().addLog(new LogElement(this, "VotationRequest", "Asked for Votation"));
		List<Votazione> votazioni = new ArrayList<>();
		votazioni.addAll(Elezione.getAllElezioni());
		votazioni.addAll(Referendum.getAllReferendums());
		return votazioni;
	}
	
	/*{context Impiegato :: modificaElezione(modificheElezione : ElezioneUpdater) : Boolean
	 * post: LogElement(self, :String, :String)
	 * post: result = ElezioneDao().updateElezione(modificheElezione)
	 *}*/
	/*@ requires modificheElezione != null;
	 @ ensures LogElement(this, "modificaElezione", "Updating votation with id: "+modificheElezione.getId());
	 @ ensures \result == ElezioneDao().updateElezione(modificheElezione);
	 @*/
	public Boolean modificaElezione(ElezioneUpdater modificheElezione) {
		LogHistory.getInstance().addLog(new LogElement(this, "modificaElezione", "Updating votation with id: "+modificheElezione.getId()));
		return new ElezioneDao().updateElezione(modificheElezione);
	}
	/*{context Impiegato :: eliminaElezione(elezioneDaEliminare : Elezione) : Boolean
	 * post: LogElement(self, :String, :String)
	 * post: result = ElezioneDao().removeElezione(elezioneDaEliminare)
	 *}*/
	/*@ requires elezioneDaEliminare != null;
	 @ ensures LogElement(this, "getInstance", "Erasing votation with id: "+elezioneDaEliminare.getId());
	 @ ensures \result == ElezioneDao().removeElezione(elezioneDaEliminare);
	 @*/
	public Boolean eliminaElezione(Elezione elezioneDaEliminare) {
		LogHistory.getInstance().addLog(new LogElement(this, "getInstance", "Erasing votation with id: "+elezioneDaEliminare.getId()));
		return new ElezioneDao().removeElezione(elezioneDaEliminare);
	}
	/*{context Impiegato :: inserisciElezione(elezioneDaInserire : NewElezione) : Boolean
	 * post: LogElement(self, :String, :String)
	 * post: result = ElezioneDao().addNewElezione(elezioneDaInserire)
	 *}*/
	/*@ requires elezioneDaInserire != null;
	 @ ensures LogElement(this, "inserisciElezione", "Adding new votation");
	 @ ensures \result == ElezioneDao().addNewElezione(elezioneDaInserire));
	 @*/
	public Boolean inserisciElezione(NewElezione elezioneDaInserire) {
		LogHistory.getInstance().addLog(new LogElement(this, "inserisciElezione", "Adding new votation"));
		return new ElezioneDao().addNewElezione(elezioneDaInserire);
	}
	/*{context Impiegato :: modificaReferendum(modificheReferendum : ReferendumUpdater) : Boolean
	 * post: LogElement(self, :String, :String)
	 * post: result = ReferendumDao().updateReferendum(modificheReferendum)
	 *}*/
	/*@ requires modificheElezione != null;
	 @ ensures LogElement(this, "modificaReferendum", "Updating votation with id: "+modificheReferendum.getId());
	 @ ensures \result == ReferendumDao().updateReferendum(modificheReferendum);
	 @*/
	public Boolean modificaReferendum(ReferendumUpdater modificheReferendum) {
		LogHistory.getInstance().addLog(new LogElement(this, "modificaReferendum", "Updating votation with id: "+modificheReferendum.getId()));
		return new ReferendumDao().updateReferendum(modificheReferendum);
	}
	/*{context Impiegato :: eliminaReferendum(referendumDaEliminare : Referendum) : Boolean
	 * post: LogElement(self, :String, :String)
	 * post: result = ReferendumDao().removeReferendum(referendumDaEliminare)
	 *}*/
	/*@ requires referendumDaEliminare != null;
	 @ ensures LogElement(this, "eliminaReferendum", "Erasing referendum with id: "+referendumDaEliminare.getId());
	 @ ensures \result == ReferendumDao().removeReferendum(referendumDaEliminare);
	 @*/
	public Boolean eliminaReferendum(Referendum referendumDaEliminare) {
		LogHistory.getInstance().addLog(new LogElement(this, "eliminaReferendum", "Erasing referendum with id: "+referendumDaEliminare.getId()));
		return new ReferendumDao().removeReferendum(referendumDaEliminare);
	}
	/*{context Impiegato :: inserisciReferendum(referendumDaInserire : NewReferendum) : Boolean
	 * post: LogElement(self, :String, :String)
	 * post: result = ReferendumDao().addNewReferendum(referendumDaInserire)
	 *}*/
	/*@ requires referendumDaInserire != null;
	 @ ensures LogElement(this, "inserisciReferendum", "Adding new referendum"));
	 @ ensures \result == ReferendumDao().addNewReferendum(referendumDaInserire);
	 @*/
	public Boolean inserisciReferendum(NewReferendum referendumDaInserire) {
		LogHistory.getInstance().addLog(new LogElement(this, "inserisciReferendum", "Adding new referendum"));
		return new ReferendumDao().addNewReferendum(referendumDaInserire);
	}	
	
	
	
}
