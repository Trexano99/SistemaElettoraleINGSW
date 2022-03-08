package controllers;

import auditing.LogElement;
import auditing.LogHistory;
import daoModels.ElezioneUpdater;
import daoModels.NewElezione;
import daoModels.NewReferendum;
import daoModels.ReferendumUpdater;
import javaFX.GraphicControllers.NuovaVotazioneViewController;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import useObject.General.SystemLoggedUser;
import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.utenze.Elettore;
import useObject.utenze.Impiegato;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione;

public class NuovaVotazioneController {

	private NuovaVotazioneViewController viewContr;
	private Votazione toUpdate = null;
	
	public NuovaVotazioneController(NuovaVotazioneViewController nuovaVotazioneViewController, Votazione toUpdate) {
		this.viewContr = nuovaVotazioneViewController;
		this.toUpdate = toUpdate;
	}

	public void populatePage() {
		populateHeader();
		populateListPartiti();
		populateListCandidati();
		if(toUpdate!=null) 
			viewContr.PopulateAllWithDati(toUpdate);
		
	}

	public void askConfirmation(NewElezione newElez) {
		if(viewContr.chiediConferma("Conferma elezione", "Confermare di voler proseguire?")) {
			if(toUpdate==null) {
				registerNewElezione(newElez);
				viewContr.getPreviousPage();
			}else {
				updateElezione(newElez);
				viewContr.getPreviousPage();
			}
		}
	}

	public void askConfirmation(NewReferendum newRefer) {
		if(viewContr.chiediConferma("Conferma referendum", "Confermare di voler proseguire?")) {
			if(toUpdate==null) {
				registerNewReferendum(newRefer);
				viewContr.getPreviousPage();
			}else {
				updateReferendum(newRefer);
				viewContr.getPreviousPage();
			}
		}
	}
	
	private void populateHeader() {
		String nomeUtente = SystemLoggedUser.getInstance().getUtenteLoggato().getNome()+" "+SystemLoggedUser.getInstance().getUtenteLoggato().getCognome();
		if(SystemLoggedUser.getInstance().getUtenteLoggato().getClass()==Elettore.class)
			viewContr.setHeaderContent(nomeUtente,"Elettore");
		else 
			viewContr.setHeaderContent(nomeUtente,"Impiegato");
		
	}
	
	private ObservableList<Partito> partitiList;
	private void populateListPartiti() {
		ObservableList<Partito> partitiScelti = getPartitiScelti();
		partitiList = FXCollections.observableArrayList();
		partitiList.addAll(Partito.getAllPartiti());
		partitiList.removeAll(partitiScelti);
		try {
			viewContr.addPartitiToTable(partitiList);
			viewContr.addPartitiSceltiToTable(partitiScelti);
		}catch(Exception e) {
			LogHistory.getInstance().addLog(new LogElement(this, "populateListPartiti", "Errore nel popolare la tabella", true));
		}		
	}
	private ObservableList<Partito> getPartitiScelti() {
		if(toUpdate!=null && toUpdate.getClass()==Elezione.class) {
			Elezione elez = (Elezione)toUpdate;
			return  FXCollections.observableArrayList(Partito.getAllPartitiElezione(elez));
		}
		return FXCollections.observableArrayList();
	}

	private ObservableList<Candidato> candidatiList;
	private void populateListCandidati() {
		ObservableList<Candidato> candidatiScelti = getCandidatiScelti();
		candidatiList = FXCollections.observableArrayList();
		candidatiList.addAll(Candidato.getAllCandidati());
		candidatiList.removeAll(candidatiScelti);
		try {
			viewContr.addCandidatiToTable(candidatiList);
			viewContr.addCandidatiSceltiToTable(candidatiScelti);
		}catch(Exception e) {
			LogHistory.getInstance().addLog(new LogElement(this, "populateListCandidati", "Errore nel popolare la tabella", true));
		}
		
	}
	private  ObservableList<Candidato>  getCandidatiScelti() {
		if(toUpdate!=null && toUpdate.getClass()==Elezione.class) {
			Elezione elez = (Elezione)toUpdate;
			return FXCollections.observableArrayList(Candidato.getAllCandidatiElezione(elez));
		}
		return FXCollections.observableArrayList();
	}
	
	private void registerNewReferendum(NewReferendum referendum) {
		Impiegato impiegato = (Impiegato)SystemLoggedUser.getInstance().getUtenteLoggato();
		impiegato.inserisciReferendum(referendum);
	}
	
	private void registerNewElezione(NewElezione elezione) {
		Impiegato impiegato = (Impiegato)SystemLoggedUser.getInstance().getUtenteLoggato();
		impiegato.inserisciElezione(elezione);
	}
	
	private void updateReferendum(NewReferendum referendum) {
		Impiegato impiegato = (Impiegato)SystemLoggedUser.getInstance().getUtenteLoggato();
		ReferendumUpdater refUpd = new ReferendumUpdater((Referendum)toUpdate);
		refUpd.setNome(referendum.getNomeBreve());
		refUpd.setQuesito(referendum.getQuesito());
		refUpd.setWithQuorum(referendum.getWithQuorum());
		impiegato.modificaReferendum(refUpd);
	}
	
	private void updateElezione(NewElezione elezione) {
		Impiegato impiegato = (Impiegato)SystemLoggedUser.getInstance().getUtenteLoggato();
		ElezioneUpdater elezUpd = new ElezioneUpdater((Elezione)toUpdate);
		elezUpd.setNome(elezione.getNomeBreve());
		elezUpd.setMaggioranzaAssoluta(elezione.getMaggioranzaAssoluta());
		elezUpd.setTipoElezione(elezione.getTipoElezione());
		elezUpd.setCandidatiProposti(elezione.getCandidatiPartecipanti());
		elezUpd.setPartitiProposti(elezione.getPartitiPartecipanti());
		impiegato.modificaElezione(elezUpd);
	}

	

}
