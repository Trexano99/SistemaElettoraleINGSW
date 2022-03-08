package controllers;

import auditing.LogElement;
import auditing.LogHistory;
import daoModels.ElezioneUpdater;
import daoModels.ReferendumUpdater;
import javaFX.GraphicControllers.ImpiegatoMainViewController;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import useObject.General.SystemLoggedUser;
import useObject.utenze.Elettore;
import useObject.utenze.Impiegato;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione;

public class ImpiegatoMainController {

	private ImpiegatoMainViewController view;
	
	
	
	public ImpiegatoMainController(ImpiegatoMainViewController view) {
		super();
		this.view = view;
	}

	public void eraseElezione(Votazione selectedItem) {
		if(view.chiediConferma("Eliminazione votazione", "Si vuole procedere con l'eliminazione della votazione: "+selectedItem.getNome())) {
			if(selectedItem.getClass().equals(Elezione.class))
				((Impiegato) SystemLoggedUser.getInstance().getUtenteLoggato()).eliminaElezione((Elezione) selectedItem);
			else
				((Impiegato) SystemLoggedUser.getInstance().getUtenteLoggato()).eliminaReferendum((Referendum) selectedItem);
			populateTable();
		}
	}

	public void openVotation(Votazione selectedItem) {
		
		if(selectedItem.getClass().equals(Elezione.class)) {
			ElezioneUpdater eu = new ElezioneUpdater(((Elezione) selectedItem));
			eu.setClosed(false);
			((Impiegato) SystemLoggedUser.getInstance().getUtenteLoggato()).modificaElezione(eu);
		}
		else {
			ReferendumUpdater ru = new ReferendumUpdater((Referendum) selectedItem);
			ru.setClosed(false);
			((Impiegato) SystemLoggedUser.getInstance().getUtenteLoggato()).modificaReferendum(ru);
		}
		populateTable();
		
	}
	
	public void closeVotation(Votazione selectedItem) {
		if(selectedItem.getClass() == Elezione.class) {
			ElezioneUpdater eu = new ElezioneUpdater(((Elezione) selectedItem));
			eu.setClosed(true);
			eu.setFinished(true);
			((Impiegato) SystemLoggedUser.getInstance().getUtenteLoggato()).modificaElezione(eu);
		}else {
			ReferendumUpdater ru = new ReferendumUpdater(((Referendum) selectedItem));
			ru.setClosed(true);
			ru.setFinished(true);
			((Impiegato) SystemLoggedUser.getInstance().getUtenteLoggato()).modificaReferendum(ru);
		}
		
		populateTable();
		
	}

	public void getResultVotation(Votazione selectedItem) {
		if(selectedItem.getClass() == Elezione.class) {
			
		}else {
			
		}
		
	}

	public void populatePage() {
		populateHeader();
		populateTable();
		
	}
	
	private void populateHeader() {
		String nomeUtente = SystemLoggedUser.getInstance().getUtenteLoggato().getNome()+" "+SystemLoggedUser.getInstance().getUtenteLoggato().getCognome();
		if(SystemLoggedUser.getInstance().getUtenteLoggato().getClass()==Elettore.class)
			view.setHeaderContent(nomeUtente,"Elettore");
		else 
			view.setHeaderContent(nomeUtente,"Impiegato");
	}

	private static ObservableList<Votazione> data;
	private void populateTable() {
		data = FXCollections.observableArrayList();
		try {
			Votazione[] elezioni =  Elezione.getAllElezioni().toArray(new Elezione[0]);
	   	 	Votazione[] referendum =  (Votazione[]) Referendum.getAllReferendums().toArray(new Referendum[0]);
	    	data.addAll(concatenate(elezioni, referendum));
	    	view.addToTable(data);
		}catch(Exception e) {
			LogHistory.getInstance().addLog(new LogElement(this, "populateTable", "Errore nel popolare la tabella", true));
		}
	}
	
	private static Votazione[] concatenate(Votazione[] a, Votazione[] b) {
	    int aLen = a.length;
	    int bLen = b.length;

	    Votazione[] c = new Votazione[aLen+bLen];
	    System.arraycopy(a, 0, c, 0, aLen);
	    System.arraycopy(b, 0, c, aLen, bLen);

	    return c;
	}
}
