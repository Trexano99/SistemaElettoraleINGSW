package controllers;

import javaFX.GraphicControllers.EsitoElezioneViewController;
import javafx.collections.FXCollections;
import useObject.General.SystemLoggedUser;
import useObject.utenze.Elettore;
import useObject.voteElements.Elezione;
import useObject.voteElements.results.EsitoElezione;

public class EsitoElezioneController {

	private Elezione elezione;
	private EsitoElezioneViewController viewContr;
	

	public EsitoElezioneController(Elezione elezione, EsitoElezioneViewController viewContr) {
		super();
		this.elezione = elezione;
		this.viewContr = viewContr;
	}

	public void populatePage() {
		populateHeader();
		EsitoElezione esito = EsitoElezione.getEsitoElezione(elezione);
		populateListPartiti(esito);
		populateListCanditi(esito);
		viewContr.popolaDati(esito);
	}


	private void populateHeader() {
		String nomeUtente = SystemLoggedUser.getInstance().getUtenteLoggato().getNome()+" "+SystemLoggedUser.getInstance().getUtenteLoggato().getCognome();
		if(SystemLoggedUser.getInstance().getUtenteLoggato().getClass()==Elettore.class)
			viewContr.setHeaderContent(nomeUtente,"Elettore");
		else 
			viewContr.setHeaderContent(nomeUtente,"Impiegato");
	}

	private void populateListCanditi(EsitoElezione esito) {
		viewContr.addCandidatiToTable(FXCollections.observableArrayList(esito.getVotiCandidati()));
	}
	
	private void populateListPartiti(EsitoElezione esito) {
		viewContr.addPartitiToTable(FXCollections.observableArrayList(esito.getVotiPartiti()));
	}
}
