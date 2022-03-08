package controllers;

import javaFX.GraphicControllers.EsitoReferendumViewController;
import useObject.General.SystemLoggedUser;
import useObject.utenze.Elettore;
import useObject.voteElements.Referendum;
import useObject.voteElements.results.EsitoReferendum;

public class EsitoReferendumController {

	private Referendum referendum;
	private EsitoReferendumViewController esitoReferendumViewController;
	
	public EsitoReferendumController(Referendum referendum,
			EsitoReferendumViewController esitoReferendumViewController) {
		this.referendum = referendum;
		this.esitoReferendumViewController = esitoReferendumViewController;
	}



	public void populatePage() {
		populateHeader();
		esitoReferendumViewController.popolaDati(EsitoReferendum.getEsitoReferendum(referendum));
	}
	
	private void populateHeader() {
		String nomeUtente = SystemLoggedUser.getInstance().getUtenteLoggato().getNome()+" "+SystemLoggedUser.getInstance().getUtenteLoggato().getCognome();
		if(SystemLoggedUser.getInstance().getUtenteLoggato().getClass()==Elettore.class)
			esitoReferendumViewController.setHeaderContent(nomeUtente,"Elettore");
		else 
			esitoReferendumViewController.setHeaderContent(nomeUtente,"Impiegato");
	}

}
