package controllers;

import javaFX.GraphicControllers.InserimentoRefVoteViewController;
import useObject.General.SystemLoggedUser;
import useObject.utenze.Elettore;
import useObject.voteElements.Referendum;

public class InserimentoVotoReferendumController implements IVoteController {
	
	private Referendum referendum;
	private InserimentoRefVoteViewController view;
	
	public InserimentoVotoReferendumController(Referendum referendum, InserimentoRefVoteViewController view) {
		this.referendum = referendum;
		this.view = view;
	}

	public void populatePage() {
		String nomeUtente = SystemLoggedUser.getInstance().getUtenteLoggato().getNome()+" "+SystemLoggedUser.getInstance().getUtenteLoggato().getCognome();
		if(SystemLoggedUser.getInstance().getUtenteLoggato().getClass()==Elettore.class)
			view.setHeaderContent(nomeUtente,"Elettore");
		else 
			view.setHeaderContent(nomeUtente,"Impiegato");
		view.initializeDomandaReferendum(referendum.getQuesito());
		view.initializeTimer();
	}
	
	public void registerVote(Boolean vote) {
		Elettore e = (Elettore)SystemLoggedUser.getInstance().getUtenteLoggato();
		e.voteRef(referendum, vote);
	}
	
	public void askConfirmation(Boolean scelta) {
		
		StringBuilder strB = new StringBuilder();
		strB.append("Hai votato per il referendum "+referendum.getNome()+" con il voto: ");
		if(scelta==null)
			strB.append("VOTO BIANCO");
		else if (scelta == false)
			strB.append("NO");
		else
			strB.append("SI");
		if(view.chiediConferma("Si vuole confermare il voto?", strB.toString())) {
			registerVote(scelta);
			view.getPreviousPage();
		}

    	
	}
	
}
