package controllers;

import auditing.LogElement;
import auditing.LogHistory;
import controllers.LogInController.LogInType;
import javaFX.GraphicControllers.ElettoreMainViewController;
import javaFX.GraphicControllers.LogInViewController;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import useObject.General.SystemLoggedUser;
import useObject.utenze.Elettore;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione;

public class ElettoreMainController  {
	
	public static void populatePage(ElettoreMainViewController view) {
		populateHeader(view);
		populateTable(view);
	}
	
	private static void populateHeader(ElettoreMainViewController view) {
		String nomeUtente = SystemLoggedUser.getInstance().getUtenteLoggato().getNome()+" "+SystemLoggedUser.getInstance().getUtenteLoggato().getCognome();
		if(SystemLoggedUser.getInstance().getUtenteLoggato().getClass()==Elettore.class)
			view.setHeaderContent(nomeUtente,"Elettore");
		else 
			view.setHeaderContent(nomeUtente,"Impiegato");
	}

	private static ObservableList<Votazione> data;
	
	private static void populateTable(ElettoreMainViewController view) {
		data = FXCollections.observableArrayList();
		try {
			Votazione[] elezioni =  Elezione.getAllElezioni().toArray(new Elezione[0]);
	   	 	Votazione[] referendum =  (Votazione[]) Referendum.getAllReferendums().toArray(new Referendum[0]);
	    	data.addAll(concatenate(elezioni, referendum));
	    	view.addToTable(data);
		}catch(Exception e) {
			LogHistory.getInstance().addLog(new LogElement(ElettoreMainController.class, "populateTable", "Errore nel popolare la tabella", true));
		}
	}
	
	public static void votaElezione(Votazione votazione, ElettoreMainViewController view) {
		switch ((votazione).getTipoElezione()) {
			case Referendum:
				view.showReferendum((Referendum)votazione);
				break;
			case VotazioneCategorica:
			case VotazioneCategoricaConPref:
				view.showVotoCategorico((Elezione)votazione);
				break;
			case VotazioneOrdinale:
				view.showVotoOrdinale((Elezione)votazione);
				break;
			default:
				LogHistory.getInstance().addLog(new LogElement(ElettoreMainController.class, "votaElezione", "Not expected", true));
				break;
			}
	}
	
	private static Votazione[] concatenate(Votazione[] a, Votazione[] b) {
	    int aLen = a.length;
	    int bLen = b.length;

	    @SuppressWarnings("unchecked")
	    Votazione[] c = new Votazione[aLen+bLen];
	    System.arraycopy(a, 0, c, 0, aLen);
	    System.arraycopy(b, 0, c, aLen, bLen);

	    return c;
	}
	
}
