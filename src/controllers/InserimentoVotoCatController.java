package controllers;

import java.util.List;

import auditing.LogElement;
import auditing.LogHistory;
import javaFX.GraphicControllers.ElettoreMainViewController;
import javaFX.GraphicControllers.InserimentoCatVoteViewController;
import javaFX.GraphicControllers.InserimentoRefVoteViewController;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import useObject.General.SystemLoggedUser;
import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.utenze.Elettore;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione;
import useObject.voteElements.Votazione.TipologiaElezione;

public class InserimentoVotoCatController implements IVoteController  {

	private Elezione elezione;
	private InserimentoCatVoteViewController viewContr;
	
	
	
	public InserimentoVotoCatController(Elezione elezione, InserimentoCatVoteViewController viewContr) {
		this.elezione = elezione;
		this.viewContr = viewContr;
	}

	@Override
	public void populatePage() {
		populateHeader();
		populateListPartiti();
		if(elezione.getTipoElezione()==TipologiaElezione.VotazioneCategorica)
			populateListCandidati();
		viewContr.initializeTimer();
	}

	public void askConfirmation(Candidato scelta) {
		if(viewContr.chiediConferma("Confermare il voto?", "Confermare di star votando il candidato: "+scelta.toString())) {
			registerVote(scelta);
			viewContr.getPreviousPage();
		}
	}
	
	public void askConfirmation(Partito scelta) {
		if(viewContr.chiediConferma("Confermare il voto?", "Confermare di star votando il partito: "+scelta.toString())) {
			registerVote(scelta);
			viewContr.getPreviousPage();
		}
		
	}
	
	public void askConfirmation(Partito partito,List<Candidato>candidati ) {
		StringBuilder strB = new StringBuilder();
		strB.append("Confermare di star votando il partito: "+partito.toString());
		if(candidati!=null && candidati.size()>0) {
			strB.append("\nE per i suoi candidati: ");
			for (Candidato candidato : candidati) {
				strB.append("\n"+candidato.toString());
			}
		}
		if(viewContr.chiediConferma("Confermare il voto?", strB.toString())) {
			registerVote(partito, candidati);
			viewContr.getPreviousPage();
		}
	}
	
	public void askConfirmation() {
		if(viewContr.chiediConferma("Confermare il voto?", "Confermare di star votando: SCHEDA BIANCA")) {
			registerVote();
			viewContr.getPreviousPage();
		}
	}
	
	private void populateHeader() {
		String nomeUtente = SystemLoggedUser.getInstance().getUtenteLoggato().getNome()+" "+SystemLoggedUser.getInstance().getUtenteLoggato().getCognome();
		if(SystemLoggedUser.getInstance().getUtenteLoggato().getClass()==Elettore.class)
			viewContr.setHeaderContent(nomeUtente,"Elettore");
		else 
			viewContr.setHeaderContent(nomeUtente,"Impiegato");
	}

	private ObservableList<Candidato> candidatiList;
	
	private void populateListCandidati() {
		candidatiList = FXCollections.observableArrayList();
		candidatiList.addAll(Candidato.getAllCandidatiElezione(elezione));
		try {
			viewContr.addCandidatiToTable(candidatiList);
		}catch(Exception e) {
			LogHistory.getInstance().addLog(new LogElement(InserimentoVotoCatController.class, "populateListCandidati", "Errore nel popolare la tabella", true));
		}
	}
	
	public void populateListCandidatiDelPartito(Partito p) {
		candidatiList = FXCollections.observableArrayList();
		candidatiList.addAll(Candidato.getAllCandidatiPartito(p));
		try {
			viewContr.addCandidatiToTable(candidatiList);
		}catch(Exception e) {
			LogHistory.getInstance().addLog(new LogElement(InserimentoVotoCatController.class, "populateListCandidati", "Errore nel popolare la tabella", true));
		}
	}

	

	private ObservableList<Partito> partitiList;
	
	private void populateListPartiti() {
		partitiList = FXCollections.observableArrayList();
		partitiList.addAll(Partito.getAllPartitiElezione(elezione));
		try {
			viewContr.addPartitiToTable(partitiList);
		}catch(Exception e) {
			LogHistory.getInstance().addLog(new LogElement(InserimentoVotoCatController.class, "populateListPartiti", "Errore nel popolare la tabella", true));
		}
	}
		
	private void registerVote(Partito p) {
		Elettore e = (Elettore)SystemLoggedUser.getInstance().getUtenteLoggato();
		e.voteElez_Categorico(elezione, null, p);
	}
	
	private void registerVote(Candidato c) {
		Elettore e = (Elettore)SystemLoggedUser.getInstance().getUtenteLoggato();
		e.voteElez_Categorico(elezione, c, null);
	}
	
	private void registerVote(Partito p, List<Candidato> candidati) {
		Elettore e = (Elettore)SystemLoggedUser.getInstance().getUtenteLoggato();
		e.voteElez_CategoricoConPref(elezione, p , candidati);
	} 
	
	private void registerVote() {
		Elettore e = (Elettore)SystemLoggedUser.getInstance().getUtenteLoggato();
		e.voteElez_Categorico(elezione, null, null);
	}
	

}
