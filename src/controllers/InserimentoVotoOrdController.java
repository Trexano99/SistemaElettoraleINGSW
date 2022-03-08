package controllers;

import java.util.List;

import auditing.LogElement;
import auditing.LogHistory;
import javaFX.GraphicControllers.InserimentoOrdVoteViewController;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import useObject.General.SystemLoggedUser;
import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.utenze.Elettore;
import useObject.voteElements.Elezione;

public class InserimentoVotoOrdController implements IVoteController {

	private Elezione elezione;
	private InserimentoOrdVoteViewController viewContr;
	
	public InserimentoVotoOrdController(Elezione elezione, InserimentoOrdVoteViewController viewContr) {
		this.elezione = elezione;
		this.viewContr = viewContr;
	}

	@Override
	public void populatePage() {
		populateHeader();
		populateListPartiti();
		populateListCandidati();
		viewContr.initializeTimer();

	}
	
	public void askConfirmation(List<Partito> partiti,List<Candidato>candidati ) {
		StringBuilder strB = new StringBuilder();
		if(partiti!=null && partiti.size()> 0) {
			strB.append("Confermare di star votando i seguenti partiti nel rispettivo ordine: ");
			for(int i = 0; i < partiti.size(); i++) 
				strB.append("\n"+i+") "+partiti.get(i).toString());
		}
		if(candidati!=null && candidati.size()>0) {
			strB.append("\nConfermare di star votando i seguenti candidati nel rispettivo ordine: ");
			for(int i = 0; i < candidati.size(); i++) 
				strB.append("\n"+i+") "+candidati.get(i).toString());
		}
		if(viewContr.chiediConferma("Confermare il voto?", strB.toString())) {
			registerVote(partiti, candidati);
			viewContr.getPreviousPage();
		}
	}
	
	public void askConfirmation() {
		if(viewContr.chiediConferma("Confermare il voto?", "Confermare di star votando: SCHEDA BIANCA")) {
			registerVote();
			viewContr.getPreviousPage();
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

	private void populateHeader() {
		String nomeUtente = SystemLoggedUser.getInstance().getUtenteLoggato().getNome()+" "+SystemLoggedUser.getInstance().getUtenteLoggato().getCognome();
		if(SystemLoggedUser.getInstance().getUtenteLoggato().getClass()==Elettore.class)
			viewContr.setHeaderContent(nomeUtente,"Elettore");
		else 
			viewContr.setHeaderContent(nomeUtente,"Impiegato");
		
	}


	
	private void registerVote() {
		Elettore e = (Elettore)SystemLoggedUser.getInstance().getUtenteLoggato();
		e.voteElez_Ordinale(elezione, null, null);
	}
	
	private void registerVote(List<Partito> partiti,List<Candidato>candidati) {
		Elettore e = (Elettore)SystemLoggedUser.getInstance().getUtenteLoggato();
		e.voteElez_Ordinale(elezione, partiti, candidati);
	}
	
}
