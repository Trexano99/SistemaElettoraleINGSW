package javaFX.GraphicControllers;


import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.ResourceBundle;

import auditing.LogElement;
import auditing.LogHistory;
import controllers.InserimentoVotoOrdController;
import javafx.beans.binding.Bindings;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.control.SelectionMode;
import javafx.scene.control.SplitPane;
import javafx.stage.Modality;
import javafx.stage.Stage;
import observer.timer.ITimerObserver;
import observer.timer.TimerTicker;
import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;

public class InserimentoOrdVoteViewController implements ITimerObserver, IBaseVoteView {

	private InserimentoVotoOrdController controller;
	
	public static Elezione elezione;
	
	public final static String TITOLO = "Sistema Elettorale - Inserimento Voto Ordinale";
	public final static String RESOURCE = "/javaFx/GraphicElements/InserimentoVotoOrdinale_Elettore.fxml";
	public final static int WIDTH = 600;
	public final static int HEIGTH = 500;
	
	@FXML
    private ResourceBundle resources;

    @FXML
    private URL location;

    @FXML
    private Button btnAnnulla;

    @FXML
    private Button btnInvia;

    @FXML
    private Button btnReset;

    @FXML
    private Button btn_aggiungiAScelti;

    @FXML
    private Button btn_rimuoviDaScelti;

    @FXML
    private Label lbNomeElettore;

    @FXML
    private Label lbRuoloElettore;

    @FXML
    private Label lbTimer;

    @FXML
    private ListView<Candidato> listCandidati;

    @FXML
    private ListView<Candidato> listCandidatiScelti;

    @FXML
    private ListView<Partito> listPartiti;

    @FXML
    private ListView<Partito> listPartitiScelti;

    @FXML
    private SplitPane mainPane;

    @FXML
    void annulla(ActionEvent event) {
    	getPreviousPage();
    }

    @FXML
    void reset(ActionEvent event) {
    	initialize();
    }

    @FXML
    void sendVote(ActionEvent event) {
    	List<Partito> partiti = listPartitiScelti.getItems();
    	List<Candidato>candidati = listCandidatiScelti.getItems();
    	if (partiti.isEmpty() && candidati.isEmpty())
    		controller.askConfirmation();
    	else
    		controller.askConfirmation(partiti,candidati);
    }
    
    @FXML
    void addSelectedToChoosen(ActionEvent event) {
    	if(!listCandidati.getSelectionModel().getSelectedItems().isEmpty()) {
	    	List<Candidato> selectedItems = listCandidati.getSelectionModel().getSelectedItems();
	    	listCandidatiScelti.getItems().addAll(selectedItems);
	    	listCandidati.getItems().removeAll(selectedItems);
    	}
    	if(!listPartiti.getSelectionModel().getSelectedItems().isEmpty()) {
	    	List<Partito> selectedItems = listPartiti.getSelectionModel().getSelectedItems();
	    	listPartitiScelti.getItems().addAll(selectedItems);
	    	listPartiti.getItems().removeAll(selectedItems);
    	}
    }
    
    @FXML
    void removeSelectedChoosen(ActionEvent event) {
    	if(!listCandidatiScelti.getSelectionModel().getSelectedItems().isEmpty()) {
	    	List<Candidato> selectedItems = listCandidatiScelti.getSelectionModel().getSelectedItems();
	    	listCandidati.getItems().addAll(selectedItems);
	    	listCandidatiScelti.getItems().removeAll(selectedItems);
    	}
    	if(!listPartitiScelti.getSelectionModel().getSelectedItems().isEmpty()) {
	    	List<Partito> selectedItems = listPartitiScelti.getSelectionModel().getSelectedItems();
	    	listPartiti.getItems().addAll(selectedItems);
	    	listPartitiScelti.getItems().removeAll(selectedItems);
    	}
    }

    @FXML
    void initialize() {
        assert btnAnnulla != null : "fx:id=\"btnAnnulla\" was not injected: check your FXML file 'InserimentoVotoOrdinale_Elettore.fxml'.";
        assert btnInvia != null : "fx:id=\"btnInvia\" was not injected: check your FXML file 'InserimentoVotoOrdinale_Elettore.fxml'.";
        assert btnReset != null : "fx:id=\"btnReset\" was not injected: check your FXML file 'InserimentoVotoOrdinale_Elettore.fxml'.";
        assert lbNomeElettore != null : "fx:id=\"lbNomeElettore\" was not injected: check your FXML file 'InserimentoVotoOrdinale_Elettore.fxml'.";
        assert lbRuoloElettore != null : "fx:id=\"lbRuoloElettore\" was not injected: check your FXML file 'InserimentoVotoOrdinale_Elettore.fxml'.";
        assert lbTimer != null : "fx:id=\"lbTimer\" was not injected: check your FXML file 'InserimentoVotoOrdinale_Elettore.fxml'.";
        assert listCandidati != null : "fx:id=\"listCandidati\" was not injected: check your FXML file 'InserimentoVotoOrdinale_Elettore.fxml'.";
        assert listCandidatiScelti != null : "fx:id=\"listCandidatiScelti\" was not injected: check your FXML file 'InserimentoVotoOrdinale_Elettore.fxml'.";
        assert listPartiti != null : "fx:id=\"listPartiti\" was not injected: check your FXML file 'InserimentoVotoOrdinale_Elettore.fxml'.";
        assert listPartitiScelti != null : "fx:id=\"listPartitiScelti\" was not injected: check your FXML file 'InserimentoVotoOrdinale_Elettore.fxml'.";
        assert mainPane != null : "fx:id=\"mainPane\" was not injected: check your FXML file 'InserimentoVotoOrdinale_Elettore.fxml'.";

        listCandidati.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
        listPartiti.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
        listCandidatiScelti.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
        listPartitiScelti.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
        
        setCellsFactory();
        
        if(elezione == null) 
        	throw new IllegalStateException("Not expected elezione null");
        
        controller = new InserimentoVotoOrdController(elezione, this);
        
        btn_aggiungiAScelti.disableProperty().bind(Bindings.and(
        		Bindings.isEmpty(listCandidati.getSelectionModel().getSelectedItems()), 
        		Bindings.isEmpty(listPartiti.getSelectionModel().getSelectedItems())));
        btn_rimuoviDaScelti.disableProperty().bind(Bindings.and(
        		Bindings.isEmpty(listCandidatiScelti.getSelectionModel().getSelectedItems()), 
        		Bindings.isEmpty(listPartitiScelti.getSelectionModel().getSelectedItems())));
        
        controller.populatePage();
    }

	@Override
	public void initializeTimer() {
		List<ITimerObserver> lista = new ArrayList<ITimerObserver>();
	    lista.add(this);
	    TimerTicker.createTimer(60*10, lista);
	}

	@Override
	public void setHeaderContent(String nominativoElettore, String ruoloElettore) {
		lbNomeElettore.setText(nominativoElettore);
    	lbRuoloElettore.setText("Ruolo utente: "+ruoloElettore);

	}

	@Override
	public void getPreviousPage() {
		try {
			 Stage stageTheEventSourceNodeBelongs = (Stage) (mainPane.getScene().getWindow());
			 Parent root = FXMLLoader.load(getClass().getResource(ElettoreMainViewController.RESOURCE));
			
			 stageTheEventSourceNodeBelongs.setTitle(ElettoreMainViewController.TITOLO);
			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, ElettoreMainViewController.WIDTH, ElettoreMainViewController.HEIGTH));
			 stageTheEventSourceNodeBelongs.show();
		} catch (IOException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "getPreviousPage", "Fail changing scene", true));
		}

	}

	@Override
	public void segnalaErrore(String nomeErrore, String contenutoErrore) {
		Stage stage = (Stage) mainPane.getScene().getWindow();
		
		Alert.AlertType type = Alert.AlertType.ERROR;
		Alert alert = new Alert(type, "");
		
		alert.initModality(Modality.APPLICATION_MODAL);
		alert.initOwner(stage);
		
		alert.getDialogPane().setContentText(contenutoErrore);
		alert.getDialogPane().setHeaderText(nomeErrore);
		
		alert.showAndWait();

	}

	@Override
	public Boolean chiediConferma(String titolo, String contenuto) {
		Stage stage = (Stage) mainPane.getScene().getWindow();
		
		Alert.AlertType type = Alert.AlertType.CONFIRMATION;
		Alert alert = new Alert(type, "");
		
		alert.initModality(Modality.APPLICATION_MODAL);
		alert.initOwner(stage);
		
		alert.getDialogPane().setContentText(contenuto);
		alert.getDialogPane().setHeaderText(titolo);
		
		Optional<ButtonType> result = alert.showAndWait();
		if(result.get() == ButtonType.OK) 
			return true;
		return false;
	}

	@Override
	public void thickedTimer(TimerTicker timer) {
		lbTimer.setText(timer.getSecondsString());

	}

	@Override
	public void endedTimer() {
		segnalaErrore("Tempo esaurito", "Si verrà riportati alla pagina precedente.");
		getPreviousPage();

	}
	
	private void setCellsFactory() {
		listPartiti.setCellFactory(partiti -> new ListCell<Partito>() {
		    @Override
		    protected void updateItem(Partito partito, boolean empty) {
		        super.updateItem(partito, empty);
		        if(empty || partito == null)
		        	setText(null);
		        else
		        	setText(partito.toString());
		    }
		});
		listCandidati.setCellFactory(candidati -> new ListCell<Candidato>() {
		    @Override
		    protected void updateItem(Candidato candidato, boolean empty) {
		        super.updateItem(candidato, empty);
		        if(empty || candidato == null)
		        	setText(null);
		        else
		        	setText(candidato.toString());
		    }
		});
		listPartitiScelti.setCellFactory(partiti -> new ListCell<Partito>() {
		    @Override
		    protected void updateItem(Partito partito, boolean empty) {
		        super.updateItem(partito, empty);
		        if(empty || partito == null)
		        	setText(null);
		        else
		        	setText(partito.toString());
		    }
		});
		listCandidatiScelti.setCellFactory(candidati -> new ListCell<Candidato>() {
		    @Override
		    protected void updateItem(Candidato candidato, boolean empty) {
		        super.updateItem(candidato, empty);
		        if(empty || candidato == null)
		        	setText(null);
		        else
		        	setText(candidato.toString());
		    }
		});
	}

	public void addCandidatiToTable(ObservableList<Candidato> candidatiList) {
		listCandidati.setItems(candidatiList);
		
	}

	public void addPartitiToTable(ObservableList<Partito> partitiList) {
		listPartiti.setItems(partitiList);
		
	}

}
