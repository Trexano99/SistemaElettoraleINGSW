package javaFX.GraphicControllers;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import auditing.LogElement;
import auditing.LogHistory;
import controllers.InserimentoVotoCatController;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
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
import useObject.voteElements.Votazione.TipologiaElezione;

public class InserimentoCatVoteViewController implements ITimerObserver, IBaseVoteView {

	private InserimentoVotoCatController controller;
	
	public static Elezione elezione;
	
	public final static String TITOLO = "Sistema Elettorale - Inserimento Voto Categorico";
	public final static String RESOURCE = "/javaFx/GraphicElements/InserimentoVotoCategorico_Elettore.fxml";
	public final static int WIDTH = 600;
	public final static int HEIGTH = 500;
	
	 @FXML
	    private Button btnAnnulla;

	    @FXML
	    private Button btnInvia;

	    @FXML
	    private Button btnReset;

	    @FXML
	    private Label lbNomeElettore;

	    @FXML
	    private Label lbRuoloElettore;

	    @FXML
	    private Label lbTimer;

	    @FXML
	    private ListView<Candidato> listCandidati;

	    @FXML
	    private ListView<Partito> listPartiti;

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
	    	if(listCandidati.getSelectionModel().getSelectedItem()==null&&listPartiti.getSelectionModel().getSelectedItem()==null)
				controller.askConfirmation();
	    	if(elezione.getTipoElezione()==TipologiaElezione.VotazioneCategorica) {
		    	if(listCandidati.getSelectionModel().getSelectedItem()!=null)
					controller.askConfirmation(listCandidati.getSelectionModel().getSelectedItem());
				else if(listPartiti.getSelectionModel().getSelectedItem()!=null)
					controller.askConfirmation(listPartiti.getSelectionModel().getSelectedItem());
	    	}else 
	    		controller.askConfirmation(listPartiti.getSelectionModel().getSelectedItem(),listCandidati.getSelectionModel().getSelectedItems());
	    		
	    }
	    
	    @FXML
	    void initialize() {
	        assert btnAnnulla != null : "fx:id=\"btnAnnulla\" was not injected: check your FXML file 'InserimentoVotoCategorico_Elettore.fxml'.";
	        assert btnInvia != null : "fx:id=\"btnInvia\" was not injected: check your FXML file 'InserimentoVotoCategorico_Elettore.fxml'.";
	        assert btnReset != null : "fx:id=\"btnReset\" was not injected: check your FXML file 'InserimentoVotoCategorico_Elettore.fxml'.";
	        assert lbNomeElettore != null : "fx:id=\"lbNomeElettore\" was not injected: check your FXML file 'InserimentoVotoCategorico_Elettore.fxml'.";
	        assert lbRuoloElettore != null : "fx:id=\"lbRuoloElettore\" was not injected: check your FXML file 'InserimentoVotoCategorico_Elettore.fxml'.";
	        assert lbTimer != null : "fx:id=\"lbTimer\" was not injected: check your FXML file 'InserimentoVotoCategorico_Elettore.fxml'.";
	        assert listCandidati != null : "fx:id=\"listCandidati\" was not injected: check your FXML file 'InserimentoVotoCategorico_Elettore.fxml'.";
	        assert listPartiti != null : "fx:id=\"listPartiti\" was not injected: check your FXML file 'InserimentoVotoCategorico_Elettore.fxml'.";
	        assert mainPane != null : "fx:id=\"mainPane\" was not injected: check your FXML file 'InserimentoVotoCategorico_Elettore.fxml'.";

	        if(elezione == null) {
	        	throw new IllegalStateException("Not expected elezione null");
	        }
	        controller = new InserimentoVotoCatController(elezione, this);
	        
	        if(elezione.getTipoElezione()==TipologiaElezione.VotazioneCategorica)
	        	addListHandlersCat();
	        else {
	        	addListHandlersCatPref();
	        	listCandidati.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
	        }
	        controller.populatePage();
	        
	    }
	    
	    private void addListHandlersCat() {
	    	listPartiti.getSelectionModel().selectedItemProperty().addListener(new ChangeListener<Partito>() {
	    	    @Override
	    	    public void changed(ObservableValue<? extends Partito> observable, Partito oldValue, Partito newValue) {
	    	    	listCandidati.getSelectionModel().clearSelection();
	    	    }
	    	});
	    	listCandidati.getSelectionModel().selectedItemProperty().addListener(new ChangeListener<Candidato>() {
	    	    @Override
	    	    public void changed(ObservableValue<? extends Candidato> observable, Candidato oldValue, Candidato newValue) {
	    	    	listPartiti.getSelectionModel().clearSelection();
	    	    }
	    	});
	    	
	    }
	    
	    private void addListHandlersCatPref() {
	    	listPartiti.getSelectionModel().selectedItemProperty().addListener(new ChangeListener<Partito>() {
	    	    @Override
	    	    public void changed(ObservableValue<? extends Partito> observable, Partito oldValue, Partito newValue) {
	    	    	try {
	    	    		controller.populateListCandidatiDelPartito(newValue);
	    	    		listCandidati.getSelectionModel().clearSelection();
	    	    	}catch(Exception e) {}
	    	    }
	    	});
	    	
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
		
		public void addPartitiToTable(ObservableList<Partito> data) {
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
			listPartiti.setItems(data);
		}
		
		public void addCandidatiToTable(ObservableList<Candidato> data) {
			listCandidati.getItems().clear();
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
			listCandidati.setItems(data);
		}
	
}
