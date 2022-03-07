package javaFX.GraphicControllers;

import java.util.Timer;

import auditing.LogElement;
import auditing.LogHistory;
import controllers.InserimentoVotoReferendumController;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.ResourceBundle;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.SplitPane;
import javafx.scene.control.ToggleGroup;
import javafx.stage.Modality;
import javafx.stage.Stage;
import observer.timer.ITimerObserver;
import observer.timer.TimerTicker;
import useObject.voteElements.Referendum;

public class InserimentoRefVoteViewController implements ITimerObserver, IBaseVoteView {

	private InserimentoVotoReferendumController controller;
	
	public static Referendum referendum;
	
	public final static String TITOLO = "Sistema Elettorale - Inserimento Voto Referendum";
	public final static String RESOURCE = "/javaFx/GraphicElements/InserimentoVotoReferendum_Elettore.fxml";
	public final static int WIDTH = 600;
	public final static int HEIGTH = 500;
	
	
	  @FXML
	    private ResourceBundle resources;

	    @FXML
	    private SplitPane mainPane;
	  
	    @FXML
	    private URL location;

	    @FXML
	    private Button btnAnnulla;

	    @FXML
	    private Button btnInvia;

	    @FXML
	    private Button btnReset;

	    @FXML
	    private RadioButton btnsceltaRefNo;

	    @FXML
	    private RadioButton btnsceltaRefYes;

	    @FXML
	    private Label lbNomeElettore;

	    @FXML
	    private Label lbProposta;

	    @FXML
	    private Label lbRuoloElettore;

	    @FXML
	    private Label lbTimer;

	    @FXML
	    private ToggleGroup scelta;

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
	    	if(btnsceltaRefYes.isSelected() || btnsceltaRefNo.isSelected()) {
	    		if(btnsceltaRefYes.isSelected())
	    			controller.askConfirmation(true);
	    		else if(btnsceltaRefNo.isSelected())
	    			controller.askConfirmation(false);
	    	}else
	    		controller.askConfirmation(null);
	    	
	    }

	    @FXML
	    void initialize() {
	        assert btnAnnulla != null : "fx:id=\"btnAnnulla\" was not injected: check your FXML file 'InserimentoVotoReferendum_Elettore.fxml'.";
	        assert btnInvia != null : "fx:id=\"btnInvia\" was not injected: check your FXML file 'InserimentoVotoReferendum_Elettore.fxml'.";
	        assert btnReset != null : "fx:id=\"btnReset\" was not injected: check your FXML file 'InserimentoVotoReferendum_Elettore.fxml'.";
	        assert btnsceltaRefNo != null : "fx:id=\"btnsceltaRefNo\" was not injected: check your FXML file 'InserimentoVotoReferendum_Elettore.fxml'.";
	        assert btnsceltaRefYes != null : "fx:id=\"btnsceltaRefYes\" was not injected: check your FXML file 'InserimentoVotoReferendum_Elettore.fxml'.";
	        assert lbNomeElettore != null : "fx:id=\"lbNomeElettore\" was not injected: check your FXML file 'InserimentoVotoReferendum_Elettore.fxml'.";
	        assert lbProposta != null : "fx:id=\"lbProposta\" was not injected: check your FXML file 'InserimentoVotoReferendum_Elettore.fxml'.";
	        assert lbRuoloElettore != null : "fx:id=\"lbRuoloElettore\" was not injected: check your FXML file 'InserimentoVotoReferendum_Elettore.fxml'.";
	        assert lbTimer != null : "fx:id=\"lbTimer\" was not injected: check your FXML file 'InserimentoVotoReferendum_Elettore.fxml'.";
	        assert scelta != null : "fx:id=\"scelta\" was not injected: check your FXML file 'InserimentoVotoReferendum_Elettore.fxml'.";

	        if(referendum == null) {
	        	throw new IllegalStateException("Not expected referendum null");
	        }
	        
	        controller = new InserimentoVotoReferendumController(referendum, this);
	        
	        controller.populatePage();
	    }

		
	    
	    public void initializeDomandaReferendum(String domandaRef) {
	    	lbProposta.setText(domandaRef);
	    }
	    
	    public void initializeTimer() {
	    	List<ITimerObserver> lista = new ArrayList<ITimerObserver>();
		    lista.add(this);
		    TimerTicker.createTimer(60*10, lista);
	    }
	    
	    public void setHeaderContent(String nominativoElettore, String ruoloElettore) {
	    	lbNomeElettore.setText(nominativoElettore);
	    	lbRuoloElettore.setText("Ruolo utente: "+ruoloElettore);
	    }
	    
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
	    
}
