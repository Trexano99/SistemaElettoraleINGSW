package javaFX.GraphicControllers;

import java.io.IOException;
import java.net.URL;
import java.util.Optional;
import java.util.ResourceBundle;

import auditing.LogElement;
import auditing.LogHistory;
import controllers.ImpiegatoMainController;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonType;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.input.MouseButton;
import javafx.scene.input.MouseEvent;
import javafx.stage.Modality;
import javafx.stage.Stage;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione;

public class ImpiegatoMainViewController {
	
	private ImpiegatoMainController controller;
	
	public final static String TITOLO = "Sistema Elettorale - Consulto Votazioni Impiegato";
	public final static String RESOURCE = "/javaFx/GraphicElements/ConsultaElezioni_Impiegato.fxml";
	public final static int WIDTH = 600;
	public final static int HEIGTH = 500;
	
	@FXML
    private ResourceBundle resources;

    @FXML
    private URL location;

    @FXML
    private Button btnInserisciVotazione;

    @FXML
    private Button btnLogout;

    @FXML
    private TableColumn<Votazione, String> colNomeV;

    @FXML
    private TableColumn<Votazione, String> colTipoV;

    @FXML
    private TableColumn<Votazione, String> colVAperta;

    @FXML
    private TableColumn<Votazione, String> colVTerminata;

    @FXML
    private Label lbNomeElettore;

    @FXML
    private Label lbRuoloElettore;

    @FXML
    private SplitPane mainPane;

    @FXML
    private TableView<Votazione> tb_tabellaElezioni;

    @FXML
    void btnLogoutClicked(ActionEvent event) {
    	if(chiediConferma("LOGOUT","Si vuole lasciare la sessione?"))
    	try {
			 Stage stageTheEventSourceNodeBelongs = (Stage) ((Node)event.getSource()).getScene().getWindow();
			 Parent root = FXMLLoader.load(getClass().getResource(LogInViewController.RESOURCE));
			
			 stageTheEventSourceNodeBelongs.setTitle(LogInViewController.TITOLO);
			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, LogInViewController.WIDTH, LogInViewController.HEIGTH));
			 stageTheEventSourceNodeBelongs.show();
		} catch (IOException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "btnLogoutClicked", "Fail changing scene", true));
		}
    }

    @FXML
    void inserisciVotazione_click(ActionEvent event) {
    	NuovaVotazioneViewController.toUpdate = null;
    	try {
			 Stage stageTheEventSourceNodeBelongs = (Stage) ((Node)event.getSource()).getScene().getWindow();
			 Parent root = FXMLLoader.load(getClass().getResource(NuovaVotazioneViewController.RESOURCE));
			
			 stageTheEventSourceNodeBelongs.setTitle(NuovaVotazioneViewController.TITOLO);
			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, NuovaVotazioneViewController.WIDTH, NuovaVotazioneViewController.HEIGTH));
			 stageTheEventSourceNodeBelongs.show();
		} catch (IOException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "btnLogoutClicked", "Fail changing scene", true));
		} 
    }


    ContextMenu cm = new ContextMenu();
    
    @FXML
    void initialize() {
        assert btnInserisciVotazione != null : "fx:id=\"btnInserisciVotazione\" was not injected: check your FXML file 'ConsultaElezioni_Impiegato.fxml'.";
        assert btnLogout != null : "fx:id=\"btnLogout\" was not injected: check your FXML file 'ConsultaElezioni_Impiegato.fxml'.";
        assert colNomeV != null : "fx:id=\"colNomeV\" was not injected: check your FXML file 'ConsultaElezioni_Impiegato.fxml'.";
        assert colTipoV != null : "fx:id=\"colTipoV\" was not injected: check your FXML file 'ConsultaElezioni_Impiegato.fxml'.";
        assert colVAperta != null : "fx:id=\"colVAperta\" was not injected: check your FXML file 'ConsultaElezioni_Impiegato.fxml'.";
        assert colVTerminata != null : "fx:id=\"colVTerminata\" was not injected: check your FXML file 'ConsultaElezioni_Impiegato.fxml'.";
        assert lbNomeElettore != null : "fx:id=\"lbNomeElettore\" was not injected: check your FXML file 'ConsultaElezioni_Impiegato.fxml'.";
        assert lbRuoloElettore != null : "fx:id=\"lbRuoloElettore\" was not injected: check your FXML file 'ConsultaElezioni_Impiegato.fxml'.";
        assert mainPane != null : "fx:id=\"mainPane\" was not injected: check your FXML file 'ConsultaElezioni_Impiegato.fxml'.";
        assert tb_tabellaElezioni != null : "fx:id=\"tb_tabellaElezioni\" was not injected: check your FXML file 'ConsultaElezioni_Impiegato.fxml'.";

        controller = new ImpiegatoMainController(this);
        
        colNomeV.setCellValueFactory(
        		new PropertyValueFactory<>("nome"));
        colTipoV.setCellValueFactory(
        		new PropertyValueFactory<>("tipoElezioneStr"));
        colVAperta.setCellValueFactory(
        		new PropertyValueFactory<>("isClosedStr"));
        colVTerminata.setCellValueFactory(
        		new PropertyValueFactory<>("isFinishedStr"));
        
        tb_tabellaElezioni.addEventHandler(MouseEvent.MOUSE_CLICKED, new EventHandler<MouseEvent>() {

            @Override
            public void handle(MouseEvent t) {
            	if ((t.getButton() == MouseButton.SECONDARY || t.getButton() == MouseButton.PRIMARY)&& cm.isShowing())
            		cm.hide();
                if(t.getButton() == MouseButton.SECONDARY && 
                		tb_tabellaElezioni.getSelectionModel().getSelectedItem()!=null) {
                	generateAppropriateCM(tb_tabellaElezioni.getSelectionModel().getSelectedItem());
                	cm.show(tb_tabellaElezioni, t.getScreenX(), t.getScreenY());
                }
            }
        }); 
        
        controller.populatePage();	
    }
    

    
    private void generateAppropriateCM (Votazione v) {
        cm = new ContextMenu();
        
        if(v.isClosed()||v.isFinished()) {
	        MenuItem mi1 = new MenuItem("Elimina Votazione");
	        mi1.setOnAction( e -> {
	            controller.eraseElezione((Votazione)tb_tabellaElezioni.getSelectionModel().getSelectedItem());
	        });
	        cm.getItems().add(mi1);
        }
        if(v.isClosed()&&!v.isFinished()) {
	        MenuItem mi2 = new MenuItem("Apri Votazione");
	        mi2.setOnAction( e -> {
	        	controller.openVotation((Votazione)tb_tabellaElezioni.getSelectionModel().getSelectedItem());
	        });
	        cm.getItems().add(mi2);
        }
        if(!v.isClosed()) {
	        MenuItem mi3 = new MenuItem("Chiudi Votazione");
	        mi3.setOnAction( e -> {
	            controller.closeVotation((Votazione)tb_tabellaElezioni.getSelectionModel().getSelectedItem());
	        });
	        cm.getItems().add(mi3);
        }
        if(v.isClosed()&&v.isFinished()) {
	        MenuItem mi4 = new MenuItem("Esito Votazione");
	        mi4.setOnAction( e -> {
	        	Votazione vote = (Votazione)tb_tabellaElezioni.getSelectionModel().getSelectedItem();
	        	if(vote.getClass() == Elezione.class) {
	    			Elezione elezione = (Elezione)vote;
	    			try {
	    				 EsitoElezioneViewController.elezione = elezione;
			   			 Stage stageTheEventSourceNodeBelongs = (Stage) (mainPane.getScene().getWindow());
			   			 Parent root = FXMLLoader.load(getClass().getResource(EsitoElezioneViewController.RESOURCE));
			   			
			   			 stageTheEventSourceNodeBelongs.setTitle(EsitoElezioneViewController.TITOLO);
			   			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, EsitoElezioneViewController.WIDTH, EsitoElezioneViewController.HEIGTH));
			   			 stageTheEventSourceNodeBelongs.show();
			   		} catch (IOException excep) {
			   			LogHistory.getInstance().addLog(new LogElement(this, "generateAppropriateCM", "Fail changing scene", true));
			   		} 
	    		}else {
	    			Referendum referendum = (Referendum)vote;
	    			try {
	    				 EsitoReferendumViewController.referendum = referendum;
			   			 Stage stageTheEventSourceNodeBelongs = (Stage) (mainPane.getScene().getWindow());
			   			 Parent root = FXMLLoader.load(getClass().getResource(EsitoReferendumViewController.RESOURCE));
			   			
			   			 stageTheEventSourceNodeBelongs.setTitle(EsitoReferendumViewController.TITOLO);
			   			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, EsitoReferendumViewController.WIDTH, EsitoReferendumViewController.HEIGTH));
			   			 stageTheEventSourceNodeBelongs.show();
			   		} catch (IOException excep) {
			   			LogHistory.getInstance().addLog(new LogElement(this, "generateAppropriateCM", "Fail changing scene", true));
			   		} 
	    		}
	        });
	        cm.getItems().add(mi4);
        }

        if(v.isClosed()&&!v.isFinished()) {
        	MenuItem mi5 = new MenuItem("Modifica Votazione");
	        mi5.setOnAction( e -> {
	        	Votazione vote = ((Votazione)tb_tabellaElezioni.getSelectionModel().getSelectedItem());
	        	NuovaVotazioneViewController.toUpdate = vote;
	        	try {
		   			 Stage stageTheEventSourceNodeBelongs = (Stage) (mainPane.getScene().getWindow());
		   			 Parent root = FXMLLoader.load(getClass().getResource(NuovaVotazioneViewController.RESOURCE));
		   			
		   			 stageTheEventSourceNodeBelongs.setTitle(NuovaVotazioneViewController.TITOLO);
		   			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, NuovaVotazioneViewController.WIDTH, NuovaVotazioneViewController.HEIGTH));
		   			 stageTheEventSourceNodeBelongs.show();
		   		} catch (IOException excep) {
		   			LogHistory.getInstance().addLog(new LogElement(this, "generateAppropriateCM", "Fail changing scene", true));
		   		} 
	        });
	        cm.getItems().add(mi5);
        }
        
    }
    
    public void setHeaderContent(String nominativoElettore, String ruoloElettore) {
    	lbNomeElettore.setText(nominativoElettore);
    	lbRuoloElettore.setText("Ruolo utente: "+ruoloElettore);
    }
    
    public void addToTable(ObservableList<Votazione> votazioni) {
        tb_tabellaElezioni.setItems(votazioni);
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


}
