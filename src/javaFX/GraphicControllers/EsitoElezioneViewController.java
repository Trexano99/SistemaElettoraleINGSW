package javaFX.GraphicControllers;

import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;

import auditing.LogElement;
import auditing.LogHistory;
import controllers.EsitoElezioneController;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.stage.Stage;
import useObject.voteElements.Elezione;
import useObject.voteElements.results.EsitoElezione;
import useObject.voteElements.results.GenericVoto;

public class EsitoElezioneViewController {

	public static Elezione elezione;
	
	private EsitoElezioneController controller;
	
	public final static String TITOLO = "Sistema Elettorale - Esito voto Elezione";
	public final static String RESOURCE = "/javaFx/GraphicElements/ConsultaEsitoElezione.fxml";
	public final static int WIDTH = 600;
	public final static int HEIGTH = 554;
	
	@FXML
    private ResourceBundle resources;

    @FXML
    private URL location;

    @FXML
    private Label lbNomeElettore;

    @FXML
    private Label lbRuoloElettore;

    @FXML
    private Label lbl_NomeElezione;

    @FXML
    private Label lbl_votiBianchi;

    @FXML
    private Label lbl_votiTotali;

    @FXML
    private Label lbl_votoValido;

    @FXML
    private SplitPane mainPane;

    @FXML
    private TableColumn<GenericVoto, String> colVCNome;

    @FXML
    private TableColumn<GenericVoto, String> colVCVoti;

    @FXML
    private TableColumn<GenericVoto, String> colVPNome;

    @FXML
    private TableColumn<GenericVoto, String> colVPVoti;
    
    @FXML
    private TableView<GenericVoto> tb_votiCandidati;

    @FXML
    private TableView<GenericVoto> tb_votiPartiti;


    @FXML
    void btnBack(ActionEvent event) {
    	getPreviousPage();
    }

    @FXML
    void initialize() {
    	 assert colVCNome != null : "fx:id=\"colVCNome\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert colVCVoti != null : "fx:id=\"colVCVoti\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert colVPNome != null : "fx:id=\"colVPNome\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert colVPVoti != null : "fx:id=\"colVPVoti\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert lbNomeElettore != null : "fx:id=\"lbNomeElettore\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert lbRuoloElettore != null : "fx:id=\"lbRuoloElettore\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert lbl_NomeElezione != null : "fx:id=\"lbl_NomeElezione\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert lbl_votiBianchi != null : "fx:id=\"lbl_votiBianchi\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert lbl_votiTotali != null : "fx:id=\"lbl_votiTotali\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert lbl_votoValido != null : "fx:id=\"lbl_votoValido\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert mainPane != null : "fx:id=\"mainPane\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert tb_votiCandidati != null : "fx:id=\"tb_votiCandidati\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";
         assert tb_votiPartiti != null : "fx:id=\"tb_votiPartiti\" was not injected: check your FXML file 'ConsultaEsitoElezione.fxml'.";

         colVCNome.setCellValueFactory(
         		new PropertyValueFactory<>("nominativo"));
         colVCVoti.setCellValueFactory(
         		new PropertyValueFactory<>("numeroVoti"));
         colVPNome.setCellValueFactory(
          		new PropertyValueFactory<>("nominativo"));
          colVPVoti.setCellValueFactory(
          		new PropertyValueFactory<>("numeroVoti"));
         
         controller = new EsitoElezioneController(elezione, this);

         controller.populatePage();	
    }

    
	public void setHeaderContent(String nominativoElettore, String ruoloElettore) {
		lbNomeElettore.setText(nominativoElettore);
    	lbRuoloElettore.setText("Ruolo utente: "+ruoloElettore);
	}
    
    public void getPreviousPage() {
		try {
			 Stage stageTheEventSourceNodeBelongs = (Stage) (mainPane.getScene().getWindow());
			 Parent root = FXMLLoader.load(getClass().getResource(ImpiegatoMainViewController.RESOURCE));
			
			 stageTheEventSourceNodeBelongs.setTitle(ImpiegatoMainViewController.TITOLO);
			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, ImpiegatoMainViewController.WIDTH, ElettoreMainViewController.HEIGTH));
			 stageTheEventSourceNodeBelongs.show();
		} catch (IOException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "getPreviousPage", "Fail changing scene", true));
		}
		
	}
    
    public void addPartitiToTable(ObservableList<GenericVoto> data) {
    	tb_votiPartiti.setItems(data);
	}
	
	public void addCandidatiToTable(ObservableList<GenericVoto> data) {
		tb_votiCandidati.setItems(data);
	}
	public void popolaDati(EsitoElezione esito) {
    	lbl_NomeElezione.setText(elezione.getNome());
    	lbl_votiTotali.setText(String.valueOf(esito.getNumeroSchedeTotali()));
    	lbl_votiBianchi.setText(String.valueOf(esito.getNumeroSchedeBianche()));
    	if(esito.getIsValid())
    		lbl_votoValido.setText("SI");
    	else
    		lbl_votoValido.setText("NO");
    }
	
}
