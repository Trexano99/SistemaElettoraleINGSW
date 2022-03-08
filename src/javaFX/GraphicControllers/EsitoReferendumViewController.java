package javaFX.GraphicControllers;

import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;

import auditing.LogElement;
import auditing.LogHistory;
import controllers.EsitoReferendumController;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.SplitPane;
import javafx.stage.Stage;
import useObject.voteElements.Referendum;
import useObject.voteElements.results.EsitoReferendum;

public class EsitoReferendumViewController {
	
	public static Referendum referendum;
	
	private EsitoReferendumController controller;
	
	public final static String TITOLO = "Sistema Elettorale - Esito voto Referendum";
	public final static String RESOURCE = "/javaFx/GraphicElements/ConsultaEsitoReferendum.fxml";
	public final static int WIDTH = 600;
	public final static int HEIGTH = 454;
	
	@FXML
    private ResourceBundle resources;

    @FXML
    private URL location;

    @FXML
    private Button btnBack;

    @FXML
    private Label lbNomeElettore;

    @FXML
    private Label lbRuoloElettore;

    @FXML
    private Label lbl_nomeReferendum;

    @FXML
    private Label lbl_votiBianchi;

    @FXML
    private Label lbl_votiNegativi;

    @FXML
    private Label lbl_votiPositivi;

    @FXML
    private Label lbl_votiTotali;

    @FXML
    private Label lbl_votoValido;

    @FXML
    private SplitPane mainPane;

    @FXML
    void btnBack(ActionEvent event) {
    	getPreviousPage();
    }

    @FXML
    void initialize() {
        assert btnBack != null : "fx:id=\"btnBack\" was not injected: check your FXML file 'ConsultaEsitoReferendum.fxml'.";
        assert lbNomeElettore != null : "fx:id=\"lbNomeElettore\" was not injected: check your FXML file 'ConsultaEsitoReferendum.fxml'.";
        assert lbRuoloElettore != null : "fx:id=\"lbRuoloElettore\" was not injected: check your FXML file 'ConsultaEsitoReferendum.fxml'.";
        assert lbl_nomeReferendum != null : "fx:id=\"lbl_nomeReferendum\" was not injected: check your FXML file 'ConsultaEsitoReferendum.fxml'.";
        assert lbl_votiBianchi != null : "fx:id=\"lbl_votiBianchi\" was not injected: check your FXML file 'ConsultaEsitoReferendum.fxml'.";
        assert lbl_votiNegativi != null : "fx:id=\"lbl_votiNegativi\" was not injected: check your FXML file 'ConsultaEsitoReferendum.fxml'.";
        assert lbl_votiPositivi != null : "fx:id=\"lbl_votiPositivi\" was not injected: check your FXML file 'ConsultaEsitoReferendum.fxml'.";
        assert lbl_votiTotali != null : "fx:id=\"lbl_votiTotali\" was not injected: check your FXML file 'ConsultaEsitoReferendum.fxml'.";
        assert lbl_votoValido != null : "fx:id=\"lbl_votoValido\" was not injected: check your FXML file 'ConsultaEsitoReferendum.fxml'.";
        assert mainPane != null : "fx:id=\"mainPane\" was not injected: check your FXML file 'ConsultaEsitoReferendum.fxml'.";

        if(referendum == null) {
        	throw new IllegalStateException("Not expected referendum null");
        }
        
        controller = new EsitoReferendumController(referendum, this);
        
        controller.populatePage();
    }
    
    public void getPreviousPage() {
		try {
			 Stage stageTheEventSourceNodeBelongs = (Stage) (mainPane.getScene().getWindow());
			 Parent root = FXMLLoader.load(getClass().getResource(ImpiegatoMainViewController.RESOURCE));
			
			 stageTheEventSourceNodeBelongs.setTitle(ImpiegatoMainViewController.TITOLO);
			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, ImpiegatoMainViewController.WIDTH, ImpiegatoMainViewController.HEIGTH));
			 stageTheEventSourceNodeBelongs.show();
		} catch (IOException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "getPreviousPage", "Fail changing scene", true));
		}
		
	}
    
	public void setHeaderContent(String nominativoElettore, String ruoloElettore) {
		lbNomeElettore.setText(nominativoElettore);
    	lbRuoloElettore.setText("Ruolo utente: "+ruoloElettore);
	}
    
    public void popolaDati(EsitoReferendum esito) {
    	lbl_nomeReferendum.setText(referendum.getNome());
    	lbl_votiTotali.setText(String.valueOf(esito.getNumeroSchedeTotali()));
    	lbl_votiBianchi.setText(String.valueOf(esito.getNumeroSchedeBianche()));
    	lbl_votiPositivi.setText(String.valueOf(esito.getVotiPositivi()));
    	lbl_votiNegativi.setText(String.valueOf(esito.getVotiNegativi()));
    	if(esito.isValid())
    		lbl_votoValido.setText("SI");
    	else
    		lbl_votoValido.setText("NO");
    }

}
