package javaFX.GraphicControllers;

import java.io.IOException;
import java.net.URL;
import java.util.List;
import java.util.Optional;
import java.util.ResourceBundle;

import auditing.LogElement;
import auditing.LogHistory;
import controllers.NuovaVotazioneController;
import daoModels.NewElezione;
import daoModels.NewReferendum;
import javafx.beans.binding.Bindings;
import javafx.collections.ObservableList;
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
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.control.RadioButton;
import javafx.scene.control.SelectionMode;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleGroup;
import javafx.stage.Modality;
import javafx.stage.Stage;
import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione;
import useObject.voteElements.Votazione.TipologiaElezione;

public class NuovaVotazioneViewController {

	public static Votazione toUpdate = null;

	private NuovaVotazioneController controller;
	
	public final static String TITOLO = "Sistema Elettorale - Inserimento Nuova Votazione";
	public final static String RESOURCE = "/javaFx/GraphicElements/InserimentoNuovaVotazione.fxml";
	public final static int WIDTH = 600;
	public final static int HEIGTH = 665;

    @FXML
    private ResourceBundle resources;

    @FXML
    private URL location;

    @FXML
    private Button btnAnnulla;

    @FXML
    private RadioButton btnElezione;

    @FXML
    private Button btnInserisci;

    @FXML
    private RadioButton btnNo;

    @FXML
    private RadioButton btnReferendum;

    @FXML
    private RadioButton btnSi;

    @FXML
    private ToggleGroup calcoloVincitore;

    @FXML
    private Label lbNomeElettore;

    @FXML
    private Label lbRuoloElettore;

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
    private ToggleGroup modVoto;

    @FXML
    private ToggleGroup quorum;

    @FXML
    private ToggleGroup tipologia;

    @FXML
    private TextField txtQuesito;//QUESTO
    
    @FXML
    private TextField txtNomeVotazione;
    
    @FXML
    private Button btn_aggiungiCAScelti;

    @FXML
    private Button btn_aggiungiPAScelti;

    @FXML
    private Button btn_rimuoviCDaScelti;

    @FXML
    private Button btn_rimuoviPDaScelti;
    
    @FXML
    private RadioButton rbCategorico;

    @FXML
    private RadioButton rbCategoricoConPref;

    @FXML
    private RadioButton rbMaggioranza;

    @FXML
    private RadioButton rbMaggioranzaAbs;

    @FXML
    private RadioButton rbOrdinale;

    @FXML
    void onActionAnnulla(ActionEvent event) {
    	getPreviousPage();
    }


    @FXML
    void onActionInserisci(ActionEvent event) {
    	if(txtNomeVotazione.getText().isEmpty())
    		segnalaErrore("Dati non completi","Inserire il nome della votazione");
    	else if(btnElezione.isSelected()) {
	    	List<Partito> partiti = listPartitiScelti.getItems();
	    	List<Candidato>candidati = listCandidatiScelti.getItems();
	    	TipologiaElezione tipologia ;
	    	if(rbCategorico.isSelected())
	    		tipologia = TipologiaElezione.VotazioneCategorica;
	    	else if(rbCategoricoConPref.isSelected())
	    		tipologia = TipologiaElezione.VotazioneCategoricaConPref;
	    	else
	    		tipologia = TipologiaElezione.VotazioneOrdinale;
	    	NewElezione newElez = new NewElezione(
	    			txtNomeVotazione.getText(),
	    			true,
	    			false, 
	    			rbMaggioranzaAbs.isSelected(),
	    			tipologia,
	    			candidati,
	    			partiti);
	    	controller.askConfirmation(newElez);
    	}else {
    		if(txtQuesito.getText().isEmpty())
        		segnalaErrore("Dati non completi","Inserire la richiesta del referendum");
    		else {
	    		NewReferendum newRefer = new NewReferendum(txtNomeVotazione.getText(),
		    			true,
		    			false, 
		    			btnSi.isSelected(),
		    			txtQuesito.getText());
		    	controller.askConfirmation(newRefer);
    		}
    	}
    	
    }


	@FXML
    void onActionElezione(ActionEvent event) {
		modVoto.getToggles().forEach(toggle -> {
    	    Node node = (Node) toggle ;
    	    node.setDisable(false);
    	});
    	calcoloVincitore.getToggles().forEach(toggle -> {
    	    Node node = (Node) toggle ;
    	    node.setDisable(false);
    	});
    	quorum.getToggles().forEach(toggle -> {
    	    Node node = (Node) toggle ;
    	    node.setDisable(true);
    	});
    	txtQuesito.setDisable(true);
    	listPartiti.setDisable(false);
    	listCandidati.setDisable(false);
    	listPartitiScelti.setDisable(false);
    	listCandidatiScelti.setDisable(false);
    }

    @FXML
    void onActionReferendum(ActionEvent event) {
    	modVoto.getToggles().forEach(toggle -> {
    	    Node node = (Node) toggle ;
    	    node.setDisable(true);
    	});
    	calcoloVincitore.getToggles().forEach(toggle -> {
    	    Node node = (Node) toggle ;
    	    node.setDisable(true);
    	});
    	quorum.getToggles().forEach(toggle -> {
    	    Node node = (Node) toggle ;
    	    node.setDisable(false);
    	});
    	txtQuesito.setDisable(false);
    	listPartiti.setDisable(true);
    	listCandidati.setDisable(true);
    	listPartitiScelti.setDisable(true);
    	listCandidatiScelti.setDisable(true);
    }

    @FXML
    void addCandidatiAScelti(ActionEvent event) {
    	if(!listCandidati.getSelectionModel().getSelectedItems().isEmpty()) {
	    	List<Candidato> selectedItems = listCandidati.getSelectionModel().getSelectedItems();
	    	listCandidatiScelti.getItems().addAll(selectedItems);
	    	listCandidati.getItems().removeAll(selectedItems);
    	}
    }
    @FXML
    void addPartitiAScelti(ActionEvent event) {
    	if(!listPartiti.getSelectionModel().getSelectedItems().isEmpty()) {
	    	List<Partito> selectedItems = listPartiti.getSelectionModel().getSelectedItems();
	    	listPartitiScelti.getItems().addAll(selectedItems);
	    	listPartiti.getItems().removeAll(selectedItems);
    	}
    }
    
    @FXML
    void removeCandidatiDaScelti(ActionEvent event) {
    	if(!listCandidatiScelti.getSelectionModel().getSelectedItems().isEmpty()) {
	    	List<Candidato> selectedItems = listCandidatiScelti.getSelectionModel().getSelectedItems();
	    	listCandidati.getItems().addAll(selectedItems);
	    	listCandidatiScelti.getItems().removeAll(selectedItems);
    	}
    }
    @FXML
    void removePartitiDaScelti(ActionEvent event) {
    	if(!listPartitiScelti.getSelectionModel().getSelectedItems().isEmpty()) {
	    	List<Partito> selectedItems = listPartitiScelti.getSelectionModel().getSelectedItems();
	    	listPartiti.getItems().addAll(selectedItems);
	    	listPartitiScelti.getItems().removeAll(selectedItems);
    	}
    }

    @FXML
    void initialize() {
        assert btnAnnulla != null : "fx:id=\"btnAnnulla\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert btnElezione != null : "fx:id=\"btnElezione\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert btnInserisci != null : "fx:id=\"btnInserisci\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert btnNo != null : "fx:id=\"btnNo\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert btnReferendum != null : "fx:id=\"btnReferendum\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert btnSi != null : "fx:id=\"btnSi\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert calcoloVincitore != null : "fx:id=\"calcoloVincitore\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert lbNomeElettore != null : "fx:id=\"lbNomeElettore\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert lbRuoloElettore != null : "fx:id=\"lbRuoloElettore\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert listCandidati != null : "fx:id=\"listCandidati\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert listCandidatiScelti != null : "fx:id=\"listCandidatiScelti\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert listPartiti != null : "fx:id=\"listPartiti\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert listPartitiScelti != null : "fx:id=\"listPartitiScelti\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert mainPane != null : "fx:id=\"mainPane\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert modVoto != null : "fx:id=\"modVoto\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert quorum != null : "fx:id=\"quorum\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert tipologia != null : "fx:id=\"tipologia\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";
        assert txtQuesito != null : "fx:id=\"txtQuesito\" was not injected: check your FXML file 'InserimentoElezEReferendum_SHA.fxml'.";

        listCandidati.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
        listPartiti.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
        listCandidatiScelti.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
        listPartitiScelti.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
        
        setCellsFactory();
        
        controller = new NuovaVotazioneController(this, toUpdate);
        
        btn_aggiungiPAScelti.disableProperty().bind(Bindings.isEmpty(listPartiti.getSelectionModel().getSelectedItems()));
        btn_aggiungiCAScelti.disableProperty().bind(Bindings.isEmpty(listCandidati.getSelectionModel().getSelectedItems()));
        btn_rimuoviPDaScelti.disableProperty().bind(Bindings.isEmpty(listPartitiScelti.getSelectionModel().getSelectedItems()));
        btn_rimuoviCDaScelti.disableProperty().bind(Bindings.isEmpty(listCandidatiScelti.getSelectionModel().getSelectedItems()));
    
        onActionElezione(null);
        
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
			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, ImpiegatoMainViewController.WIDTH, ImpiegatoMainViewController.HEIGTH));
			 stageTheEventSourceNodeBelongs.show();
		} catch (IOException e) {
			LogHistory.getInstance().addLog(new LogElement(this, "getPreviousPage", "Fail changing scene", true));
		}
		
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
	
	public void addCandidatiToTable(ObservableList<Candidato> candidatiList) {
		listCandidati.setItems(candidatiList);
		
	}

	public void addPartitiToTable(ObservableList<Partito> partitiList) {
		listPartiti.setItems(partitiList);
		
	}
	public void addCandidatiSceltiToTable(ObservableList<Candidato> candidatiList) {
		listCandidatiScelti.setItems(candidatiList);
		
	}

	public void addPartitiSceltiToTable(ObservableList<Partito> partitiList) {
		listPartitiScelti.setItems(partitiList);
		
	}
	
	public void PopulateAllWithDati(Votazione votazione) {
		btnElezione.setDisable(true);
		btnReferendum.setDisable(true);
		txtNomeVotazione.setText(votazione.getNome());
		switch (votazione.getTipoElezione()) {
		case Referendum:
			btnReferendum.setSelected(true);
			onActionReferendum(null);
			Referendum ref = (Referendum)votazione;
			txtQuesito.setText(ref.getQuesito());
			btnSi.setSelected(ref.withQuorum());;
			btnNo.setSelected(!ref.withQuorum());
			break;
		default:
			btnElezione.setSelected(true);
			onActionElezione(null);
			Elezione elez = (Elezione) votazione;
			rbMaggioranza.setSelected(!elez.getMaggioranzaAssoluta());
			rbMaggioranzaAbs.setSelected(elez.getMaggioranzaAssoluta());
			if(elez.getTipoElezione()==TipologiaElezione.VotazioneCategorica)
				rbCategorico.setSelected(true);
			else if(elez.getTipoElezione()==TipologiaElezione.VotazioneCategoricaConPref)
				rbCategoricoConPref.setSelected(true);
			break;
		}
	}
	
}
