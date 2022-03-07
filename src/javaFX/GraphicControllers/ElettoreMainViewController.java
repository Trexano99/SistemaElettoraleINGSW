package javaFX.GraphicControllers;

import java.io.IOException;
import java.lang.reflect.Array;
import java.net.URL;
import java.util.List;
import java.util.ResourceBundle;
import java.util.Timer;

import auditing.LogElement;
import auditing.LogHistory;
import controllers.ElettoreMainController;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.CustomMenuItem;
import javafx.scene.control.Label;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableRow;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.input.MouseButton;
import javafx.scene.input.MouseEvent;
import javafx.stage.Stage;
import javafx.util.Callback;
import observer.timer.ITimerObserver;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione;

public class ElettoreMainViewController {

	public final static String TITOLO = "Sistema Elettorale - Scelta Votazione Elettore";
	public final static String RESOURCE = "/javaFx/GraphicElements/SceltaElezione_Elettore.fxml";
	public final static int WIDTH = 600;
	public final static int HEIGTH = 500;
	
    @FXML
    private ResourceBundle resources;

    @FXML
    private URL location;

    @FXML
    private Button btnLogout;
    
    @FXML
    private SplitPane mainPane;

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
    private TableView<Votazione> tb_tabellaElezioni;

    @FXML
    void btnLogoutClicked(ActionEvent event) {

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
    void initialize() {
        assert btnLogout != null : "fx:id=\"btnLogout\" was not injected: check your FXML file 'SceltaElezione_Elettore - Copia.fxml'.";
        assert colNomeV != null : "fx:id=\"colNomeV\" was not injected: check your FXML file 'SceltaElezione_Elettore - Copia.fxml'.";
        assert colTipoV != null : "fx:id=\"colTipoV\" was not injected: check your FXML file 'SceltaElezione_Elettore - Copia.fxml'.";
        assert colVAperta != null : "fx:id=\"colVAperta\" was not injected: check your FXML file 'SceltaElezione_Elettore - Copia.fxml'.";
        assert colVTerminata != null : "fx:id=\"colVTerminata\" was not injected: check your FXML file 'SceltaElezione_Elettore - Copia.fxml'.";
        assert lbNomeElettore != null : "fx:id=\"lbNomeElettore\" was not injected: check your FXML file 'SceltaElezione_Elettore - Copia.fxml'.";
        assert tb_tabellaElezioni != null : "fx:id=\"tb_tabellaElezioni\" was not injected: check your FXML file 'SceltaElezione_Elettore - Copia.fxml'.";        
        
        ContextMenu cm = new ContextMenu();
        MenuItem mi1 = new MenuItem("Vota Elezione");
        mi1.setOnAction( e -> {
            ElettoreMainController.votaElezione(tb_tabellaElezioni.getSelectionModel().getSelectedItem() , this);
        });
        cm.getItems().add(mi1);

        tb_tabellaElezioni.addEventHandler(MouseEvent.MOUSE_CLICKED, new EventHandler<MouseEvent>() {

            @Override
            public void handle(MouseEvent t) {
            	if ((t.getButton() == MouseButton.SECONDARY || t.getButton() == MouseButton.PRIMARY)&& cm.isShowing())
            		cm.hide();
                if(t.getButton() == MouseButton.SECONDARY && 
                		tb_tabellaElezioni.getSelectionModel().getSelectedItem()!=null&&
                		tb_tabellaElezioni.getSelectionModel().getSelectedItem().isClosed()==false&&
                		tb_tabellaElezioni.getSelectionModel().getSelectedItem().getHasLoggedElettoreVotedFor()==false) {
                    cm.show(tb_tabellaElezioni, t.getScreenX(), t.getScreenY());
                }
            }
        });    

        ElettoreMainController.populatePage(this);	
        
    }
    
    
    public void setHeaderContent(String nominativoElettore, String ruoloElettore) {
    	lbNomeElettore.setText(nominativoElettore);
    	lbRuoloElettore.setText("Ruolo utente: "+ruoloElettore);
    }

    public void addToTable(ObservableList<Votazione> votazioni) {
        colNomeV.setCellValueFactory(
        		new PropertyValueFactory<>("nome"));
        colTipoV.setCellValueFactory(
        		new PropertyValueFactory<>("tipoElezioneStr"));
        colVAperta.setCellValueFactory(
        		new PropertyValueFactory<>("isClosedStr"));
        colVTerminata.setCellValueFactory(
        		new PropertyValueFactory<>("isFinishedStr"));
        tb_tabellaElezioni.setItems(votazioni);
    }

    
    public void showVotoOrdinale(Elezione elezione) {
       //FAI
    }
    
    public void showVotoCategorico(Elezione elezione) {
    	try {
			 Stage stageTheEventSourceNodeBelongs = (Stage) (mainPane.getScene().getWindow());			
			 InserimentoCatVoteViewController.elezione = elezione;
			 Parent root = FXMLLoader.load(getClass().getResource(InserimentoCatVoteViewController.RESOURCE));
			
			 stageTheEventSourceNodeBelongs.setTitle(InserimentoCatVoteViewController.TITOLO);
			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, InserimentoCatVoteViewController.WIDTH, InserimentoCatVoteViewController.HEIGTH));
			 
			 stageTheEventSourceNodeBelongs.show();
		} catch (IOException ex) {
			LogHistory.getInstance().addLog(new LogElement(this, "showVotoCategorico", "Fail changing scene", true));
		}
    }
    
    public void showReferendum(Referendum referendum) {			 
    	try {
			 Stage stageTheEventSourceNodeBelongs = (Stage) (mainPane.getScene().getWindow());			
			 InserimentoRefVoteViewController.referendum = referendum;
			 Parent root = FXMLLoader.load(getClass().getResource(InserimentoRefVoteViewController.RESOURCE));
			
			 stageTheEventSourceNodeBelongs.setTitle(InserimentoRefVoteViewController.TITOLO);
			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, InserimentoRefVoteViewController.WIDTH, InserimentoRefVoteViewController.HEIGTH));
			 
			 stageTheEventSourceNodeBelongs.show();
		} catch (IOException ex) {
			LogHistory.getInstance().addLog(new LogElement(this, "showReferendum", "Fail changing scene", true));
		}
    }
    
    
}