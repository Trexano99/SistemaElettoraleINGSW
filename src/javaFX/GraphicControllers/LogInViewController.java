package javaFX.GraphicControllers;

import java.io.IOException;

import auditing.LogElement;
import auditing.LogHistory;
import controllers.LogInController;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleGroup;
import javafx.scene.input.MouseEvent;
import javafx.scene.paint.Color;
import javafx.stage.Stage;


/**
 * 
 * Questa classe è il controller della paginaAutenticazione.fxml 
 * e contiene le interazioni della stessa con gli elementi dell'MVC.
 * 
 * @author Shanti Ayala
 *
 */
public class LogInViewController{

	public final static String TITOLO = "Sistema Elettorale - LOGIN";
	public final static String RESOURCE = "/javaFx/GraphicElements/paginaAutenticazione.fxml";
	public final static int WIDTH = 600;
	public final static int HEIGTH = 500;
	
	
    @FXML
    private Button btnLogin;

    @FXML
    private RadioButton groupElettore;

    @FXML
    private RadioButton groupImpiegato;

    @FXML
    private Label lblMessage;
    
    @FXML
    private Label message1;//usato

    @FXML
    private Label message2;//usato

    @FXML
    private TextField lblName; //usato

    @FXML
    private TextField lblPassword; //usato

    @FXML
    private Label paramName; //usato

    @FXML
    private ToggleGroup typeUtente;
    
    @FXML
    void changeLabelUsername(MouseEvent event) {	
    		paramName.setText("Username: ");
    		lblName.setPromptText("Inserire username");
    		
    }
    @FXML
    void changeLabelCodicefiscale(MouseEvent event) {	
    		paramName.setText("Codice Fiscale: ");
    		lblName.setPromptText("Inserire codice fiscale");
    }
    
    void checkActivationLogin() {
    	if(!lblName.getText().isBlank() && !lblPassword.getText().isBlank())
    		btnLogin.setDisable(false);
    	else 
    		btnLogin.setDisable(true);
    }
    
    @FXML
    void handleLogin(ActionEvent event) {
    	
    	if(groupElettore.isSelected()) {

        	if(lblName.getText().length()!=16)
        		message1.setVisible(true);
        	else {
        		message1.setVisible(false);
        		if(LogInController.attemptElettoreLogin(lblName.getText(), lblPassword.getText(), this)) {
					try {
	        			 Stage stageTheEventSourceNodeBelongs = (Stage) ((Node)event.getSource()).getScene().getWindow();
	        			 Parent root = FXMLLoader.load(getClass().getResource(ElettoreMainViewController.RESOURCE));
						
	        			 stageTheEventSourceNodeBelongs.setTitle(ElettoreMainViewController.TITOLO);
	        			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, ElettoreMainViewController.WIDTH, ElettoreMainViewController.HEIGTH));
	        			 stageTheEventSourceNodeBelongs.show();
					} catch (IOException e) {
						LogHistory.getInstance().addLog(new LogElement(this, "handleLogin", "Fail changing scene", true));
					}
        		}
        	}
    	}
    	else {
    		message1.setVisible(false);
    		if(LogInController.attemptImpiegatoLogin(lblName.getText(), lblPassword.getText(), this)) {
    			try {
       			 Stage stageTheEventSourceNodeBelongs = (Stage) ((Node)event.getSource()).getScene().getWindow();
       			 Parent root = FXMLLoader.load(getClass().getResource(ImpiegatoMainViewController.RESOURCE));
					
       			 stageTheEventSourceNodeBelongs.setTitle(ImpiegatoMainViewController.TITOLO);
       			 stageTheEventSourceNodeBelongs.setScene(new Scene(root, ImpiegatoMainViewController.WIDTH, ImpiegatoMainViewController.HEIGTH));
       			 stageTheEventSourceNodeBelongs.show();
				} catch (IOException e) {
					LogHistory.getInstance().addLog(new LogElement(this, "handleLogin", "Fail changing scene", true));
				}
    		}
    	}

    }


    @FXML
    void initialize() {
        assert btnLogin != null : "fx:id=\"btnLogin\" was not injected: check your FXML file 'paginaAutenticazione.fxml'.";
        assert groupElettore != null : "fx:id=\"groupElettore\" was not injected: check your FXML file 'paginaAutenticazione.fxml'.";
        assert groupImpiegato != null : "fx:id=\"groupImpiegato\" was not injected: check your FXML file 'paginaAutenticazione.fxml'.";
        assert lblMessage != null : "fx:id=\"lblMessage\" was not injected: check your FXML file 'paginaAutenticazione.fxml'.";
        assert lblName != null : "fx:id=\"lblName\" was not injected: check your FXML file 'paginaAutenticazione.fxml'.";
        assert lblPassword != null : "fx:id=\"lblPassword\" was not injected: check your FXML file 'paginaAutenticazione.fxml'.";
        assert paramName != null : "fx:id=\"paramName\" was not injected: check your FXML file 'paginaAutenticazione.fxml'.";
        assert typeUtente != null : "fx:id=\"typeUtente\" was not injected: check your FXML file 'paginaAutenticazione.fxml'.";
        lblName.textProperty().addListener((observable, oldValue, newValue) -> {
            checkActivationLogin();
        });
        lblPassword.textProperty().addListener((observable, oldValue, newValue) -> {
            checkActivationLogin();
        });

    }
	
	public void denyLogin() {
		
		lblMessage.setText("Credenziali errate, riprovare");
		lblMessage.setTextFill(Color.rgb(210, 39, 30));
        
	}
	
	public void signalError(String errorName, String errorDetails) {
		
		System.out.println(errorName + " : " + errorDetails);
	}
	
}