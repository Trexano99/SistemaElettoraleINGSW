package javaFX.GraphicControllers;

import controllers.LogInController;
import javafx.fxml.FXML;

import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleGroup;
import javafx.scene.input.MouseEvent;
import javafx.scene.paint.Color;


/**
 * 
 * Questa classe è il controller della paginaAutenticazione.fxml 
 * e contiene le interazioni della stessa con gli elementi dell'MVC.
 * 
 * @author Shanti Ayala
 *
 */
public class LogInViewController{

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
    void handleLogin(MouseEvent event) {
    	
    	if(groupElettore.isSelected()) {

        	if(lblName.getText().length()!=16)
        		message1.setVisible(true);
        	else {
        		message1.setVisible(false);
        		LogInController.attemptElettoreLogin(lblName.getText(), lblPassword.getText(), this);
        	}
    	}
    	else {
    		message1.setVisible(false);
    		LogInController.attemptImpiegatoLogin(lblName.getText(), lblPassword.getText(), this);
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
    
    
    public void confirmLogin() {
		
    	lblMessage.setText("Benvenuto!");
		lblMessage.setTextFill(Color.rgb(21, 117, 84));
    	
		System.out.println("LOGIN DONE");
	}
	
	public void denyLogin() {
		
		lblMessage.setText("Credenziali errate, riprovare");
		lblMessage.setTextFill(Color.rgb(210, 39, 30));
        
		System.out.println("LOGIN FAILED");
	}
	
	public void signalError(String errorName, String errorDetails) {
		
		System.out.println(errorName + " : " + errorDetails);
	}
	
}