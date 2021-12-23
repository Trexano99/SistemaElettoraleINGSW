package autenticazione;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;

import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleGroup;
import javafx.scene.input.MouseEvent;
import javafx.scene.paint.Color;

@SuppressWarnings("javadoc")
public class Controller{

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

    @FXML
    void handleLogin(MouseEvent event) {
    	String name = lblName.getText(); //da passare al db
    	String password = lblPassword.getText(); //da passare al db
    	System.out.println(name);
    	if(!name.equals("da quello preso dal db")) {
    		message1.setText("Your credential is incorrect!");
    		message1.setVisible(true);
            message1.setTextFill(Color.rgb(210, 39, 30));
    	}
    	if(!password.equals("da quello preso dal db")) {	
    		message2.setVisible(true);
    		message2.setText("Your password is incorrect!");
            message2.setTextFill(Color.rgb(210, 39, 30));
    	}
    	//se tutto va bene login ok 
    	lblMessage.setText("valori inseriti: "+ name +" "+ password);//questo è da togliere
    }

    @FXML
    void handleName(ActionEvent event) {
    	
    }

    @FXML
    void handlePassword(ActionEvent event) {

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

    }
	
}
