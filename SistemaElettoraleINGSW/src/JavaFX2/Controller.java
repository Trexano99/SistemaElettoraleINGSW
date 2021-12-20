package JavaFX2;

import javafx.application.Application;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleGroup;
import javafx.stage.Stage;

public class Controller extends Application{

    @FXML
    private Button btnLogin;

    @FXML
    private Label lblMessage;

    @FXML
    private TextField lblName;

    @FXML
    private TextField lblPassword;

    @FXML
    private Label paramName;

    @FXML
    private ToggleGroup typeUtente;
    
    @FXML
    private RadioButton groupElettore; //forse da togliere

    @FXML
    private RadioButton groupImpiegato; //forse da togliere

    @FXML
    void handleLogin(ActionEvent event) {

    }

    @FXML
    void handleName(ActionEvent event) {
    	/*if (typeUtente = 'Elettore') {
    		paramName = 'CodiceFiscale: ';
    	}*/
    }

    @FXML
    void handlePassword(ActionEvent event) {

    }

	@Override
	public void start(Stage arg0) throws Exception {
		// TODO Auto-generated method stub
		
	}
    
}
