package JavaFX2;

import java.io.IOException;

import javafx.application.Application;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.control.ToggleGroup;
import javafx.scene.layout.StackPane;
import javafx.stage.Stage;

public class AutenticationFX extends Application{

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
    void handleLogin(ActionEvent event) {

    }

    @FXML
    void handleName(ActionEvent event) {

    }

    @FXML
    void handlePassword(ActionEvent event) {

    }
    
    @Override
	public void start(Stage primaryStage) throws Exception {
    	Parent root = FXMLLoader.load(getClass().getResource("paginaAutenticazione.fxml"));
		
		Scene scene = new Scene(root, 400, 300);
		primaryStage.setTitle("Sistema Elettorale");
		primaryStage.setScene(scene);
		primaryStage.show();
	}
	

	public static void main(String[] args) {
		launch(args);
	}

}
