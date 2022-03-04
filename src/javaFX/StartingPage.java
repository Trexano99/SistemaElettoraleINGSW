package javaFX;

import java.sql.SQLException;

import daoModels.DBConnector;
import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;

/**
 * 
 * Questa classe racchiude il Main generico che permette l'inizializzazione
 * dell'interfaccia grafica e il suo avvio.
 * 
 * @author Massimiliano Visconti
 *
 */
public class StartingPage extends Application {

	@Override
	public void start(Stage primaryStage) throws SQLException {
		
		DBConnector.openConnection();
		
		try {
			Parent root = FXMLLoader.load(getClass().getResource("/javaFx/GraphicElements/paginaAutenticazione.fxml"));
			primaryStage.setTitle("Sistema Elettorale");
			primaryStage.setScene(new Scene(root, 600, 500));
			primaryStage.show();
		}catch(Exception e) {
	        e.printStackTrace();
	   }
	}

	public static void main(String[] args) {
		launch(args);
	}
}
