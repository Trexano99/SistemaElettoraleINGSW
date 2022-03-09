package javaFX;

import java.sql.SQLException;

import dBUtility.DBConnector;
import javaFX.GraphicControllers.LogInViewController;
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
			Parent root = FXMLLoader.load(getClass().getResource(LogInViewController.RESOURCE));
			primaryStage.setTitle(LogInViewController.TITOLO);
			primaryStage.setScene(new Scene(root, LogInViewController.WIDTH, LogInViewController.HEIGTH));
		    primaryStage.setResizable(false);
			primaryStage.show();
		}catch(Exception e) {
	        e.printStackTrace();
	   }
	}

	public static void main(String[] args) {
		launch(args);
	}
}
