package JavaFX;

import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.layout.StackPane;
import javafx.stage.Stage;


public class helloWordFX extends Application{
	
	@Override
	public void start(Stage primaryStage) {
		String javaVersion = System.getProperty("java.version");
		String javafxVersion = System.getProperty("javafx.version");
		Label l = new Label("Hello, JavaFX" + javafxVersion + ",\running on Java "+ javaVersion + ".");
		
		Scene scene = new Scene(new StackPane(l), 400, 300);
		primaryStage.setTitle("Hello Word");
		primaryStage.setScene(scene);
		primaryStage.show();
	}
	

	public static void main(String[] args) {
		launch(args);
	}
}

