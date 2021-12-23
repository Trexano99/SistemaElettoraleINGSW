package autenticazione;
//fx:controller="autenticazione.Controller"
import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;

@SuppressWarnings("javadoc")
public class Main extends Application{
	
	@Override
	public void start(Stage primaryStage) throws Exception{
		try {Parent root = FXMLLoader.load(getClass().getResource("paginaAutenticazione.fxml"));
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