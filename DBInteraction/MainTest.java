import java.sql.SQLException;
import java.text.ParseException;

import Controllers.LogInController;
import SEModels.DBConnector;
import ViewElements.LogInView;
public class MainTest {

	public static void main(String[] args) throws ParseException, SQLException {
		// TODO Auto-generated method stub

		DBConnector.openConnection();
		
		LogInView view = new LogInView();
		
		LogInController controller = new LogInController();
		
		controller.attemptElettoreLogin("VSCMSM", "ciao", view);
		
		//ElettoreMapper.addNewElettore("VSCMSM", "Massimiliano", "Visconti", new java.sql.Date(df.parse("02-04-2015").getTime()), "ciao");
	}
	
}
