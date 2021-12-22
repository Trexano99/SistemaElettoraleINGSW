package ViewElements;

public class LogInView {


	public LogInView() {
		//Inizializzazione componenti

		System.out.println("VIEW SETTED, AWAIT FOR CREDENTIALS");
	}
	
	public void confirmLogin() {
		
		System.out.println("LOGIN DONE");
	}
	
	public void denyLogin() {
		
		System.out.println("LOGIN FAILED");
	}
	
	public void signalError(String errorName, String errorDetails) {
		
		System.out.println(errorName + " : " + errorDetails);
	}
}
