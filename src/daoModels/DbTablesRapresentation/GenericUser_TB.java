package daoModels.DbTablesRapresentation;

/**
 * Utente generico per l'autenticazione al Database.
 * Può essere utilizzato sia per login di impiegati che elettori.
 * <p>
 * Questa classe è una pura rappresentazione dei parametri richiesti 
 * lato DB per l'autenticazione. Questa potrà poi essere espansa con 
 * altri metodi richiamabili per la gestione delle utenze lato DB.
 * 
 * @author Massimiliano Visconti
 *
 */
public class GenericUser_TB {

	private String username;
	private String password;
	
	public String getUsername() {
		return username;
	}
	public String getPassword() {
		return password;
	}
	
	/**
	 * Permette di crere una nuova istanza utente a partire dalle
	 * credenziali quali username e password
	 * @param username 	Nome utente
	 * @param password	Password utente
	 */
	public GenericUser_TB(String username, String password) {
		if(username.isBlank() || password.isBlank())
			throw new IllegalArgumentException("Fields cannot be blank or whiteSpaces");
		this.username = username;
		this.password = password;
	}
	
	
	
}
