package utenze;

/**
 * Questa classe astratta rappresenta un generico Utente.
 * Essa può essere utilizzata in qualsiasi classe che 
 * necessiti delle credenziali per l'autenticazione della 
 * figura che rappresenta. 
 * 
 * <p>  
 * Il costruttore rimane definito privato per garantire 
 * l'instanziabilità solo tramite la funzione 
 * {@link utenze.Utente#logIn(String, String)}.
 * 
 * 
 * @author Massimiliano Visconti
 *
 */
public class Utente {
	
	//Identificativo univoco dell'utente lato DB
	private int userId;
	private tipoUtente userType;
	
	private Utente (Integer userId) {
		this.userId = userId;
	}
	
	/**
	 * Permette di ottenere l'identificativo dell'utente 
	 * 
	 * @return identificativo dell'utente
	 */
	public int getUserId() {
		return userId;
	}
	
	/**
	 * Permette di controllare che l'utente sia di una determinata tipologia
	 * 
	 * @param type tipologia utente che si vuole controllare
	 * @return {@code true} se l'utente è del tipo indicato
	 */
	public boolean isTypeOfUser(tipoUtente type) {
		return userType == type;
	}
	
	/**
	 * Funzione statica che permette di instanziare un nuovo utente.
	 * 
	 * @param username nome dell'utente che deve effettuare il LogIn
	 * @param password password dell'utente che deve effettuare il LogIn
	 * @return {@code null} se la procedura non è andata a buon fine. L'utente altrimenti. 
	 */
	static public Utente logIn(String username, String password) {
		
		/*
		 * Query per richiedere l'autenticazione al Database.
		 * 
		 * Inserimento dell'identificativo ricevuto nella 
		 * variabile 'userId'.
		 * 
		 * Inserimento della tipologia di utente nella 
		 * variabile userType.
		 * 
		 * Return della risposta. 
		 * */
		
		return null;
	}
	
	/**
	 * Permette di ottenere quanti tentativi di LogIn rimangono ad un utente
	 * il cui username è passato come parametro.
	 * 
	 * @param username Username dell'utente del quale si vuole sapere il numero
	 * di possibili LogIn rimasti.
	 * @return numero di tentativi rimasti.
	 */
	static public int remainingLogInAttempts(String username) {
		
		/*
		 * Query per richiedere il numero di tentativi rimasti
		 * per eseguire il LogIn.
		 * 
		 * Return della risposta. 
		 * */
		
		return 3;
	}
	
	/**
	 * Enumeratore che elenca le tipologie di utenti possibili
	 */
	static public enum tipoUtente {
		/**
		 * Rappresenta la tipologia di Utente elettore, rifetito 
		 * alla classe esistente {@link utenze.Elettore}
		 */
		Elettore,
		/**
		 * Rappresenta la tipologia di Utente scrutatore, rifetito 
		 * alla classe esistente {@link utenze.Scrutatore}
		 */
		Scrutatore
	}
	
}
