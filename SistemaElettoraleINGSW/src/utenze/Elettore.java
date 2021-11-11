package utenze;

import utenze.Utente.tipoUtente;
import java.lang.*;

/**
 * Questa classe rappresenta un Elettore del sistema di voto.
 * 
 * @author Shanti Ayala
 *
 */
/*Definire una classe Elettore che contenga i seguenti attributi e metodi: 
• voto, un booleano che ha valore true nel caso in cui l’elettore abbia espresso il suo voto, false
nel caso in cui l’elettore non abbia ancora espresso il voto
• metodo esprimi_voto, di cui non è necessario dare l’implementazione completa (non mi 
interessa sapere cosa abbia votato l’elettore, ma che abbia votato. Serve solo per poter specificare 
alcune condizioni JML)*/
public final class Elettore {
	
	//caratteristiche
	private String nome, cognome, comune, nazione, sesso; 
	private int[] dataNascita = new int[3]; //len 3
	private char[] cf = new char[5]; 
	private Boolean voto; 
	
	//getter&setter
	public String getNome() {
		return nome;
	}


	public void setNome(String nome) {
		checkNome(nome); //nome non nullo
		this.nome = nome;
	}


	public String getCognome() {
		return cognome;
	}


	public void setCognome(String cognome) {
		checkCognome(cognome); //cogn non nullo 
		this.cognome = cognome;
	}


	public String getComune() {
		//checkComune(elettore);
		return comune;
	}


	public void setComune(String comune) {
		this.comune = comune;
	}


	public String getNazione() {
		return nazione;
	}


	public void setNazione(String nazione) {
		this.nazione = nazione;
	}


	public String getSesso() {
		return sesso;
	}


	public void setSesso(String sesso) {
		checkSesso(sesso); //sesso solo F o M
		this.sesso = sesso;
	}


	public int[] getDataNascita() {
		return dataNascita;
	}


	public void setDataNascita(int[] dataNascita) {
		checkEta(dataNascita); //maggiorenne
		this.dataNascita = dataNascita;
	}


	public char[] getCf() {
		return cf;
	}


	public void setCf(char[] cf) {
		this.cf = cf;
	}


	public Boolean getVoto() {
		return voto;
	}


	public void setVoto(Boolean voto) {
		hasAlreadyVoted(voto);
		this.voto = voto;
	}
	//JLM ------------------------------------------------------------------------------------------
	
		/**
		 * 
		 * @param 
		 * @return
		 */
		private boolean checkNome(String nome){
			if (nome == null)
				throw new IllegalArgumentException("Il nome non può essere nullo");
			return true;
		}
		
		/**
		 * 
		 * @param 
		 * @return
		 */
		private boolean checkCognome(String cognome){
			if (cognome == null)
				throw new IllegalArgumentException("Il cognome non può essere nullo");
			return true;
		}
		
		/**
		 * 
		 * @param 
		 * @return
		 */
		private boolean checkSesso(String sesso) {
			 if (sesso != "F" || sesso != "M")
					throw new IllegalArgumentException("Il sesso può essere solo F o M");
				return true; 
		 
		}
		
		
		/**
		 * @requires
		 * @param 
		 * @return
		 */
		private boolean checkEta(int[] dataNascita){
			int eta =  calcolaEta(dataNascita);
			if (eta < 18) //18 = maggiore eta in Italia!
				throw new IllegalArgumentException("L'elettore non può essere minorenne");
			return true;
		}
		
		private int calcolaEta(int[] nascita) {
			int eta = 0;
			//usa qualche libreira per calcolare l'eta
			
			return eta;
		}
		
		/**
		 * Indica se l'utente ha già votato per una determinata elezione
		 * 
		 * @return {@code false} se l'utente non ha ancora votato per la stessa, quindi può votare. 
		 */
		 // @parama elezione elezione per cui si vuole sapere se l'utente ha già votato
		private boolean hasAlreadyVoted (boolean voto /*, Votazione elezione*/) {
			if(esprimi_voto(voto /*,elezione*/))
				throw new IllegalArgumentException("L'utente ha già votato per questa elezione");
			return false;
		}
		
		private boolean checkComune(Elettore elettore){
				if(elettore.nazione == "Italia") {
					if (elettore.comune == null) {
						throw new IllegalArgumentException("Il comune non può essere null, se la nazione corrisponde a Italia");
					}
				}
			return true; 
		}
		
		private boolean checkData(Elettore elettore){
			//libreria per prendere dataOdierna
			
			/*if(elettore.dataNascita > dataOdierna) {
				throw new IllegalArgumentException("La data inserita deve essere valida");
			}*/
		return true; 
	}
		

//--------------------------------------------------------------------------------------------------
	//resta una cosa separata con il suo scopo unico quale comunicazione del DB.
	//In altri casi ha poco senso avere come suoi attributi (vedi implementazione astratta) delle cose relative alla comunicazione con il DB.
	Utente utenza;
	
	/**
	 * Permette di creare un nuovo Elettore.
	 * 
	 * <p>
	 * La sua creazione è subordinata dal passaggio come parametro
	 * di un Utente che non sia nullo e che sia di tipologia
	 * {@code Elettore} [{@link utenze.Utente.tipoUtente}].
	 * 
	 * @param utenza utenza a cui è associato l'elettore restituito
	 */
	public Elettore(Utente utenza) {
		if (utenza == null)
			throw new IllegalArgumentException("L'utente non può essere nullo");
		if (!utenza.isTypeOfUser(tipoUtente.Elettore))
			throw new IllegalArgumentException("L'utenza passata non è un elettore");
		this.utenza = utenza;
	}
	//METODI --------------------------------------------------------------------------------------
	/**
	 * Indica se l'utente ha già espresso il per una determinata elezione
	 * 
	 * @return {@code true} se l'utente ha già votato, {@code false} se l'utente ha ancora votato votato. 
	 */
	public boolean esprimi_voto(boolean voto /*, Votazione elezione*/) {
		/*
		 * Query per richiedere se l'utente ha già votato al Database.
		 * 
		 * Return della risposta. 
		 * */
		if(/*elezione &&*/ voto) { //se elezione scelta = true e voto = true -> voto per quell'elezione già espresso
			return true;
		}
		return false;
	}
	
	//METODI VECCHI----------------------------------------------------------------------------------------
	/**
	 * Indica se l'utente può votare per una determinata elezione
	 * 
	 * @return {@code true} se l'utente può votare. 
	 */
	// @parama elezione elezione per cui si vuole sapere se l'utente può votare
	public boolean canVote (/*Elezione elezione*/) {
		
		/*
		 * Query per richiedere se l'utente può votare al Database.
		 * 
		 * Return della risposta. 
		 * */
		return false;
	}
	
}
