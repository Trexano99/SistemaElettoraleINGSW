package assignment;

import java.time.LocalDate;
import java.time.Period;

/**
 * Questa classe rappresenta un Elettore del sistema di voto.
 * 
 * @author Massimiliano Visconti
 *
 */
public class Elettore {
	
	public final String Nome;
	public final String Cognome;
	public final LocalDate DataNascita; 
	public final ComuneItaliano ComuneNascita;
	public final Nazione NazioneNascita;
	/**
	 * Indica se l'elettore rappresentato è Maschio. 
	 * Nel caso sia falso esso è Donna.
	 */
	public final boolean IsMale;
	
	private char[] codiceFiscale = null;
	private /*@ spec_public @*/ boolean asVoted = false;
	
	/**
	 * Ritorna il codice fiscale calcolato dell'elettore
	 * @return
	 */
	/*
	 * @ensure codiceFiscale != null
	 */
	public String getCodiceFiscale() {
		return String.valueOf(codiceFiscale);	
	}
	
	/**
	 * Indica se l'elettore ha già votato {@code true}, altrimenti {@code false} .
	 * @return
	 */
	/*
	 * @ensure \result = asVoted
	 */
	public boolean asAlreadyVoted() {
		return asVoted;	
	}
	
	/*
	 * @ requires DataNascita != null
	 */
	private boolean canVote(){
		LocalDate firstDate = DataNascita;
		LocalDate secondDate = LocalDate.now();
		return Period.between(firstDate, secondDate).getYears()>18;
	}
	
	
	/*
	 *@ requires !(nome.isEmpty())
	 *@ requires !(cognome.isEmpty())
	 *@ requires dataNascita != null
	 *@ requires comuneNascita != null
	 *@ requires nazioneNascita != null
	 */
	private Elettore(String nome, String cognome, LocalDate dataNascita, ComuneItaliano comuneNascita, Nazione nazioneNascita,
			boolean isMale) {
		if(nome.isBlank())
			throw new IllegalArgumentException("Il nome non può essere vuoto o nullo");
		if(cognome.isBlank())
			throw new IllegalArgumentException("Il cognome non può essere vuoto o nullo");
		if(dataNascita.isAfter(LocalDate.now()))
			throw new IllegalArgumentException("La data di nascita non può essere successiva alla data attuale");
		if(nazioneNascita.equals(Nazione.NazioneIta)&&comuneNascita==null)
			throw new IllegalArgumentException("Il comune di nascita non può essere nullo se la nazione è Italiana");
		Nome = nome.trim();
		Cognome = cognome.trim();
		DataNascita = dataNascita;
		ComuneNascita = comuneNascita;
		NazioneNascita = nazioneNascita;
		IsMale = isMale;
		generateCodiceFiscale();
	}
	
	/**
	 * Permette di ottenere un'istanza di Elettore straniero
	 * 
	 * @param nome Nome dell'elettore
	 * @param cognome Cognome dell'elettore 
	 * @param dataNascita Data di nascita dell'elettore  
	 * @param nazioneNascita Nazione di nascita dell'elettore 
	 * @param isMale {@code true} se l'elettore è maschio, false altrimenti
	 * @return Elettore con gli opportuni parametri
	 */
	public static Elettore foreignElettore(String nome, String cognome, LocalDate dataNascita, Nazione nazioneNascita,boolean isMale) {
		return new Elettore(nome, cognome, dataNascita, null, nazioneNascita, isMale);
	}
	
	/**
	 * Permette di ottenere un'istanza di Elettore italiano
	 * 
	 * @param nome Nome dell'elettore
	 * @param cognome Cognome dell'elettore 
	 * @param dataNascita Data di nascita dell'elettore 
	 * @param comune Comune di nascita dell'elettore 
	 * @param isMale {@code true} se l'elettore è maschio, false altrimenti
	 * @return Elettore con gli opportuni parametri
	 */
	public static Elettore italianElettore(String nome, String cognome, LocalDate dataNascita, ComuneItaliano comune,boolean isMale) {
		return new Elettore(nome, cognome, dataNascita, comune, Nazione.NazioneIta, isMale);
	}
	
	//@ requires Nome != null && Cognome != null && DataNascita != null && NazioneNascita != null 
	//@ ensures (codiceFiscale != null && codiceFiscale.length == 16)
	private void generateCodiceFiscale() {		
		codiceFiscale=CodiceFiscale.generateCodiceFiscale(this);
	}
	
	/**
	 * Permette all'elettore di esprimere il voto
	 * @throws IllegalStateException Se l'elettore ha un'età non sufficiente per esprimere il voto o ha già votato
	 */
	//@ requires asVoted == false
	//@ ensures (asVoted == true && !(\old(asVoted))==asVoted);
	public void esprimi_voto() throws IllegalStateException {
		if (asVoted)
			throw new IllegalStateException("Il seguente elettore ha già votato");
		else if(canVote())
			asVoted = true;
		else
			throw new IllegalStateException("Un elettore non può votare se minorenne");
	}
}

