package utenze;

import utenze.Utente.tipoUtente;

/**
 * Questa classe rappresenta un Elettore del sistema di voto.
 * 
 * @author Massimiliano Visconti
 *
 */
public final class Elettore {

	//resta una cosa separata con il suo scopo unico quale comunicazione del DB.
	//In altri casi ha poco senso avere come suoi attributi (vedi implementazione astratta) delle cose relative alla comunicazione con il DB.
	Utente utenza;
	
	/**
	 * Permette di creare un nuovo Elettore.
	 * 
	 * <p>
	 * La sua creazione è subordinata dal passaggio come parametro
	 * di un Utente che non sia nullo e che sia di tipologia
	 * {@link utenze.Utente.tipoUtente}.
	 * 
	 * @param utenza
	 */
	public Elettore(Utente utenza) {
		if (utenza == null)
			throw new IllegalArgumentException("L'utente non può essere nullo");
		if (!utenza.isTypeOfUser(tipoUtente.Elettore))
			throw new IllegalArgumentException("L'utenza passata non è un elettore");
		this.utenza = utenza;
	}
	
	/**
	 * Indica se l'utente può votare per una determinata elezione
	 * 
	 * @parama elezione elezione per cui si vuole sapere se l'utente può votare
	 * @return {@code true} se l'utente può votare. 
	 */
	public boolean canVote (/*Elezione elezione*/) {
		
		/*
		 * Query per richiedere se l'utente può votare al Database.
		 * 
		 * Return della risposta. 
		 * */
		return false;
	}
	
	/**
	 * Indica se l'utente ha già votato per una determinata elezione
	 * 
	 * @parama elezione elezione per cui si vuole sapere se l'utente ha già votato
	 * @return {@code true} se l'utente ha già votato per la stessa. 
	 */
	public boolean hasAlreadyVoted (/*Elezione elezione*/) {
		
		/*
		 * Query per richiedere se l'utente ha già votato al Database.
		 * 
		 * Return della risposta. 
		 * */
		return false;
	}
}
