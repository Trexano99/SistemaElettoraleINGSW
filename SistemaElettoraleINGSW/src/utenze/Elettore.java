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
	 * La sua creazione � subordinata dal passaggio come parametro
	 * di un Utente che non sia nullo e che sia di tipologia
	 * {@link utenze.Utente.tipoUtente}.
	 * 
	 * @param utenza
	 */
	public Elettore(Utente utenza) {
		if (utenza == null)
			throw new IllegalArgumentException("L'utente non pu� essere nullo");
		if (!utenza.isTypeOfUser(tipoUtente.Elettore))
			throw new IllegalArgumentException("L'utenza passata non � un elettore");
		this.utenza = utenza;
	}
	
	/**
	 * Indica se l'utente pu� votare per una determinata elezione
	 * 
	 * @parama elezione elezione per cui si vuole sapere se l'utente pu� votare
	 * @return {@code true} se l'utente pu� votare. 
	 */
	public boolean canVote (/*Elezione elezione*/) {
		
		/*
		 * Query per richiedere se l'utente pu� votare al Database.
		 * 
		 * Return della risposta. 
		 * */
		return false;
	}
	
	/**
	 * Indica se l'utente ha gi� votato per una determinata elezione
	 * 
	 * @parama elezione elezione per cui si vuole sapere se l'utente ha gi� votato
	 * @return {@code true} se l'utente ha gi� votato per la stessa. 
	 */
	public boolean hasAlreadyVoted (/*Elezione elezione*/) {
		
		/*
		 * Query per richiedere se l'utente ha gi� votato al Database.
		 * 
		 * Return della risposta. 
		 * */
		return false;
	}
}
