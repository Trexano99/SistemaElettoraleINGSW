package utenze;

import utenze.Utente.tipoUtente;

/**
 * Questa classe rappresenta uno Scrutatore del sistema di voto.
 * 
 * @author Shanti Ayala
 *
 */
public final class Scrutatore {

	Utente utenza;
	
	/**
	 * Permette di creare un nuovo Scrutatore.
	 * 
	 * <p>
	 * La sua creazione � subordinata dal passaggio come parametro
	 * di un Utente che non sia nullo e che sia di tipologia
	 * {@link utenze.Utente.tipoUtente}.
	 * 
	 * @param utenza
	 */
	public Scrutatore(Utente utenza) {
		if (utenza == null)
			throw new IllegalArgumentException("L'utente non pu� essere nullo");
		if (!utenza.isTypeOfUser(tipoUtente.Scrutatore))
			throw new IllegalArgumentException("L'utenza passata non � uno scrutatore");
		this.utenza = utenza;
	}
	
	/**
	 * Lo scrutatore vuole istanziare una nuova sessione di Voto
	 * 
	 * @parama ....
	 * @return ....
	 */
	
	public void newVoteSession (/*@parama*/) {
		
		/*	Set dei parametri della sessione di voto:
		 * 	-modalit� voto
		 * 	-calcolo vincitore 
		 * 	-lista candidati (candidato inserito deve appartenere alla lista nel db, checkCandidato)
		 *  
		 * 	Raise msg se verificati problemi nel set dei parametri
		 * */
	}

	
	/**
	 * Indica se l'utente/scrutatore pu� avviare la fase di scrutinio (Ballot)
	 * 
	 * @parama Scrutinio ballot per il quale si vuole sapere se la sessione � gi� attiva o no.
	 * @return {@code true} se la sessione pu� essere avviata, ossia attualmente inattiva.
	 */
	public boolean canStartABallot (/*Scrutinio ballot*/) {
		
		/*
		 * Query per richiedere lo scrutinio � gia avviato oppure no.
		 * 
		 * 
		 * Return della risposta. 
		 * */
		return false;
	}
	
	
}

