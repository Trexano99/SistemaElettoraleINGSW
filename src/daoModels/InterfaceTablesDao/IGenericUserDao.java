package daoModels.InterfaceTablesDao;

import daoModels.DbTablesRapresentation.GenericUser_TB;

/***
 * La seguente interfaccia segue il modello DAO mettendo a disposizione
 * i metodi richiesti per il login che verranno dunque poi specializzati
 * nell'implementazione per essere nel caso versatili ad un cambio di DB.
 * 
 * @author Massimiliano Visconti
 *
 */
public interface IGenericUserDao {

	/**
	 * Permette di eseguire il login da elettore. 
	 * La password può essere passata in chiaro poichè l'hashing della
	 * stessa viene implementato lato DB. 
	 * 
	 * @param utente Le credenziali utente
	 * @return		{@code null} se login fallito, 
	 * altrimenti l'identificativo dell'utente
	 */
	public String loginElettore(GenericUser_TB utente);
	
	/**
	 * Permette di eseguire il login da Impiegato.
	 * La password può essere passata in chiaro poichè l'hashing della
	 * stessa viene implementato lato DB. 
	 * 
	 * @param utente Le credenziali utente
	* @return		{@code null} se login fallito, 
	 * altrimenti l'identificativo dell'utente
	 */
	public String loginImpiegato(GenericUser_TB utente);
	
}
