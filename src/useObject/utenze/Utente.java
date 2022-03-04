package useObject.utenze;

import java.util.List;

import useObject.voteElements.Votazione;

public abstract class Utente {

	protected String id;
	protected String nome;
	protected String cognome;
	
	public abstract List<Votazione> getAllVotazioni();

	protected Utente(String id, String nome, String cognome) {
		if(id==null||nome==null||cognome==null) 
			throw new IllegalArgumentException("Fields cannot be null");
		
		this.id = id;
		this.nome = nome;
		this.cognome = cognome;
	}

	public String getId() {
		return id;
	}

	public String getNome() {
		return nome;
	}

	public String getCognome() {
		return cognome;
	}
	
	
}
