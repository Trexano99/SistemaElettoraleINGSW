package useObject.utenze;

import java.util.List;
import java.util.Objects;

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

	@Override
	public int hashCode() {
		return Objects.hash(id);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Utente other = (Utente) obj;
		return Objects.equals(id, other.id);
	}
	
	
	
}
