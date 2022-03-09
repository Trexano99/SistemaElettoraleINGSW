package useObject.utenze;

import java.util.List;
import java.util.Objects;

import useObject.voteElements.Votazione;

public abstract class Utente {

	protected String id;
	protected String nome;
	protected String cognome;
	
	public abstract List<Votazione> getAllVotazioni();
	/*{context Utente
	 * inv: self.allIstances() -> isUnique(id)
	 * inv lunghezzaNome: nome.size() > 1
	 * inv lunghezzaCognome: cognome.size() > 1
	 * }*/
	
	/*@ 
	 @ invariant nome.length() >1;
	 @ invariant cognome.length() >1;
	 @ assignable id;
	 @ assignable nome;
	 @ assignable cognome;
	 @*/
	protected Utente(String id, String nome, String cognome) {
		if(id==null||nome==null||cognome==null) 
			throw new IllegalArgumentException("Fields cannot be null");
		
		this.id = id;
		this.nome = nome;
		this.cognome = cognome;
	}
	/*@ ensures \result == id;
	 @*/
	public String getId() {
		return id;
	}
	
	/*@ ensures \result == nome;
	 @*/
	public String getNome() {
		return nome;
	}
	
	/*@ ensures \result == cognome;
	 @*/
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
