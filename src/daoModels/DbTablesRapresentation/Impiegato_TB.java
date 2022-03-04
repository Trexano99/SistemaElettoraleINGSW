package daoModels.DbTablesRapresentation;

public class Impiegato_TB {

	String id;
	String Nome;
	String Cognome;
	
	public Impiegato_TB(String id, String nome, String cognome) {
		super();
		this.id = id;
		Nome = nome;
		Cognome = cognome;
	}
	
	
	public String getId() {
		return id;
	}
	public String getNome() {
		return Nome;
	}
	public String getCognome() {
		return Cognome;
	}
	
	
	
}
