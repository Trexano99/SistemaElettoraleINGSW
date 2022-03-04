package daoModels.DbTablesRapresentation;

public class Elettore_TB {

	String codiceFiscale;
	String Nome;
	String Cognome;
	
	public Elettore_TB(String codiceFiscale, String nome, String cognome) {
		super();
		this.codiceFiscale = codiceFiscale;
		Nome = nome;
		Cognome = cognome;
	}
	
	
	public String getCodiceFiscale() {
		return codiceFiscale;
	}
	public String getNome() {
		return Nome;
	}
	public String getCognome() {
		return Cognome;
	}
	
	
	
}
