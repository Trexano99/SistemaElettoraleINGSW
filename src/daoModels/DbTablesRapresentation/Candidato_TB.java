package daoModels.DbTablesRapresentation;

import java.sql.Date;

public class Candidato_TB {

	private int id;
	
	private String nome;
	private String cognome;
	private Date dataNascita;
	private int idPartitoAppartenenza;
	
	public Candidato_TB(int id, String nome, String cognome, Date dataNascita, int idPartitoAppartenenza) {
		this.id = id;
		this.nome = nome;
		this.cognome = cognome;
		this.dataNascita = dataNascita;
		this.idPartitoAppartenenza = idPartitoAppartenenza;
	}

	public int getId() {
		return id;
	}
	public String getNome() {
		return nome;
	}
	public String getCognome() {
		return cognome;
	}
	public Date getDataNascita() {
		return dataNascita;
	}
	public int getIdPartitoAppartenenza() {
		return idPartitoAppartenenza;
	}
	
}
