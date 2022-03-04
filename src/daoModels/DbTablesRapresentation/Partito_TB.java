package daoModels.DbTablesRapresentation;

public class Partito_TB {

	private int id;
	private String nome;
	
	public Partito_TB(int id, String nome) {
		super();
		this.id = id;
		this.nome = nome;
	}

	public int getId() {
		return id;
	}
	public String getNome() {
		return nome;
	}
	
}
