package daoModels.DbTablesRapresentation;

public class VotoElezione_TB {

	private int id;
	private Boolean isWhiteVote;
	private int elezione_fk;

	
	public VotoElezione_TB(int id, Boolean isWhiteVote, int elezione_fk) {
		super();
		this.id = id;
		this.isWhiteVote = isWhiteVote;
		this.elezione_fk = elezione_fk;
	}
	
	
	public int getId() {
		return id;
	}
	public Boolean getIsWhiteVote() {
		return isWhiteVote;
	}
	public int getElezione_fk() {
		return elezione_fk;
	}
	
}
