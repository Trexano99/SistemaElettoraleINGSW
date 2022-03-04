package daoModels.DbTablesRapresentation;

public class VotoReferendum_TB {

	private int id;
	private Boolean isPositive, isWhiteVote;
	private int referendumRef;
	
	
	public VotoReferendum_TB(int id, Boolean isPositive, Boolean isWhiteVote, int referendumRef) {
		this.id = id;
		this.isPositive = isPositive;
		this.isWhiteVote = isWhiteVote;
		this.referendumRef = referendumRef;
	}


	public int getId() {
		return id;
	}
	public Boolean getIsPositive() {
		return isPositive;
	}
	public Boolean getIsWhiteVote() {
		return isWhiteVote;
	}
	public int getReferendumRef() {
		return referendumRef;
	}
	
	
	
}
