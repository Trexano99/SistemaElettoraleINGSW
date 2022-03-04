package daoModels;

import useObject.voteElements.Referendum;

public class ReferendumVote {
	
	private Referendum referendum;
	private Boolean vote;
	
	
	public ReferendumVote(Referendum referendum, Boolean vote) {
		this.referendum = referendum;
		this.vote = vote;
	}

	
	public Referendum getReferendum() {
		return referendum;
	}
	public boolean isVote() {
		return vote;
	}
	
}
