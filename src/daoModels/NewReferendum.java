package daoModels;

public class NewReferendum {
	
	private String nomeBreve;
	private Boolean isClosed, isFinished, withQuorum;
	private String quesito;
	
	
	public NewReferendum(String nomeBreve, Boolean isClosed, Boolean isFinished, Boolean withQuorum, String quesito) {
		super();
		this.nomeBreve = nomeBreve;
		this.isClosed = isClosed;
		this.isFinished = isFinished;
		this.withQuorum = withQuorum;
		this.quesito = quesito;
	}


	public String getNomeBreve() {
		return nomeBreve;
	}
	public Boolean getIsClosed() {
		return isClosed;
	}
	public Boolean getIsFinished() {
		return isFinished;
	}
	public Boolean getWithQuorum() {
		return withQuorum;
	}
	public String getQuesito() {
		return quesito;
	}
  

}
