package daoModels.DbTablesRapresentation;

import useObject.voteElements.Votazione.TipologiaElezione;

public class Referendum_TB {

	int id;
	String nomeBreve;
	String quesito;
	Boolean withQuorum;
	Boolean isClosed;
	Boolean isFinished;
	TipologiaElezione tipoElezione;
	
	public Referendum_TB(int id, String nomeBreve, String quesito, Boolean withQuorum, Boolean isClosed,
			Boolean isFinished, TipologiaElezione tipoElezione) {
		super();
		this.id = id;
		this.nomeBreve = nomeBreve;
		this.quesito = quesito;
		this.withQuorum = withQuorum;
		this.isClosed = isClosed;
		this.isFinished = isFinished;
		this.tipoElezione = tipoElezione;
	}
	
	public int getId() {
		return id;
	}
	public String getNomeBreve() {
		return nomeBreve;
	}
	public String getQuesito() {
		return quesito;
	}
	public Boolean getWithQuorum() {
		return withQuorum;
	}
	public Boolean getIsClosed() {
		return isClosed;
	}
	public Boolean getIsFinished() {
		return isFinished;
	}
	public TipologiaElezione getTipoElezione() {
		return tipoElezione;
	}
	
	
	
	
}
