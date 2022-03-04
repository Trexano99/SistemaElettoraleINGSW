package daoModels;

import useObject.voteElements.Referendum;
import useObject.voteElements.Votazione.TipologiaElezione;

public class ReferendumUpdater {

	private int id;
	
	private String nome;
	private boolean isClosed;
	private boolean isFinished;
	private TipologiaElezione tipoElezione;
	private String quesito;
	private Boolean withQuorum;
	
	
	
	private ReferendumUpdater(Referendum referendum) {
		super();
		this.id = referendum.getId();
		this.nome = referendum.getNome();
		this.isClosed = referendum.isClosed();
		this.isFinished = referendum.isFinished();
		this.tipoElezione = referendum.getTipoElezione();
		this.quesito = referendum.getQuesito();
		this.withQuorum = referendum.withQuorum();
	}
	
	public String getNome() {
		return nome;
	}
	public void setNome(String nome) {
		this.nome = nome;
	}
	public boolean isClosed() {
		return isClosed;
	}
	public void setClosed(boolean isClosed) {
		this.isClosed = isClosed;
	}
	public boolean isFinished() {
		return isFinished;
	}
	public void setFinished(boolean isFinished) {
		this.isFinished = isFinished;
	}
	public String getQuesito() {
		return quesito;
	}
	public void setQuesito(String quesito) {
		this.quesito = quesito;
	}
	public Boolean getWithQuorum() {
		return withQuorum;
	}
	public void setWithQuorum(Boolean withQuorum) {
		this.withQuorum = withQuorum;
	}
	public int getId() {
		return id;
	}
	public TipologiaElezione getTipoElezione() {
		return tipoElezione;
	}
	
	
	
}
