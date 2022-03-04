package daoModels.DbTablesRapresentation;

import useObject.voteElements.Votazione.TipologiaElezione;

public class Elezione_TB {

	int id;
	String nomeBreve;
	Boolean maggioranzaAssoluta;
	Boolean isClosed;
	Boolean isFinished;
	TipologiaElezione tipoElezione;
	
	public Elezione_TB(int id, String nomeBreve, Boolean maggioranzaAssoluta, Boolean isClosed, Boolean isFinished,
			TipologiaElezione tipoElezione) {
		this.id = id;
		this.nomeBreve = nomeBreve;
		this.maggioranzaAssoluta = maggioranzaAssoluta;
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

	public Boolean getMaggioranzaAssoluta() {
		return maggioranzaAssoluta;
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
