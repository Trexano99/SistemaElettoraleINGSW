package daoModels;

import useObject.voteElements.Votazione.TipologiaElezione;

public class NewElezione {
	
	private String nomeBreve;
	private Boolean isClosed, isFinished, maggioranzaAssoluta;
	private TipologiaElezione tipoElezione;
	
	
	public NewElezione(String nomeBreve, Boolean isClosed, Boolean isFinished, Boolean maggioranzaAssoluta,
			TipologiaElezione tipoElezione) {
		this.nomeBreve = nomeBreve;
		this.isClosed = isClosed;
		this.isFinished = isFinished;
		this.maggioranzaAssoluta = maggioranzaAssoluta;
		this.tipoElezione = tipoElezione;
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
	public Boolean getMaggioranzaAssoluta() {
		return maggioranzaAssoluta;
	}
	public TipologiaElezione getTipoElezione() {
		return tipoElezione;
	}


}
