package daoModels;

import auditing.LogElement;
import auditing.LogHistory;
import useObject.voteElements.Elezione;
import useObject.voteElements.Votazione.TipologiaElezione;

public class ElezioneUpdater {

	private int id;
	
	private String nome;
	private boolean isClosed;
	private boolean isFinished;
	private TipologiaElezione tipoElezione;
	private Boolean maggioranzaAssoluta;
	
	public ElezioneUpdater(Elezione elezione) {
		id = elezione.getId();
		nome = elezione.getNome();
		isClosed = elezione.isClosed();
		isFinished = elezione.isFinished();
		tipoElezione = elezione.getTipoElezione();
		maggioranzaAssoluta = elezione.getMaggioranzaAssoluta();
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

	public TipologiaElezione getTipoElezione() {
		return tipoElezione;
	}

	public void setTipoElezione(TipologiaElezione tipoElezione) {
		if(tipoElezione.equals(TipologiaElezione.Referendum)) {
			LogHistory.getInstance().addLog(new LogElement(this, "SetTipoElezione", "Impossibile cambiare una elezione in un referendum", true));
		}else {
			this.tipoElezione = tipoElezione;
		}
	}

	public Boolean getMaggioranzaAssoluta() {
		return maggioranzaAssoluta;
	}

	public void setMaggioranzaAssoluta(Boolean maggioranzaAssoluta) {
		this.maggioranzaAssoluta = maggioranzaAssoluta;
	}

	public int getId() {
		return id;
	}
	
	
	
}
