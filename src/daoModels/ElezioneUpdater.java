package daoModels;

import java.util.List;

import auditing.LogElement;
import auditing.LogHistory;
import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;
import useObject.voteElements.Votazione.TipologiaElezione;

public class ElezioneUpdater {

	private Elezione elezRef;
	
	private int id;
	
	private String nome;
	private boolean isClosed;
	private boolean isFinished;
	private TipologiaElezione tipoElezione;
	private Boolean maggioranzaAssoluta;
	private List<Candidato> candidatiProposti=null;
	private List<Partito> partitiProposti=null;
	
	public ElezioneUpdater(Elezione elezione) {
		id = elezione.getId();
		nome = elezione.getNome();
		isClosed = elezione.isClosed();
		isFinished = elezione.isFinished();
		tipoElezione = elezione.getTipoElezione();
		maggioranzaAssoluta = elezione.getMaggioranzaAssoluta();
		elezRef = elezione;
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

	public List<Candidato> getCandidatiProposti() {
		if(candidatiProposti==null)
			return Candidato.getAllCandidatiElezione(elezRef);
		return candidatiProposti;
	}

	public List<Partito> getPartitiProposti() {
		if(candidatiProposti==null)
			return Partito.getAllPartitiElezione(elezRef);
		return partitiProposti;
	}

	public void setCandidatiProposti(List<Candidato> candidatiProposti) {
		this.candidatiProposti = candidatiProposti;
	}

	public void setPartitiProposti(List<Partito> partitiProposti) {
		this.partitiProposti = partitiProposti;
	}
	
	public String getListaCandidatiDbFormat() {
		if(getCandidatiProposti()  == null ||getCandidatiProposti().size()==0)
			return "[]";
		StringBuilder sb = new StringBuilder("[");
		for (Candidato candidato : getCandidatiProposti()) {
			sb.append(candidato.getId()+",");
		}
		String finale = sb.toString();
		return finale.substring(0,finale.length()-1)+"]";
		
	}
	
	public String getListaPartitiDbFormat() {
		if(getPartitiProposti() == null ||getPartitiProposti().size()==0)
			return "[]";
		StringBuilder sb = new StringBuilder("[");
		for (Partito partito : getPartitiProposti()) {
			sb.append(partito.getId()+",");
		}
		String finale = sb.toString();
		return finale.substring(0,finale.length()-1)+"]";
		
	}
	
	
}
