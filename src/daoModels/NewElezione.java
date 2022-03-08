package daoModels;

import java.util.List;

import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Votazione.TipologiaElezione;

public class NewElezione {
	
	private String nomeBreve;
	private Boolean isClosed, isFinished, maggioranzaAssoluta;
	private TipologiaElezione tipoElezione;
	
	private List<Candidato> candidatiPartecipanti;
	private List<Partito> partitiPartecipanti;
	
	
	public NewElezione(String nomeBreve, Boolean isClosed, Boolean isFinished, Boolean maggioranzaAssoluta,
			TipologiaElezione tipoElezione, List<Candidato> candidatiPartecipanti, List<Partito> partitiPartecipanti) {
		this.nomeBreve = nomeBreve;
		this.isClosed = isClosed;
		this.isFinished = isFinished;
		this.maggioranzaAssoluta = maggioranzaAssoluta;
		this.tipoElezione = tipoElezione;
		this.candidatiPartecipanti = candidatiPartecipanti;
		this.partitiPartecipanti = partitiPartecipanti;
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
	public List<Candidato> getCandidatiPartecipanti() {
		return candidatiPartecipanti;
	}
	public List<Partito> getPartitiPartecipanti() {
		return partitiPartecipanti;
	}
	
	public String getListaCandidatiDbFormat() {
		if(candidatiPartecipanti == null ||candidatiPartecipanti.size()==0)
			return "[]";
		StringBuilder sb = new StringBuilder("[");
		for (Candidato candidato : candidatiPartecipanti) {
			sb.append(candidato.getId()+",");
		}
		String finale = sb.toString();
		return finale.substring(0,finale.length()-1)+"]";
		
	}
	
	public String getListaPartitiDbFormat() {
		if(partitiPartecipanti == null ||partitiPartecipanti.size()==0)
			return "[]";
		StringBuilder sb = new StringBuilder("[");
		for (Partito partito : partitiPartecipanti) {
			sb.append(partito.getId()+",");
		}
		String finale = sb.toString();
		return finale.substring(0,finale.length()-1)+"]";
		
	}


}
