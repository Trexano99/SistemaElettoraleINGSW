package daoModels;

import java.util.List;

import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;

public class ElezioneVote_Ordinale {

	private Elezione elezione;
	private List<Partito> partiti;
	private List<Candidato> candidati;
	

	public ElezioneVote_Ordinale(Elezione elezione, List<Partito> partiti,
			List<Candidato> candidati) {
		this.elezione = elezione;
		this.partiti = partiti;
		this.candidati = candidati;
	}
	
	
	public Elezione getElezione() {
		return elezione;
	}
	public List<Partito> getPartiti() {
		return partiti;
	}
	public List<Candidato> getCandidati() {
		return candidati;
	}
	
	public String getListaCandidatiDbFormat() {
		StringBuilder sb = new StringBuilder("[");
		for (Candidato candidato : candidati) {
			sb.append(candidato.getId()+",");
		}
		String finale = sb.toString();
		return finale.substring(0,finale.length()-1)+"]";
		
	}
	
	public String getListaPartitiDbFormat() {
		StringBuilder sb = new StringBuilder("[");
		for (Partito partito : partiti) {
			sb.append(partito.getId()+",");
		}
		String finale = sb.toString();
		return finale.substring(0,finale.length()-1)+"]";
		
	}
}
