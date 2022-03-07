package daoModels;

import java.util.List;

import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;

public class ElezioneVote_CategoricoConPref {

	private Elezione elezione;
	private Partito partito;
	private List<Candidato> candidati;
	
	
	public ElezioneVote_CategoricoConPref(Elezione elezione, Partito partito,
			List<Candidato> candidati) {
		this.elezione = elezione;
		this.partito = partito;
		this.candidati = candidati;
	}


	public Elezione getElezione() {
		return elezione;
	}
	public Partito getPartito() {
		return partito;
	}
	public List<Candidato> getCandidati() {
		return candidati;
	}
	
	public String getListaCandidatiDbFormat() {
		if(candidati == null || candidati.size()==0)
			return "[]";
		StringBuilder sb = new StringBuilder("[");
		for (Candidato candidato : candidati) {
			sb.append(candidato.getId()+",");
		}
		String finale = sb.toString();
		return finale.substring(0,finale.length()-1)+"]";
		
	}
	
	
}
