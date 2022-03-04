package daoModels;

import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;

public class ElezioneVote_Categorico {
	
	private Elezione elezione;
	private Candidato candidato;
	private Partito partito;
	
	
	public ElezioneVote_Categorico(Elezione elezione, Candidato candidato, Partito partito) {
		this.elezione = elezione;
		this.candidato = candidato;
		this.partito = partito;
	}


	public Elezione getElezione() {
		return elezione;
	}
	public Candidato getCandidato() {
		return candidato;
	}
	public Partito getPartito() {
		return partito;
	}
	
}
