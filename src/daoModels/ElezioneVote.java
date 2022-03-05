package daoModels;

import java.util.List;

import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;

public class ElezioneVote {

	Elezione elezione;
	List<Candidato> candidatiVotati;
	List<Partito> partitiVotati;
		
	public ElezioneVote(Elezione elezione, List<Candidato> candidatiVotati, List<Partito> partitiVotati) {
		super();
		this.elezione = elezione;
		this.candidatiVotati = candidatiVotati;
		this.partitiVotati = partitiVotati;
	}
	
	public Elezione getElezione() {
		return elezione;
	}
	public List<Candidato> getCandidatiVotati() {
		return candidatiVotati;
	}
	public List<Partito> getPartitiVotati() {
		return partitiVotati;
	}
	
	
	
	
}
