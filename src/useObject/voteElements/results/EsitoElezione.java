package useObject.voteElements.results;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import auditing.LogElement;
import auditing.LogHistory;
import daoModels.ElezioneVote;
import daoModels.ImplTablesDao.VotazioneDao;
import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;
import useObject.voteElements.Votazione;

public class EsitoElezione extends EsitoVotazione {

	private Map<Partito, Integer> votiPartiti = new HashMap<Partito, Integer>();
	private Map<Candidato, Integer> votiCandidati = new HashMap<Candidato, Integer>();
	
	private EsitoElezione(int numeroSchedeBianche, int numeroSchedeTotali, Map<Partito, Integer> votiPartiti,
			Map<Candidato, Integer> votiCandidati) {
		super(numeroSchedeBianche, numeroSchedeTotali);
		this.votiPartiti = votiPartiti;
		this.votiCandidati = votiCandidati;
	}

	public static EsitoElezione getEsitoElezione(Elezione elezione) {
		int schedeBianche = 0, votiTotali = 0;
		HashMap<Partito, Integer> votiPartiti = new HashMap<Partito, Integer>();
		HashMap<Candidato, Integer> votiCandidati = new HashMap<Candidato, Integer>();
		for (ElezioneVote voto : new VotazioneDao().getVotiElezione(elezione)) {
			votiTotali++;
			if(voto.getCandidatiVotati()==null && voto.getPartitiVotati()==null)
				schedeBianche++;
			else {
				switch(elezione.getTipoElezione()) {
				case VotazioneCategorica:
				case VotazioneCategoricaConPref:{
					List<Candidato> candidati = voto.getCandidatiVotati();
					 for (int i=0; i<candidati.size();i++) {
						 if(votiCandidati.containsKey(candidati.get(i)))
							 votiCandidati.put(candidati.get(i), votiCandidati.get(votiCandidati.get(i)+1));
						 else
							 votiCandidati.put(candidati.get(i), 1);
					 } 
					 List<Partito> partiti = voto.getPartitiVotati();
					 for (int i=0; i<partiti.size();i++) {
						 if(votiPartiti.containsKey(partiti.get(i)))
							 votiPartiti.put(partiti.get(i), votiPartiti.get(votiPartiti.get(i)+1));
						 else
							 votiPartiti.put(partiti.get(i), 1);
					 } 
					 break;
				}
				case VotazioneOrdinale:{
					List<Candidato> candidati = voto.getCandidatiVotati();
					 for (int i=0; i<candidati.size();i++) {
						 if(votiCandidati.containsKey(candidati.get(i)))
							 votiCandidati.put(candidati.get(i), votiCandidati.get(votiCandidati.get(i)+1/(i+1)));
						 else
							 votiCandidati.put(candidati.get(i), 1);
					 } 
					 List<Partito> partiti = voto.getPartitiVotati();
					 for (int i=0; i<partiti.size();i++) {
						 if(votiPartiti.containsKey(partiti.get(i)))
							 votiPartiti.put(partiti.get(i), votiPartiti.get(votiPartiti.get(i)+1/(i+1)));
						 else
							 votiPartiti.put(partiti.get(i), 1);
					 } 
					 break;
				}
				default:
					LogHistory.getInstance().addLog(new LogElement(EsitoElezione.class, "getEsitoElezione", "Tipo elezione non supportato o Referendum", true) );
					throw new IllegalStateException("Not expected this type of election: "+elezione.getTipoElezione());
				}
				
			}
		}
		return new EsitoElezione(schedeBianche, votiTotali, votiPartiti, votiCandidati);
		
	}
	
	
	
}
