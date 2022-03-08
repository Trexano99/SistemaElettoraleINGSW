package useObject.voteElements.results;

import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collections;
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

public class EsitoElezione extends EsitoVotazione {

	private Elezione elezione;
	
	private List<GenericVoto> votiPartiti;
	private List<GenericVoto> votiCandidati;
	
	private EsitoElezione(int numeroSchedeBianche, int numeroSchedeTotali, List<GenericVoto> votiPartiti,
			List<GenericVoto> votiCandidati, Elezione elezione) {
		super(numeroSchedeBianche, numeroSchedeTotali);
		this.votiPartiti = votiPartiti;
		this.votiCandidati = votiCandidati;
		this.elezione = elezione;
	}

	public static EsitoElezione getEsitoElezione(Elezione elezione) {
		int schedeBianche = 0, votiTotali = 0;
		HashMap<Partito, Double> votiPartiti = new HashMap<Partito, Double>();
		List<Partito> partitiCandidati = Partito.getAllPartitiElezione(elezione);
		for (Partito partito : partitiCandidati) 
			votiPartiti.put(partito, 0.0);
		HashMap<Candidato, Double> votiCandidati = new HashMap<Candidato, Double>();
		List<Candidato> candidatiCandidati = Candidato.getAllCandidatiElezione(elezione);
		for (Candidato candidato : candidatiCandidati) 
			votiCandidati.put(candidato, 0.0);
		List<ElezioneVote> voti = new VotazioneDao().getVotiElezione(elezione);
		for (ElezioneVote voto : voti) {
			votiTotali++;
			if((voto.getCandidatiVotati()==null && voto.getPartitiVotati()==null)||
					(voto.getCandidatiVotati().size()== 0 && voto.getPartitiVotati().size()==0))
				schedeBianche++;
			else {
				switch(elezione.getTipoElezione()) {
				case VotazioneCategorica:
				case VotazioneCategoricaConPref:{
					List<Candidato> candidati = voto.getCandidatiVotati();
					 for (int i=0; i<candidati.size();i++) {
						 if(votiCandidati.containsKey(candidati.get(i)))
							 votiCandidati.put(candidati.get(i), votiCandidati.get(candidati.get(i))+1);
						 else
							 votiCandidati.put(candidati.get(i), 1.0);
					 } 
					 List<Partito> partiti = voto.getPartitiVotati();
					 for (int i=0; i<partiti.size();i++) {
						 if(votiPartiti.containsKey(partiti.get(i)))
							 votiPartiti.put(partiti.get(i), votiPartiti.get(partiti.get(i))+1);
						 else
							 votiPartiti.put(partiti.get(i), 1.0);
					 } 
					 break;
				}
				case VotazioneOrdinale:{
					List<Candidato> candidati = voto.getCandidatiVotati();
					 for (int i=0; i<candidati.size();i++) {
						 if(votiCandidati.containsKey(candidati.get(i)))
							 votiCandidati.put(candidati.get(i), votiCandidati.get(candidati.get(i))+1./(i+1.));
						 else
							 votiCandidati.put(candidati.get(i), 1.0);
					 } 
					 List<Partito> partiti = voto.getPartitiVotati();
					 for (int i=0; i<partiti.size();i++) {
						 if(votiPartiti.containsKey(partiti.get(i)))
							 votiPartiti.put(partiti.get(i), votiPartiti.get(partiti.get(i))+1./(i+1.));
						 else
							 votiPartiti.put(partiti.get(i), 1.0);
					 } 
					 break;
				}
				default:
					LogHistory.getInstance().addLog(new LogElement(EsitoElezione.class, "getEsitoElezione", "Tipo elezione non supportato o Referendum", true) );
					throw new IllegalStateException("Not expected this type of election: "+elezione.getTipoElezione());
				}
				
			}
		}
		List<GenericVoto> votiCand = new ArrayList<GenericVoto>();
		List<GenericVoto> votiPart = new ArrayList<GenericVoto>();
		for (Map.Entry<Candidato, Double> elemento : votiCandidati.entrySet()) {
			votiCand.add(new GenericVoto(elemento.getKey().toString(), new DecimalFormat("##.#").format(elemento.getValue())));
		}
		for (Map.Entry<Partito, Double> elemento : votiPartiti.entrySet()) {
			votiPart.add(new GenericVoto(elemento.getKey().getNome(), new DecimalFormat("##.#").format(elemento.getValue())));
		}
		votiCand.sort((x,y) -> x.getNumeroVoti().compareTo(y.getNumeroVoti()));
		votiPart.sort((x,y) -> x.getNumeroVoti().compareTo(y.getNumeroVoti()));
		Collections.reverse(votiCand);
		Collections.reverse(votiPart);
		return new EsitoElezione(schedeBianche, votiTotali, votiPart, votiCand, elezione);
		
	}
	
	public boolean getIsValid() {
		return elezione.getMaggioranzaAssoluta()&&getNumeroSchedeBianche()>=(getNumeroSchedeTotali()/2);
	}

	public List<GenericVoto> getVotiPartiti() {
		return votiPartiti;
	}

	public List<GenericVoto> getVotiCandidati() {
		return votiCandidati;
	}
	
	
	
	
}
