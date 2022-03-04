package useObject.voteElements;

import java.util.ArrayList;
import java.util.List;

import daoModels.DbTablesRapresentation.Elezione_TB;
import daoModels.ImplTablesDao.ElezioneDao;
import daoModels.ImplTablesDao.VotazioneDao;

public class Elezione extends Votazione {
	
	private Boolean maggioranzaAssoluta;
	
	private Elezione(int id, String nome, boolean isClosed, boolean isFinished, TipologiaElezione tipoElezione,
			Boolean maggioranzaAssoluta) {
		super(id, nome, isClosed, isFinished, tipoElezione);
		this.maggioranzaAssoluta = maggioranzaAssoluta;
	}

	public Boolean getMaggioranzaAssoluta() {
		return maggioranzaAssoluta;
	}

	public static List<Elezione> getAllElezioni(){
		List<Elezione> tutteElez = new ArrayList<Elezione>();
		List<Elezione_TB> listaElez =  new ElezioneDao().getAllElezioni();
		VotazioneDao vd = new VotazioneDao();
		for (Elezione_TB elezione_TB : listaElez) {
			Elezione nuova = new Elezione(
					elezione_TB.getId(), 
					elezione_TB.getNomeBreve(), 
					elezione_TB.getIsClosed(), 
					elezione_TB.getIsFinished(),
					elezione_TB.getTipoElezione(), 
					elezione_TB.getMaggioranzaAssoluta());
			nuova.setHasLoggedElettoreVotedFor(vd.hasElettoreVotedForElez(nuova));
			tutteElez.add(nuova);
		}
		return tutteElez;
		
	}
	
		
}
