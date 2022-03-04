package useObject.voteElements.results;

import java.util.List;

import daoModels.DbTablesRapresentation.VotoReferendum_TB;
import daoModels.ImplTablesDao.VotazioneDao;
import useObject.voteElements.Referendum;

public class EsitoReferendum extends EsitoVotazione {

	private int votiPositivi;
	private int votiNegativi;
	
	
	private EsitoReferendum(int votiPositivi, int votiNegativi,int votiSchedeBianche) {
		super(votiSchedeBianche, votiPositivi+votiNegativi+votiSchedeBianche);
		this.votiPositivi = votiPositivi;
		this.votiNegativi = votiNegativi;
	}
	
	public static EsitoReferendum getEsitoReferendum(Referendum referendum) {
		
		List<VotoReferendum_TB> listaVoti =  new VotazioneDao().getVotiReferendum(referendum);
		
		int votiPos=0, votiNeg = 0,votiBia = 0;
		
		for (VotoReferendum_TB voto : listaVoti) {
			if(voto.getIsWhiteVote())
				votiBia++;
			else if(voto.getIsPositive())
				votiPos++;
			else
				votiNeg++;
		}
		
		return new EsitoReferendum(votiPos, votiNeg, votiBia);
	}

	public int getVotiPositivi() {
		return votiPositivi;
	}
	public int getVotiNegativi() {
		return votiNegativi;
	}
	
}
