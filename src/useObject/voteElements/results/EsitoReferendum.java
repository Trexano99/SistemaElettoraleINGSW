package useObject.voteElements.results;

import java.util.List;

import daoModels.DbTablesRapresentation.VotoReferendum_TB;
import daoModels.ImplTablesDao.VotazioneDao;
import useObject.voteElements.Referendum;

public class EsitoReferendum extends EsitoVotazione {

	private int votiPositivi;
	private int votiNegativi;
	private boolean isValid;
	
	private EsitoReferendum(int votiPositivi, int votiNegativi,int votiSchedeBianche, boolean isValid) {
		super(votiSchedeBianche, votiPositivi+votiNegativi+votiSchedeBianche);
		this.votiPositivi = votiPositivi;
		this.votiNegativi = votiNegativi;
		this.isValid = isValid;
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
		
		if(referendum.withQuorum()&&votiBia>=(votiPos+votiNeg))
			return new EsitoReferendum(votiPos, votiNeg, votiBia, false);
		return new EsitoReferendum(votiPos, votiNeg, votiBia, true);
		
	}

	public int getVotiPositivi() {
		return votiPositivi;
	}
	public int getVotiNegativi() {
		return votiNegativi;
	}

	public boolean isValid() {
		return isValid;
	}
	
	
}
