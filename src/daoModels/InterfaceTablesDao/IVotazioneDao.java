package daoModels.InterfaceTablesDao;

import java.util.List;

import daoModels.ElezioneVote_Categorico;
import daoModels.ElezioneVote_CategoricoConPref;
import daoModels.ElezioneVote_Ordinale;
import daoModels.ReferendumVote;
import daoModels.DbTablesRapresentation.VotoReferendum_TB;
import useObject.voteElements.Elezione;
import useObject.voteElements.Referendum;

public interface IVotazioneDao {
	
	public boolean addElezioneVote(ElezioneVote_Categorico referVote);
	
	public boolean addElezioneVote(ElezioneVote_CategoricoConPref referVote);
	
	public boolean addElezioneVote(ElezioneVote_Ordinale referVote);

	public boolean addReferendumVote(ReferendumVote referVote);
	
	public Boolean hasElettoreVotedForRef(Referendum ref);
	
	public Boolean hasElettoreVotedForElez(Elezione ele);
	
	public List<VotoReferendum_TB> getVotiReferendum(Referendum referendum);
	
	

}
