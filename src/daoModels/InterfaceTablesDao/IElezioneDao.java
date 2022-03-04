package daoModels.InterfaceTablesDao;

import java.util.List;

import daoModels.ElezioneUpdater;
import daoModels.NewElezione;
import daoModels.DbTablesRapresentation.Elezione_TB;
import useObject.voteElements.Elezione;

public interface IElezioneDao {
	
	public List<Elezione_TB> getAllElezioni();
	
	public boolean addNewElezione(NewElezione elezione);
	
	public boolean removeElezione(Elezione elezione);
	
	public boolean updateElezione(ElezioneUpdater elezione);

}
