package daoModels.InterfaceTablesDao;

import java.util.List;

import daoModels.DbTablesRapresentation.Partito_TB;
import useObject.voteElements.Elezione;

public interface IPartitoDao {

	
	public List<Partito_TB> getAllPartiti();

	public List<Partito_TB> getAllPartitiElezione(Elezione elezione);
	
}
