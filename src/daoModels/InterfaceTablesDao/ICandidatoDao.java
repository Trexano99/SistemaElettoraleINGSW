package daoModels.InterfaceTablesDao;

import java.util.List;

import daoModels.DbTablesRapresentation.Candidato_TB;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;

public interface ICandidatoDao {
	
	public List<Candidato_TB>getAllCandidati();

	public List<Candidato_TB>getCandidatiPartito(Partito partito);
	
	public List<Candidato_TB>getCandidatiElezione(Elezione partito);

}
