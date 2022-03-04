package useObject.voteElements;

import java.util.ArrayList;
import java.util.List;

import daoModels.DbTablesRapresentation.Referendum_TB;
import daoModels.ImplTablesDao.ReferendumDao;

public class Referendum extends Votazione {

	private Boolean withQuorum;
	private String quesito;
	

	private Referendum(int id, String nome, boolean isClosed, boolean isFinished, TipologiaElezione tipoElezione,
			Boolean withQuorum, String quesito) {
		super(id, nome, isClosed, isFinished, tipoElezione);
		this.withQuorum = withQuorum;
		this.quesito = quesito;
	}
	
	public Boolean withQuorum() {
		return withQuorum;
	}
	public String getQuesito() {
		return quesito;
	}
	
	static public List<Referendum> getAllReferendums(){
		List<Referendum> tuttiRefer = new ArrayList<Referendum>();
		List<Referendum_TB> listaRefer =  new ReferendumDao().getAllReferendums();
		for (Referendum_TB referendum_TB : listaRefer) {
			tuttiRefer.add(new Referendum(
					referendum_TB.getId(), 
					referendum_TB.getNomeBreve(), 
					referendum_TB.getIsClosed(), 
					referendum_TB.getIsFinished(), 
					referendum_TB.getTipoElezione(),
					referendum_TB.getWithQuorum(),
					referendum_TB.getQuesito()));
		}
		return tuttiRefer;
	}
	
}
