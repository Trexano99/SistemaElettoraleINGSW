package daoModels.InterfaceTablesDao;

import java.util.List;

import daoModels.NewReferendum;
import daoModels.ReferendumUpdater;
import daoModels.DbTablesRapresentation.Referendum_TB;
import useObject.voteElements.Referendum;

public interface IReferendumDao {

	public List<Referendum_TB> getAllReferendums();
	
	public boolean addNewReferendum(NewReferendum referendum);
	
	public boolean removeReferendum(Referendum referendum);

	public boolean updateReferendum(ReferendumUpdater referendum);
	
	
}
