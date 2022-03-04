package daoModels.InterfaceTablesDao;

import daoModels.DbTablesRapresentation.Elettore_TB;

public interface IElettoreDao {
	
	public Elettore_TB get(String elettoreId);
	
}
