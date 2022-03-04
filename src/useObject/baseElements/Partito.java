package useObject.baseElements;

import java.util.ArrayList;
import java.util.List;

import daoModels.DbTablesRapresentation.Candidato_TB;
import daoModels.DbTablesRapresentation.Partito_TB;
import daoModels.ImplTablesDao.CandidatoDao;
import daoModels.ImplTablesDao.PartitoDao;
import useObject.voteElements.Elezione;

public class Partito {
	
	private int id;
	private String nome;
	private List<Candidato> candidatiPartito = new ArrayList<Candidato>();
	
	private Partito(int id, String nome) {
		super();
		this.id = id;
		this.nome = nome;
	}

	public int getId() {
		return id;
	}
	public String getNome() {
		return nome;
	}
	public List<Candidato> getCandidatiPartito() {
		return candidatiPartito;
	}
	
	private void addPartitoCandidati(List<Candidato> candidati) {
		this.candidatiPartito = candidati;
	}
	

	public static List<Partito> getAllPartiti(){
		return listTabPartToPart(new PartitoDao().getAllPartiti());
	}
	public static List<Partito> getAllPartitiElezione(Elezione elezione){
		return listTabPartToPart(new PartitoDao().getAllPartitiElezione(elezione));
	}
	private static List<Partito> listTabPartToPart(List<Partito_TB> partiti){
		List<Partito> listaPartiti = new ArrayList<Partito>();
		for (Partito_TB partito : partiti) {
			Partito p = new Partito(
					partito.getId(),
					partito.getNome()
					);
			p.addPartitoCandidati(Candidato.getAllCandidatiPartito(p));
			listaPartiti.add(p);
			
		}		
		return listaPartiti;
	}
	
	
}
