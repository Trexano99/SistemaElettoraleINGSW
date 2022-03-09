package useObject.baseElements;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import daoModels.DbTablesRapresentation.Partito_TB;
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
	public static List<Partito> getAllPartitiVotatiInVoto(int idVoto){
		return listTabPartToPart(new PartitoDao().getAllPartitiVotatiVoto(idVoto));
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
	/*
	 * METODO STATICO PER IL SOLO SCOPO DI TESTING!
	 * NON UTILIZZARE AL DI FUORI DEL PACKAGE JUNIT
	 */
	public static Partito createPartitoForTestingJUNIT(int id, String nome) {
		return new Partito(id, nome);
	}
	
	
	@Override
	public int hashCode() {
		return Objects.hash(id);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Partito other = (Partito) obj;
		return id == other.id;
	}

	@Override
	public String toString() {
		return  nome ;
	}
	
	
}
