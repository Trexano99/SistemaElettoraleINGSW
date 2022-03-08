package useObject.baseElements;

import java.sql.Date;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import daoModels.DbTablesRapresentation.Candidato_TB;
import daoModels.ImplTablesDao.CandidatoDao;
import useObject.voteElements.Elezione;

public class Candidato {
	
	private int id;
	
	private String nome, cognome;
	private Date dataNascita;
	
	
	private Candidato(int id, String nome, String cognome, Date dataNascita) {
		super();
		this.id = id;
		this.nome = nome;
		this.cognome = cognome;
		this.dataNascita = dataNascita;
	}


	public int getId() {
		return id;
	}
	public String getNome() {
		return nome;
	}
	public String getCognome() {
		return cognome;
	}
	public Date getDataNascita() {
		return dataNascita;
	}
	
	public static List<Candidato> getAllCandidati(){
		return listTabCandToCand(new CandidatoDao().getAllCandidati());
	}
	public static List<Candidato> getAllCandidatiPartito(Partito partito){	
		return listTabCandToCand(new CandidatoDao().getCandidatiPartito(partito));
	}
	public static List<Candidato> getAllCandidatiElezione(Elezione elezione){
		return listTabCandToCand(new CandidatoDao().getCandidatiElezione(elezione));
	}
	public static List<Candidato> getAllCandidatiVoto(int idVoto){
		return listTabCandToCand(new CandidatoDao().getAllCandidatiVotatiVoto(idVoto));
	}
	
	private static List<Candidato> listTabCandToCand(List<Candidato_TB> candidati){
		List<Candidato> listaCandidati = new ArrayList<Candidato>();
		for (Candidato_TB candidato : candidati) {
			listaCandidati.add(new Candidato(
					candidato.getId(), 
					candidato.getNome(), 
					candidato.getCognome(), 
					candidato.getDataNascita()));
		}		
		return listaCandidati;
	}


	@Override
	public String toString() { 
		DateFormat df = new SimpleDateFormat("dd-MM-yyyy");
		return nome + " " + cognome + " (" + df.format(dataNascita) + ")";
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
		Candidato other = (Candidato) obj;
		return id == other.id;
	}
	
	
	
	
}
