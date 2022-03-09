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
	
	private /*@ not_null @*/int id;
	
	private /*@ not_null @*/ String nome, /*@ not_null @*/ cognome;
	private /*@ not_null @*/ Date dataNascita;
	
	/*@ 
	 @ assignable id;
	 @ assignable nome;
	 @ assignable cognome;
	 @ assignable dataNascita;
	 @*/
	private Candidato(int id, String nome, String cognome, Date dataNascita) {
		super();
		this.id = id;
		this.nome = nome;
		this.cognome = cognome;
		this.dataNascita = dataNascita;
	}


	/*@ ensures \result == id;
	 @*/
	/*{Context Candidato:: getId()
	 * post: result id}*/
	public int getId() {
		return id;
	}
	/*@ ensures \result == nome;
	 @*/
	/*{Context Candidato:: getNome()
	 * post: result nome}*/
	public String getNome() {
		return nome;
	}
	/*@ ensures \result == cognome;
	 @*/
	/*Context Candidato:: getCognome()
	 * post: result cognome*/
	public String getCognome() {
		return cognome;
	}
	/*@ ensures \result == dataNascita;
	  @*/
	/*Context Candidato:: getDataNascita()
	 * post: result dataNascita*/
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

	/*
	 * METODO STATICO PER IL SOLO SCOPO DI TESTING!
	 * NON UTILIZZARE AL DI FUORI DEL PACKAGE JUNIT
	 */
	public static Candidato createCandidatoForTestingJUNIT(int id, String nome, String cognome, Date dataNascita) {
		return new Candidato(id, nome, cognome, dataNascita);
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
