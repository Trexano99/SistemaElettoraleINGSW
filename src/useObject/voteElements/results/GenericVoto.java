package useObject.voteElements.results;

public class GenericVoto {

	private String nominativo;
	private String numeroVoti;
	
	public GenericVoto(String nominativo, String numeroVoti) {
		this.nominativo = nominativo;
		this.numeroVoti = numeroVoti;
	}
	
	public String getNominativo() {
		return nominativo;
	}
	public String getNumeroVoti() {
		return numeroVoti;
	}
	
}
