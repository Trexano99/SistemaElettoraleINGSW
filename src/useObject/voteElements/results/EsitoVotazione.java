package useObject.voteElements.results;

public abstract class EsitoVotazione {

	private int numeroSchedeBianche;
	private int numeroSchedeTotali;
	
	
	protected EsitoVotazione(int numeroSchedeBianche, int numeroSchedeTotali) {
		this.numeroSchedeBianche = numeroSchedeBianche;
		this.numeroSchedeTotali = numeroSchedeTotali;
	}


	public int getNumeroSchedeBianche() {
		return numeroSchedeBianche;
	}
	public int getNumeroSchedeValide() {
		return numeroSchedeTotali- numeroSchedeBianche;
	}
	public int getNumeroSchedeTotali() {
		return numeroSchedeTotali;
	}
	
}
