package useObject.voteElements;

public abstract class Votazione {
	
	private int id;
	
	protected String nome;
	protected boolean isClosed;
	protected boolean isFinished;
	protected TipologiaElezione tipoElezione;
	
	protected Votazione(int id, String nome, boolean isClosed, boolean isFinished, TipologiaElezione tipoElezione) {
		this.id = id;
		this.nome = nome;
		this.isClosed = isClosed;
		this.isFinished = isFinished;
		this.tipoElezione = tipoElezione;
	}
	
	public enum TipologiaElezione{
		Referendum,
		VotazioneCategorica,
		VotazioneCategoricaConPref,
		VotazioneOrdinale		
	}


	public int getId() {
		return id;
	}
	public String getNome() {
		return nome;
	}
	public boolean isClosed() {
		return isClosed;
	}
	public boolean isFinished() {
		return isFinished;
	}
	public TipologiaElezione getTipoElezione() {
		return tipoElezione;
	}
	
	
	
}
