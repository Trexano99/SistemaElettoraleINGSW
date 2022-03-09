package useObject.voteElements;


public abstract class Votazione {
	
	private int id;
	
	protected /*@not_null@*/String nome;
	protected boolean isClosed;
	protected boolean isFinished;
	protected /*@not_null@*/TipologiaElezione tipoElezione;
	private Boolean hasLoggedElettoreVotedFor = null;
	/*@
	 @ assignable id;
	 @ assignable nome;
	 @ assignable isClosed;
	 @ assignable isFinished;
	 @ assignable tipoElezione;
	 @*/
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

	/*@ ensures \result == id;
	 @*/
	public int getId() {
		return id;
	}
	/*@ ensures \result == nome;
	 @*/
	public String getNome() {
		return nome;
	}
	/*@ ensures \result == isClosed;
	 @*/
	public boolean isClosed() {
		return isClosed;
	}
	/*@ ensures \result == isFinished;
	 @*/
	public boolean isFinished() {
		return isFinished;
	}
	/*@ ensures \result == tipoElezione;
	 @*/
	public TipologiaElezione getTipoElezione() {
		return tipoElezione;
	}
	public Boolean getHasLoggedElettoreVotedFor() {
		return hasLoggedElettoreVotedFor;
	}
	protected void setHasLoggedElettoreVotedFor(Boolean hasLoggedElettoreVotedFor) {
		this.hasLoggedElettoreVotedFor = hasLoggedElettoreVotedFor;
	}
	
	public String getIsClosedStr() {
		if(isClosed)
			return "CHIUSA";
		return "APERTA";
	}
	public String getIsFinishedStr() {
		if(isFinished)
			return "TERMINATA";
		return "NON TERMINATA";
	}
	public String getTipoElezioneStr() {
		switch (tipoElezione) {
		case Referendum:
			return "REFERENDUM";
		case VotazioneCategorica:
			return "VOTAZIONE CATEGORICA";
		case VotazioneCategoricaConPref:
			return "VOTAZIONE CATEGORICA CON PREFERENZA";
		case VotazioneOrdinale:
			return "VOTAZIONE ORDINALE";
		default:
			return "UNDEFINED";
		}
	}
	
	
}
