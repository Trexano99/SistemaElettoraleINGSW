package assignment;

//import java.time.LocalDate;

/**
* Questa classe rappresenta un Elettore del sistema di voto.
* 
* @author Massimiliano Visconti
*
*/
public class Elettore {
	/*@public invariant Nome!= null;
	  @public invariant Cognome!= null;
	  @*/
	public final String Nome;
	public final String Cognome;
	//public final LocalDate DataNascita; 
	public int[] DataNascita = new int [3]; //dn[0] = giorno, dn[1] = mese, dn[2] = anno
	public final ComuneItaliano ComuneNascita;
	public final Nazione NazioneNascita;
	/**
	 * Indica se l'elettore rappresentato è Maschio. 
	 * Nel caso sia falso esso è Donna.
	 */
	public final boolean IsMale;
	
	private char[] codiceFiscale = null;
	private /*@ spec_public @*/ boolean asVoted = false;
	
	private int[] dataOdierna = {23,11,2021};
	
	/**
	 * Ritorna il codice fiscale calcolato dell'elettore
	 * @return
	 */
	//@ensure codiceFiscale != null;
	public String getCodiceFiscale() {
		return String.valueOf(codiceFiscale);	
	}
	
	/**
	 * Indica se l'elettore ha già votato {@code true}, altrimenti {@code false} .
	 * @return
	 */
	
	//@ensure \result = asVoted;
	public boolean asAlreadyVoted() {
		return asVoted;	
	}
	
	//@requires DataNascita != null;
	private boolean canVote(){
		/*LocalDate firstDate = DataNascita;
		LocalDate secondDate = LocalDate.now();
		return Period.between(firstDate, secondDate).getYears()>18;*/
		return true; //if Elettore e' maggiorenne;
	}
	
	
	/*@requires !(nome.isEmpty());
	 @requires !(cognome.isEmpty());
	 @requires dataNascita != null;
	 @requires comuneNascita != null;
	 @requires nazioneNascita != null;
	 @*/
	private Elettore(String nome, String cognome, int[] dataNascita, ComuneItaliano comuneNascita, Nazione nazioneNascita,
			boolean isMale) {
		if(/*nome.isBlank()*/isBlank(nome))
			throw new IllegalArgumentException("Il nome non può essere vuoto o nullo");
		if(/*cognome.isBlank()*/isBlank(cognome))
			throw new IllegalArgumentException("Il cognome non può essere vuoto o nullo");
		//if(dataNascita.isAfter(LocalDate.now()))
		if(isAfter(dataNascita,dataOdierna))
			throw new IllegalArgumentException("La data di nascita non può essere successiva alla data attuale");
		if(nazioneNascita.equals(Nazione.NazioneIta)&&comuneNascita==null)
			throw new IllegalArgumentException("Il comune di nascita non può essere nullo se la nazione è Italiana");
		Nome = nome.trim();
		Cognome = cognome.trim();
		DataNascita = dataNascita;
		ComuneNascita = comuneNascita;
		NazioneNascita = nazioneNascita;
		IsMale = isMale;
		generateCodiceFiscale();
	}
	
	//metodo messo perchè non esiste in java7
		private boolean isBlank(String string) {
		    return  string.trim().isEmpty();
		}
		//@requires dataNascita!= null;
		//@requires dataNascita.length==dataOdiera.length;
		private boolean isAfter(int[] dataNascita, int[] dataOdierna){
			if(dataNascita[2]>dataOdierna[2])
				return true;
			else if(dataNascita[2]==dataOdierna[2])
				if(dataNascita[1]>dataOdierna[1])
					return true;
					else if (dataNascita[1]==dataOdierna[1] && dataNascita[0]>dataOdierna[0])
						return true;
			return false;
		}
	
	/**
	 * Permette di ottenere un'istanza di Elettore straniero
	 * 
	 * @param nome Nome dell'elettore
	 * @param cognome Cognome dell'elettore 
	 * @param dataNascita Data di nascita dell'elettore  
	 * @param nazioneNascita Nazione di nascita dell'elettore 
	 * @param isMale {@code true} se l'elettore è maschio, false altrimenti
	 * @return Elettore con gli opportuni parametri
	 */
	//@requires !nazioneNascita.equals(Nazione.NazioneIta);
	//@ensures comuneNascita ==null;	
	public static Elettore foreignElettore(String nome, String cognome, int[] dataNascita, Nazione nazioneNascita,boolean isMale) {
		return new Elettore(nome, cognome, dataNascita, null, nazioneNascita, isMale);
	}
	
	/**
	 * Permette di ottenere un'istanza di Elettore italiano
	 * 
	 * @param nome Nome dell'elettore
	 * @param cognome Cognome dell'elettore 
	 * @param dataNascita Data di nascita dell'elettore 
	 * @param comune Comune di nascita dell'elettore 
	 * @param isMale {@code true} se l'elettore è maschio, false altrimenti
	 * @return Elettore con gli opportuni parametri
	 */
	//@requires comune!=null;
	//@ensures nazioneNascita.equals(Nazione.NazioneIta);
	public static Elettore italianElettore(String nome, String cognome, int[] dataNascita, ComuneItaliano comune,boolean isMale) {
		return new Elettore(nome, cognome, dataNascita, comune, Nazione.NazioneIta, isMale);
	}
	
	//@requires Nome != null && Cognome != null && DataNascita != null && NazioneNascita != null;
	//@ensures (codiceFiscale != null && codiceFiscale.length == 16);
	private void generateCodiceFiscale() {		
		codiceFiscale=CodiceFiscale.generateCodiceFiscale(this);
	}
	
	/**
	 * Permette all'elettore di esprimere il voto
	 * @throws IllegalStateException Se l'elettore ha un'età non sufficiente per esprimere il voto o ha già votato
	 */
	//@requires asVoted == false;
	//@ensures (asVoted == true && !(\old(asVoted))==asVoted);
	//@signals (IllegalStateException e);
	public void esprimi_voto() throws IllegalStateException {
		if (asVoted)
			throw new IllegalStateException("Il seguente elettore ha già votato");
		else if(canVote())
			asVoted = true;
		else
			throw new IllegalStateException("Un elettore non può votare se minorenne");
	}
	
	public String toString() {
		   String s = "nome=" + Nome + "; ";
		   s = s + "cognome=" + Cognome + "; ";
		   s = s + "datanascita=" + DataNascita[0]+"/"+ DataNascita[1]+"/" +DataNascita[2] + "; ";
		   s = s + "comune=" + ComuneNascita + "; ";
		   s = s + "nazione=" + NazioneNascita + "; ";
		   if(IsMale){
			   s = s + "sesso=" + "Maschio" + "; ";
		   }else{
			   s = s + "sesso=" + "Femmina" + "; ";
		   }
		   return s;
		}
}


