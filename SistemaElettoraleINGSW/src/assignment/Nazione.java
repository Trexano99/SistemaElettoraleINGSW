package assignment;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import org.json.simple.JSONArray;
import org.json.simple.JSONObject;
import org.json.simple.parser.JSONParser;

/**
 * Questa classe rappresenta una Nazione nel mondo.
 * 
 * <p>
 * Essa contiene le informazioni base dello stesso, di cui il {@link #Nome} 
 * e la {@link #Sigla}.
 * 
 * <p>
 * Sar� possibile che la classe venga poi estesa di altre informazioni per 
 * rappresentare la nazione in una maniera migliore
 * 
 * 
 * @author Massimiliano Visconti
 *
 */
public class Nazione {

	/**
	 * Nome della nazione
	 */
	public final String Nome ;
	/**
	 * Codice della nazione
	 */
	public final String CountryCode;
	
	/*Instanziato come privato per rendere possibile la generazione
	degli stessi solo tramite il metodo statico getAllNazioni che 
	li crea a partire dal file esistente*/
	private Nazione(String nome, String codiceNazione) {
		Nome = nome;
		CountryCode = codiceNazione;
	}
	
	/**
	 * Insieme di tutte le nazioni generate a partire dal file
	 * esistente che pu� anche essere aggiornato nel caso 
	 * di eventuali cambiamenti.
	 * 
	 * @return Lista Nazioni
	 */
	public static final List<Nazione> AllNazioni = uploadAllNazioni();
	
	/**
	 * Permette di ottenere la nazione con il nome passato come parametro
	 * @param nomeNazione nome della nazione da estrarre
	 * @return nazione estratta o {@code null} se la ricerca non ha prodotto risultati
	 */
	public static Nazione getNazioneFromName(String nomeNazione) {
		for (Nazione nazione:AllNazioni)
			if ((nazione.Nome).toLowerCase().equals(nomeNazione.toLowerCase()))
				return nazione;
		return null;
	}

	@SuppressWarnings("unchecked")
	private static List<Nazione> uploadAllNazioni() {
		List<Nazione> listaFinale = new ArrayList<Nazione>();
		
		JSONParser jsonParser = new JSONParser();
         
	        try (FileReader reader = new FileReader("C:\\Users\\visco\\git\\SistemaElettoraleINGSW\\SistemaElettoraleINGSW\\src\\assignment\\nazioniMondo.json"))
	        {
	            Object obj = jsonParser.parse(reader);
	 
	            JSONArray nazioniList = (JSONArray) obj;

	            nazioniList.forEach( nazione -> listaFinale.add(parseNazioneObject( (JSONObject) nazione)) );
	 
	        } catch (FileNotFoundException e) {
	            e.printStackTrace();
	        } catch (IOException e) {
	            e.printStackTrace();
	        } catch (org.json.simple.parser.ParseException e) {
				e.printStackTrace();
			}
	        
	   return listaFinale;
	}
	
	private static Nazione parseNazioneObject(JSONObject nazione) 
    {
		if(nazione.get("italian_country_code")==null)
			return new Nazione((String) nazione.get("english_country_name"), null);   
        return new Nazione((String) nazione.get("english_country_name"), (String) nazione.get("italian_country_code"));   
    }
	
	/**
	 * La nazione italiana
	 * @return nazione italiana
	 */
	public static final Nazione NazioneIta = genNazioneIta();

	private static Nazione genNazioneIta() {
		for(Nazione n: AllNazioni)
			if(n.Nome.equals("Italy"))
				return n;
		return null;
	}

	@Override
	public int hashCode() {
		return Objects.hash(Nome);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Nazione other = (Nazione) obj;
		return Objects.equals(Nome, other.Nome);
	}
	
	
}