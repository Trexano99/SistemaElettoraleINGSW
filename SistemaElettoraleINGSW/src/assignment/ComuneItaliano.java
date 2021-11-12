package assignment;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.json.simple.JSONArray;
import org.json.simple.JSONObject;
import org.json.simple.parser.JSONParser;

/**
 * Questa classe rappresenta un comune Italiano.
 * 
 * <p>
 * Essa contiene le informazioni base dello stesso, di cui il {@link #Nome} 
 * e il {@link #CodiceCatastale}.
 * 
 * <p>
 * Sarà possibile che la classe venga poi estesa di altre informazioni per 
 * rappresentare il comune in una maniera migliore
 * 
 * 
 * @author Massimiliano Visconti
 *
 */
public class ComuneItaliano {
	/**
	 * Il nome del comune
	 */
	public final String Nome;
	/**
	 * Il codice catastale del comune. Utile ad esempio per 
	 * la generazione del codice fiscale.
	 */
	public final String CodiceCatastale;
	
	/*Instanziato come privato per rendere possibile la generazione
	degli stessi solo tramite il metodo statico getAllComuni che 
	li crea a partire dal file esistente*/
	private ComuneItaliano(String nome, String codiceCatastale) {
		super();
		Nome = nome;
		CodiceCatastale = codiceCatastale;
	}
	
	/**
	 * Insieme di tutti i comuni generati a partire dal file
	 * esistente dell'Istat che può anche essere aggiornato nel caso 
	 * di eventuali cambiamenti.
	 * 
	 * @return Lista di comuni
	 */
	public static final List<ComuneItaliano> AllComuni = uploadAllComuni();
	
	@SuppressWarnings("unchecked")
	private static List<ComuneItaliano> uploadAllComuni() {
		List<ComuneItaliano> listaFinale = new ArrayList<ComuneItaliano>();
		
		JSONParser jsonParser = new JSONParser();
         
	        try (FileReader reader = new FileReader("C:\\Users\\visco\\git\\SistemaElettoraleINGSW\\SistemaElettoraleINGSW\\src\\assignment\\comuniItaliani.json"))
	        {
	            Object obj = jsonParser.parse(reader);
	 
	            JSONArray comuniList = (JSONArray) obj;

	            comuniList.forEach( comune -> listaFinale.add(parseComuneObject( (JSONObject) comune )) );
	 
	        } catch (FileNotFoundException e) {
	            e.printStackTrace();
	        } catch (IOException e) {
	            e.printStackTrace();
	        } catch (org.json.simple.parser.ParseException e) {
				e.printStackTrace();
			}
	        
	   return listaFinale;
	}
	
	/**
	 * Permette di ottenere il comune con il nome passato come parametro
	 * @param nomeComune nome del comune da estrarre
	 * @return comune estratto o {@code null} se la ricerca non ha prodotto risultati
	 */
	public static ComuneItaliano getComuneFromName(String nomeComune) {
		for (ComuneItaliano comune:AllComuni)
			if (comune.Nome.toLowerCase().equals(nomeComune.toLowerCase()))
				return comune;
		return null;
	}
	
	
	private static ComuneItaliano parseComuneObject(JSONObject comune) 
    {
        return new ComuneItaliano((String) comune.get("nome"), (String) comune.get("codiceCatastale"));   
    }
}
