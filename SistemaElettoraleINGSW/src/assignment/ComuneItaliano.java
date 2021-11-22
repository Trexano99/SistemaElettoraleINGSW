package assignment;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.json.JSONArray;
import org.json.JSONObject;



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
	
	private static String fileComuni = ".//FileJson//comuniItaliani.json";
	
	/**
	 * Il nome del comune
	 */
	//@public invariant Nome!= null;
	public final String Nome;
	/**
	 * Il codice catastale del comune. Utile ad esempio per 
	 * la generazione del codice fiscale.
	 */
	//@public invariant CodiceCatastale!= null;
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
        String fullContent;
        
		try {
			fullContent = new String(Files.readAllBytes( Paths.get(fileComuni)));
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
        
        JSONArray comuniList = new JSONArray(fullContent);
        for(int i = 0; i<comuniList.length();i++)
        	listaFinale.add(parseComuneObject((JSONObject)comuniList.get(i)));
        
	        
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
