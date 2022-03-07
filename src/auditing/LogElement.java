package auditing;

import java.lang.reflect.Array;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Date;

/***
 * Un elemento di log
 * 
 * @author Massimiliano Visconti
 *
 */
public class LogElement {

	private Date date;
	private Object logSource;
	private String logName;
	private String logDetails;
	private Boolean isError = false;
	
	public Boolean getIsError() {
		return isError;
	}
	/***
	 * Permette di costruire un elemento di log con tutte le informazioni necessarie. 
	 * 
	 * @param logSource
	 * @param logName
	 * @param logDetails
	 */
	public LogElement(Object logSource, String logName, String logDetails) {
		date = new Date();
		this.logSource = logSource;
		this.logName = logName;
		this.logDetails = logDetails;
	}
	public LogElement(Object logSource, String logName, String logDetails,Boolean isError) {
		date = new Date();
		this.logSource = logSource;
		this.logName = logName;
		this.logDetails = logDetails;
		this.isError = isError;
	}

	/***
	 * Permette una stampa dettagliata dell'evento di log
	 */
	@Override
	public String toString() {
		DateFormat df = new SimpleDateFormat("dd/MM/yyyy HH:mm:ss");
		if(!isError)
			return (df.format(date))+" - ["+logSource.getClass().toString()+"]  "+logName+" : "+logDetails;
		else
			return (df.format(date))+" - !!! ERROR !!! ["+logSource.getClass().getSimpleName()+"]  "+logName+" : "+logDetails;
	}
	

}
