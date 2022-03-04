package auditing;

import java.util.ArrayList;
import java.util.List;

/***
 * Questa classe (Singleton) mantiene traccia di tutte le attività che
 * avvengono all'interno del sistema di voto sviluppato.
 * Esso 
 * 
 * @author Massimiliano Visconti
 *
 */
public class LogHistory {
	
	private static final String ANSI_RESET = "\u001B[0m";
	private static final String ANSI_RED = "\u001B[31m";
	
	private static LogHistory instance = null;
	
	public static LogHistory getInstance() {
		if (instance==null)
			instance = new LogHistory();
		return instance;
	}
	
	private LogHistory() {
		System.out.println("**** LOGGING DI SISTEMA DI VOTO ELETTRONICO ****");
		allLogs = new ArrayList<LogElement>();
	}
	
	private List<LogElement> allLogs;
	
	public void addLog(LogElement elemento) {
		allLogs.add(elemento);
		if(elemento.getIsError())
			System.out.println(ANSI_RED +elemento+ANSI_RESET);
		else
			System.out.println(elemento);
	}

}