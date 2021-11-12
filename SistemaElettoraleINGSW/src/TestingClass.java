import java.time.LocalDate;

import assignment.ComuneItaliano;
import assignment.Elettore;
import assignment.Nazione;

public class TestingClass {
	
	public static void main (String[] args) {
			Elettore elettoreItaliano = assignment.Elettore.italianElettore(
					"Mario",
					"Bianchi",
					LocalDate.of(1980, 2, 21),
					ComuneItaliano.getComuneFromName("Gallarate"),
					true);
			Elettore elettoreStraniero = assignment.Elettore.foreignElettore(
					"Mario",
					"Bianchi",
					LocalDate.of(2002, 2, 21),
					Nazione.getNazioneFromName("UgAnda"),
					true);
			elettoreStraniero.esprimi_voto();
			System.out.println(elettoreItaliano.getCodiceFiscale());
			System.out.println(elettoreStraniero.getCodiceFiscale());
		}
}
