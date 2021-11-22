package assignment;

public class TestingClass {
	public static void main (String[] args) {
		int[] nascita ={21,2,1980};
		Elettore elettoreItaliano = assignment.Elettore.italianElettore(
				"Mario",
				"Bianchi",
				nascita,
				ComuneItaliano.getComuneFromName("Gallarate"),
				true);
		int[] nascita2 ={21,2,2002};
		Elettore elettoreStraniero = assignment.Elettore.foreignElettore(
				"Mario",
				"Bianchi",
				nascita2,
				Nazione.getNazioneFromName("UgAnda"),
				true);
		elettoreStraniero.esprimi_voto();
		System.out.println(elettoreItaliano.getCodiceFiscale());
		System.out.println(elettoreStraniero.getCodiceFiscale());
		//Elettore giusto------------------------------------------------------------
		int[] data = {5,5,1998};
		//Elettore prova = assignment.Elettore.foreignElettore("Shanti","Ayala", data, "Svizzera",false); 
		//System.out.println(prova.toString());
		//Elettore nome nullo--------------------------------------------------------
		//Elettore prova2 = nassignment.Elettore.foreignElettore(null,"Ayala", data, null, "Svizzera",false);
		//System.out.println(prova2.toString());
		//Elettore cognome nullo------------------------------------------------------
		//String cognom = null;
		//Elettore prova3 = assignment.Elettore.foreignElettore("Shanti",cognom, data, null, "Svizzera",false);
		//System.out.println(prova3.toString());
		//Elettore italiano senza comune -----------------------------------------------
		//Elettore prova4 = assignment.Elettore("Shanti","Ayala", data, null, "italia",false);
		//System.out.println(prova4.toString());
		//Elettore Minorenne ---------------------------------------------------------
		//int[] data2 = {5,5,2020};
		//Elettore prova5 = assignment.Elettore.foreignElettore("Shanti","Ayala", data2, null, "svizzera",false);
		//System.out.println(prova5.toString());
	}

}
