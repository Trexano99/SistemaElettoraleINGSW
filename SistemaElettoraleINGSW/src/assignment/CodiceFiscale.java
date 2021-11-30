package assignment;

import java.time.format.DateTimeFormatter;
import java.util.*;


/**
 * Questa classe astratta mette a disposizione un metodo statico per 
 * la generazione del codice fiscale, passato come parametro un Elettore.
 * 
 * @author Massimiliano Visconti
 *
 */
public abstract class CodiceFiscale {
	
	/**
	 * Permette di ottenere il codice fiscale di un Elettore passato
	 * come parametro, sotto forma di Lista di caratteri.
	 * @param elettore	Elettore del quale si vuole ottenere il codice fiscale
	 * @return	Codice fiscale calcolato 
	 */
	public static char[] generateCodiceFiscale(Elettore elettore) {
		ArrayList<Character> codiceFinale = new ArrayList<Character>();
		codiceFinale.addAll(getWordForCF(elettore.Cognome, false));
		codiceFinale.addAll(getWordForCF(elettore.Nome.split(",")[0], true));
		codiceFinale.addAll(convertStringToCharList(elettore.DataNascita.format(DateTimeFormatter.ofPattern("yy"))));
		codiceFinale.add(monthToCFLetter(elettore.DataNascita.getMonthValue()));
		codiceFinale.addAll(dayToCFLetters(elettore.DataNascita.getDayOfMonth(),elettore.IsMale));
		if(elettore.ComuneNascita!=null)
			codiceFinale.addAll(convertStringToCharList(elettore.ComuneNascita.CodiceCatastale));
		else
			codiceFinale.addAll(convertStringToCharList(elettore.NazioneNascita.CountryCode));
		codiceFinale.add(calcoloCarattereControllo(codiceFinale));
		return listToCharArray(codiceFinale);
	}
	//@return (\forall int i; i>= 0 && i< list.length;  \result = (char)list.get(i));
	private static char[] listToCharArray (ArrayList<Character> list){
		char[] myCharArray = new char[list.size()];
		for(int i = 0; i < list.size(); i++)
		    myCharArray[i] = (char)list.get(i);
		return myCharArray;
	}
	
	private static ArrayList<Character> getWordForCF(String parola, boolean isForName){
		final ArrayList<Character> vocali = new ArrayList<Character>(Arrays.asList('A','E','I','O','U'));
		ArrayList<Character> vocaliParola = new ArrayList<Character>();
		ArrayList<Character> consonantiParola = new ArrayList<Character>();
		ArrayList<Character> risultato = new ArrayList<Character>();
		for (char c : parola.toCharArray()) 
			if (vocali.contains(Character.toUpperCase(c)))
				vocaliParola.add(Character.toUpperCase(c));
			else
				consonantiParola.add(Character.toUpperCase(c));
		if (isForName&&consonantiParola.size()>3)
			consonantiParola.remove(1);
		do {
			if (consonantiParola.size()>0)
				risultato.add(consonantiParola.remove(0));
			else if(vocaliParola.size()>0)
				risultato.add(vocaliParola.remove(0));
			else 
				risultato.add('X');
		}while(risultato.size()<3);
		return risultato; 
	}
	/*@
	 @requires  ((month<6&& \result == (char)('A'+(month-1)) &&
	 @		(month=6 && \result == 'H') &&
	 @		(month=7 && \result == 'L') &&
	 @		(month=8 && \result == 'M') &&
	 @		(month=9 && \result == 'P') &&
	 @		(month=10 && \result == 'R') &&
	 @		(month=11 && \result == 'S') &&
	 @		(month=7 && \result == 'T') );
	 @*/
	private static char monthToCFLetter(int month) {
		if(month<6)
			return (char)('A'+(month-1));
		else switch (month) {
		case 6: return 'H' ;
		case 7: return 'L' ;
		case 8: return 'M' ;
		case 9: return 'P' ;
		case 10: return 'R' ;
		case 11: return 'S' ;
		case 12: return 'T' ;
		default: throw new IllegalArgumentException("month not expected");
		}
	}
	/*@
	 @requires ( (day>0) && (day<32) );
	 @requires (!isMale ==> day = \old(day)+40 );
	 @requires (day>0 &&day<10) ==> \result char(0).add(Integer.toString(day).charAt(0)) &&
	 @          ( (day>9) && \result = (Integer.toString(day).charAt(0)+Integer.toString(day).charAt(1)) ;
	 @*/
	private static ArrayList<Character> dayToCFLetters (int day, boolean isMale) {
		ArrayList<Character> lettere = new ArrayList<Character>(2);
		if(!isMale)
			day+=40;
		if(day<10) {
			lettere.add('0');
			lettere.add(Integer.toString(day).charAt(0));
		}else {
			lettere.add(Integer.toString(day).charAt(0));
			lettere.add(Integer.toString(day).charAt(1));
		}
		return lettere;
	}
	//@ensures (\forall int i; i>= 0 && i< str.length(); \result = str.toCharArray()));
	private static ArrayList<Character> convertStringToCharList(String str)
    {
        ArrayList<Character> chars = new ArrayList<>();
        for (char ch : str.toCharArray())  
            chars.add(ch);
        return chars;
    }
	
	private static Character calcoloCarattereControllo(ArrayList<Character> codiceFinale) {
		Character c=null;
		String char_posPari="";
		String char_posDispari="";
		int counter=0;
		
		boolean pari = false;
		for(Character charac : codiceFinale){
			if(!pari)
				char_posDispari+=charac; 
			else
				char_posPari+=charac;
			pari=!pari;
		}
		for(Character charac : char_posDispari.toCharArray()){
			switch(charac){
			case '0': counter+=1;break;
			case '1': counter+=0;break;
			case '2': counter+=5;break;
			case '3': counter+=7;break;
			case '4': counter+=9;break;
			case '5': counter+=13;break;
			case '6': counter+=15;break;
			case '7': counter+=17;break;
			case '8': counter+=19;break;
			case '9': counter+=21;break;
			case 'A': counter+=1;break;
			case 'B': counter+=0;break;
			case 'C': counter+=5;break;
			case 'D': counter+=7;break;
			case 'E': counter+=9;break;
			case 'F': counter+=13;break;
			case 'G': counter+=15;break;
			case 'H': counter+=17;break;
			case 'I': counter+=19;break;
			case 'J': counter+=21;break;
			case 'K': counter+=2;break;
			case 'L': counter+=4;break;
			case 'M': counter+=18;break;
			case 'N': counter+=20;break;
			case 'O': counter+=11;break;
			case 'P': counter+=3;break;
			case 'Q': counter+=6;break;
			case 'R': counter+=8;break;
			case 'S': counter+=12;break;
			case 'T': counter+=14;break;
			case 'U': counter+=16;break;
			case 'V': counter+=10;break;
			case 'W': counter+=22;break;
			case 'X': counter+=25;break;
			case 'Y': counter+=24;break;
			case 'Z': counter+=23;break;
			}
		}
		for(Character charac : char_posPari.toCharArray()){
			switch(charac){
			case '0': counter+=0;break;
			case '1': counter+=1;break;
			case '2': counter+=2;break;
			case '3': counter+=3;break;
			case '4': counter+=4;break;
			case '5': counter+=5;break;
			case '6': counter+=6;break;
			case '7': counter+=7;break;
			case '8': counter+=8;break;
			case '9': counter+=9;break;
			case 'A': counter+=0;break;
			case 'B': counter+=1;break;
			case 'C': counter+=2;break;
			case 'D': counter+=3;break;
			case 'E': counter+=4;break;
			case 'F': counter+=5;break;
			case 'G': counter+=6;break;
			case 'H': counter+=7;break;
			case 'I': counter+=8;break;
			case 'J': counter+=9;break;
			case 'K': counter+=10;break;
			case 'L': counter+=11;break;
			case 'M': counter+=12;break;
			case 'N': counter+=13;break;
			case 'O': counter+=14;break;
			case 'P': counter+=15;break;
			case 'Q': counter+=16;break;
			case 'R': counter+=17;break;
			case 'S': counter+=18;break;
			case 'T': counter+=19;break;
			case 'U': counter+=20;break;
			case 'V': counter+=21;break;
			case 'W': counter+=22;break;
			case 'X': counter+=23;break;
			case 'Y': counter+=24;break;
			case 'Z': counter+=25;break;
			}
		}
		switch(counter%26){
		case 0: c='A';break;
		case 1: c='B';break;
		case 2: c='C';break;
		case 3: c='D';break;
		case 4: c='E';break;
		case 5: c='F';break;
		case 6: c='G';break;
		case 7: c='H';break;
		case 8: c='I';break;
		case 9: c='J';break;
		case 10: c='K';break;
		case 11: c='L';break;
		case 12: c='M';break;
		case 13: c='N';break;
		case 14: c='O';break;
		case 15: c='P';break;
		case 16: c='Q';break;
		case 17: c='R';break;
		case 18: c='S';break;
		case 19: c='T';break;
		case 20: c='U';break;
		case 21: c='V';break;
		case 22: c='W';break;
		case 23: c='X';break;
		case 24: c='Y';break;
		case 25: c='Z';break;
		}
		return c;
	}
}
