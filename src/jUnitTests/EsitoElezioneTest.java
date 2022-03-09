package jUnitTests;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.sql.Date;
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import daoModels.ElezioneVote;
import useObject.baseElements.Candidato;
import useObject.baseElements.Partito;
import useObject.voteElements.Elezione;
import useObject.voteElements.Votazione.TipologiaElezione;
import useObject.voteElements.results.EsitoElezione;
import useObject.voteElements.results.GenericVoto;

public class EsitoElezioneTest {

	/*
	 * Il seguente test ha lo scopo di andare a testare il corretto
	 * funzionamento della funzione getEsitoElezioneForJUnitTesting.
	 * Questa funzione è stata appositamente creata per il testing 
	 * ed è stato necessario fare così in quanto i dati vengono 
	 * altrimenti direttamente presi da DB e si rischiava non 
	 * venissero soddisfatti tutti i criteri di test.
	 * La funzione riporta le stesse operazioni eseguite dalla duale
	 * funzione getEsitoElezione.
	 * 
	 * Il test serve a verificare il corretto calcolo delle somme
	 * dei voti rilasciati dagli utenti.
	 * 
	 * La copertura è stata testata con il criterio del branch 
	 * coverage e sono statai testati tutti i casi limite della
	 * funzione stessa.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 100%
	 */
	@Test
	public void testEsitoElezione() {
		testEsitoElezione_NoVotes();
		testEsitoElezione_OnlyWhiteVotes();
		testEsitoElezione_NullVotes();
		testEsitoElezione_SignleVotazioneCategoricaPartCand();
		testEsitoElezione_MultVotazioneCategoricaPartCand();
		testEsitoElezione_SignleVotazioneOrdPartCand();
		testEsitoElezione_MultVotazioneOrdPartCand();
		testEsitoElezione_VotazioneOrdMolPartEMolCand();
		testEsitoElezione_MolVotazioneOrdMolPartEMolCand();
		testEsitoElezione_InvalidVotazione();
		try {
			testEsitoElezione_TipologiaElezioneReferendumErrata();
		}catch(Exception e){
			//TUTTO OK
		}
	}
	
	
	/*
	 * Serve per testare lo skip di tutte le condizioni di ciclo
	 * nel caso in cui non siano state inserite votazioni.
	 * 
	 * Aspettattive:
	 * 	- Numero schede totali = 0 
	 * 	- Numero schede totali = numero schede bianche + 
	 * 		numero schede valide
	 * 	- Array voti Candidati sia vuoto 
	 * 	- Array voti Partiti sia vuoto 
	 * 
	 * Risultati ottenuti coerenti con le aspettative.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 17.3%
	 * 	  
	 */
	@Test
	public void testEsitoElezione_NoVotes() {
		List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		TipologiaElezione tipo = TipologiaElezione.VotazioneCategorica;
		EsitoElezione esito = EsitoElezione.getEsitoElezioneForJUnitTesting(votiElezione, tipo, null);
		assertEquals(esito.getNumeroSchedeTotali(),0);
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeValide()+esito.getNumeroSchedeBianche());
		assertArrayEquals(esito.getVotiCandidati().toArray(), new GenericVoto[0]);
		assertArrayEquals(esito.getVotiPartiti().toArray(), new GenericVoto[0]);
	}
	
	/*
	 * Serve per testare lo skip di tutte le condizioni di ciclo
	 * nel caso in cui le votazioni siano null.
	 * 
	 * Aspettattive:
	 * 	- Numero schede totali = 1 
	 * 	- Numero schede totali = numero schede bianche + 
	 * 		numero schede valide
	 * 	- Array voti Candidati sia vuoto 
	 * 	- Array voti Partiti sia vuoto 
	 * 
	 * Risultati ottenuti coerenti con le aspettative.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 20.9%
	 * 	  
	 */
	@Test
	public void testEsitoElezione_NullVotes() {
List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		
		Elezione elezione = Elezione.createElezioneForTestingJUNIT(0, 
				null, 
				false, 
				false, 
				TipologiaElezione.VotazioneCategorica, 
				false);
		List<Candidato> candidatiVotati = null;
		List<Partito> partitiVotati = null;
		
		ElezioneVote ev = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev);
		
		EsitoElezione esito = EsitoElezione.getEsitoElezioneForJUnitTesting(votiElezione, elezione.getTipoElezione(), elezione);
		assertEquals(esito.getNumeroSchedeTotali(),1);
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeBianche());
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeValide()+esito.getNumeroSchedeBianche());
		assertArrayEquals(esito.getVotiCandidati().toArray(), new GenericVoto[0]);
		assertArrayEquals(esito.getVotiPartiti().toArray(), new GenericVoto[0]);
	}

	/*
	 * Serve per testare il conteggio dei voti bianchi che sia
	 * coerente con il totale degli stessi
	 * 
	 * Aspettattive:
	 * 	- Numero schede totali = 1 
	 * 	- Numero schede totali = Numero schede bianche
	 * 	- Numero schede totali = numero schede bianche + 
	 * 		numero schede valide
	 * 	- Array voti Candidati sia vuoto 
	 * 	- Array voti Partiti sia vuoto 
	 * 
	 * Risultati ottenuti coerenti con le aspettative.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 22.3%
	 * 	  
	 */
	@Test
	public void testEsitoElezione_OnlyWhiteVotes() {
		List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		
		Elezione elezione = Elezione.createElezioneForTestingJUNIT(0, 
				null, 
				false, 
				false, 
				TipologiaElezione.VotazioneCategorica, 
				false);
		List<Candidato> candidatiVotati = new ArrayList<Candidato>();
		List<Partito> partitiVotati = new ArrayList<Partito>();
		
		ElezioneVote ev = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev);
		
		EsitoElezione esito = EsitoElezione.getEsitoElezioneForJUnitTesting(votiElezione, elezione.getTipoElezione(), elezione);
		assertEquals(esito.getNumeroSchedeTotali(),1);
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeBianche());
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeValide()+esito.getNumeroSchedeBianche());
		assertArrayEquals(esito.getVotiCandidati().toArray(), new GenericVoto[0]);
		assertArrayEquals(esito.getVotiPartiti().toArray(), new GenericVoto[0]);
	}
	
	/*
	 * Serve per testare che esca il corretto messagio di log in
	 * caso di una tipologia elezione errata e che venga sollevata
	 * la opportuna eccezione IllegalStateException.
	 * 
	 * Aspettattive:
	 * 	- IllegalStateException
	 * 	- Messaggio di Log in console che specifica l'errore
	 * 
	 * Risultati ottenuti coerenti con le aspettative.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 15.9%
	 * 	  
	 */
	@Test(expected = IllegalStateException.class)
	public void testEsitoElezione_TipologiaElezioneReferendumErrata() {
		List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		
		Elezione elezione = Elezione.createElezioneForTestingJUNIT(0, 
				null, 
				false, 
				false, 
				TipologiaElezione.Referendum, 
				false);
		List<Candidato> candidatiVotati = new ArrayList<Candidato>();
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(0, null, null, null));
		List<Partito> partitiVotati = new ArrayList<Partito>();

		ElezioneVote ev = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev);
		
		EsitoElezione.getEsitoElezioneForJUnitTesting(votiElezione, elezione.getTipoElezione(), elezione);
		
		fail("Expected exception has not been thrown");
	}
	
	/*
	 * Serve per testare che vengano intrapresi entrambi i cicli
	 * per il conteggio dei voti categorici ma di questi venga solo preso
	 * l'else. Quindi per aggiungere un solo voto partito e un 
	 * solo candidato.
	 * Controlla inoltre che la votazione sia valida.
	 * 
	 * Aspettattive:
	 * 	- Numero schede totali = 1 
	 * 	- Numero schede totali = numero schede bianche + 
	 * 		numero schede valide
	 * 	- Array voti Candidati abbia 1 elemento
	 * 	- Array voti Partiti abbia 1 elemento
	 * 
	 * Risultati ottenuti coerenti con le aspettative.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 51.3%
	 * 	  
	 */
	@Test
	public void testEsitoElezione_SignleVotazioneCategoricaPartCand() {
		List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		
		Elezione elezione = Elezione.createElezioneForTestingJUNIT(0, 
				null, 
				false, 
				false, 
				TipologiaElezione.VotazioneCategoricaConPref, 
				true);
		List<Candidato> candidatiVotati = new ArrayList<Candidato>();
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(0, "Matteo", "Rizzi", new Date(System.currentTimeMillis())));
		List<Partito> partitiVotati = new ArrayList<Partito>();
		partitiVotati.add(Partito.createPartitoForTestingJUNIT(0, "PartitoA"));

		ElezioneVote ev = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev);
		
		EsitoElezione esito = EsitoElezione.getEsitoElezioneForJUnitTesting(votiElezione, elezione.getTipoElezione(), elezione);
		assertEquals(esito.getNumeroSchedeTotali(),1);
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeValide()+esito.getNumeroSchedeBianche());
		assertEquals(esito.getVotiCandidati().size(), 1);
		assertEquals(esito.getVotiPartiti().size(), 1);
	}
	
	/*
	 * Serve per testare che vengano intrapresi entrambi i cicli
	 * per il conteggio dei voti categorici e vengano intraprese per essi 
	 * entrambe le condizioni. Quindi per aggiungere più voti 
	 * allo stesso partito e candidato.
	 * 
	 * Aspettattive:
	 * 	- Numero schede totali = 2 
	 * 	- Numero schede totali = numero schede bianche + 
	 * 		numero schede valide
	 * 	- Array voti Candidati abbia 1 elemento
	 * 	- Array voti Partiti abbia 1 elemento
	 * 
	 * Risultati ottenuti coerenti con le aspettative.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 61.9%
	 * 	  
	 */
	@Test
	public void testEsitoElezione_MultVotazioneCategoricaPartCand() {
		List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		
		Elezione elezione = Elezione.createElezioneForTestingJUNIT(0, 
				null, 
				false, 
				false, 
				TipologiaElezione.VotazioneCategoricaConPref, 
				false);
		List<Candidato> candidatiVotati = new ArrayList<Candidato>();
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(0, "Matteo", "Rizzi", new Date(System.currentTimeMillis())));
		List<Partito> partitiVotati = new ArrayList<Partito>();
		partitiVotati.add(Partito.createPartitoForTestingJUNIT(0, "PartitoA"));

		ElezioneVote ev = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev);
		ElezioneVote ev1 = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev1);
		
		EsitoElezione esito = EsitoElezione.getEsitoElezioneForJUnitTesting(votiElezione, elezione.getTipoElezione(), elezione);
		assertEquals(esito.getNumeroSchedeTotali(),2);
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeValide()+esito.getNumeroSchedeBianche());
		assertEquals(esito.getVotiCandidati().size(), 1);
		assertEquals(esito.getVotiPartiti().size(), 1);
	}
	
	/*
	 * Serve per testare che vengano intrapresi entrambi i cicli
	 * per il conteggio dei voti ordinali ma di questi venga solo preso
	 * l'else. Quindi per aggiungere un solo voto partito e un 
	 * solo candidato
	 * 
	 * Aspettattive:
	 * 	- Numero schede totali = 1 
	 * 	- Numero schede totali = numero schede bianche + 
	 * 		numero schede valide
	 * 	- Array voti Candidati abbia 1 elemento
	 * 	- Array voti Partiti abbia 1 elemento
	 * 
	 * Risultati ottenuti coerenti con le aspettative.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 51.3%
	 * 	  
	 */
	@Test
	public void testEsitoElezione_SignleVotazioneOrdPartCand() {
		List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		
		Elezione elezione = Elezione.createElezioneForTestingJUNIT(0, 
				null, 
				false, 
				false, 
				TipologiaElezione.VotazioneOrdinale, 
				false);
		List<Candidato> candidatiVotati = new ArrayList<Candidato>();
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(0, "Matteo", "Rizzi", new Date(System.currentTimeMillis())));
		List<Partito> partitiVotati = new ArrayList<Partito>();
		partitiVotati.add(Partito.createPartitoForTestingJUNIT(0, "PartitoA"));

		ElezioneVote ev = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev);
		
		EsitoElezione esito = EsitoElezione.getEsitoElezioneForJUnitTesting(votiElezione, elezione.getTipoElezione(), elezione);
		assertEquals(esito.getNumeroSchedeTotali(),1);
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeValide()+esito.getNumeroSchedeBianche());
		assertEquals(esito.getVotiCandidati().size(), 1);
		assertEquals(esito.getVotiPartiti().size(), 1);
	}
	
	/*
	 * Serve per testare che vengano intrapresi entrambi i cicli
	 * per il conteggio dei voti ordinali e vengano intraprese per essi 
	 * entrambe le condizioni. Quindi per aggiungere più voti 
	 * allo stesso partito e candidato.
	 * 
	 * Aspettattive:
	 * 	- Numero schede totali = 2 
	 * 	- Numero schede totali = numero schede bianche + 
	 * 		numero schede valide
	 * 	- Array voti Candidati abbia 1 elemento
	 * 	- Array voti Partiti abbia 1 elemento
	 * 
	 * Risultati ottenuti coerenti con le aspettative.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 64.9%
	 * 	  
	 */
	@Test
	public void testEsitoElezione_MultVotazioneOrdPartCand() {
		List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		
		Elezione elezione = Elezione.createElezioneForTestingJUNIT(0, 
				null, 
				false, 
				false, 
				TipologiaElezione.VotazioneOrdinale, 
				false);
		List<Candidato> candidatiVotati = new ArrayList<Candidato>();
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(0, "Matteo", "Rizzi", new Date(System.currentTimeMillis())));
		List<Partito> partitiVotati = new ArrayList<Partito>();
		partitiVotati.add(Partito.createPartitoForTestingJUNIT(0, "PartitoA"));

		ElezioneVote ev = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev);
		ElezioneVote ev1 = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev1);
		
		EsitoElezione esito = EsitoElezione.getEsitoElezioneForJUnitTesting(votiElezione, elezione.getTipoElezione(), elezione);
		assertEquals(esito.getNumeroSchedeTotali(),2);
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeValide()+esito.getNumeroSchedeBianche());
		assertEquals(esito.getVotiCandidati().size(), 1);
		assertEquals(esito.getVotiPartiti().size(), 1);
	}
	
	/*
	 * Serve per testare che il calcolo dei voti totali 
	 * nella votazione ordinale (in caso siano inseriti 
	 * molteplici partiti o candidati) valga meno del 
	 * singolo voto.
	 * Se inseriti quindi più partiti il primo avrà voto
	 * 1 e gli altri in coda rispettivamente uno sulla
	 * posizione di essi stessi. 
	 * Discorso duale per i candidati.
	 * 
	 * Aspettattive:
	 * 	- Numero schede totali = 1 
	 * 	- Numero schede totali = numero schede bianche + 
	 * 		numero schede valide
	 * 	- Array voti Candidati abbia 3 elementi
	 * 	- Array voti Partiti abbia 2 elementi
	 * 	- Il voto del terzo candidato sia 0,3
	 * 	- Il voto del secondo partito sia 0,5
	 * 
	 * Risultati ottenuti coerenti con le aspettative.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 51.3%
	 * 	  
	 */
	@Test
	public void testEsitoElezione_VotazioneOrdMolPartEMolCand() {
		List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		
		Elezione elezione = Elezione.createElezioneForTestingJUNIT(0, 
				null, 
				false, 
				false, 
				TipologiaElezione.VotazioneOrdinale, 
				false);
		List<Candidato> candidatiVotati = new ArrayList<Candidato>();
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(0, "Matteo", "Rizzi", new Date(System.currentTimeMillis())));
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(1, "Giovanni", "Torta", new Date(System.currentTimeMillis())));
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(2, "Gino", "Strada", new Date(System.currentTimeMillis())));
		List<Partito> partitiVotati = new ArrayList<Partito>();
		partitiVotati.add(Partito.createPartitoForTestingJUNIT(0, "PartitoA"));
		partitiVotati.add(Partito.createPartitoForTestingJUNIT(1, "PartitoB"));

		ElezioneVote ev = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev);
		
		EsitoElezione esito = EsitoElezione.getEsitoElezioneForJUnitTesting(votiElezione, elezione.getTipoElezione(), elezione);
		assertEquals(esito.getNumeroSchedeTotali(),1);
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeValide()+esito.getNumeroSchedeBianche());
		assertEquals(esito.getVotiCandidati().size(), 3);
		assertEquals(esito.getVotiPartiti().size(), 2);
		assertEquals(esito.getVotiCandidati().get(2).getNumeroVoti(), "0,3");
		assertEquals(esito.getVotiPartiti().get(1).getNumeroVoti(), "0,5");
	}
	
	/*
	 * Serve per testare che il calcolo dei voti totali 
	 * nella votazione ordinale rispetti la somma dei 
	 * singoli voti in base all'espressione di voto per 
	 * candidati e partiti secondo l'ordine dato.
	 * Testa inoltre che la votazione sia valida
	 * 
	 * Aspettattive:
	 * 	- Numero schede totali = 2 
	 * 	- Numero schede totali = numero schede bianche + 
	 * 		numero schede valide
	 * 	- Array voti Candidati abbia 4 elementi
	 * 	- Array voti Partiti abbia due elementi
	 * 	- Il voto del terzo candidato sia 0,3
	 * 	- Il voto del secondo partito sia 0,5
	 * 
	 * Risultati ottenuti coerenti con le aspettative.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 64.1%
	 * 	  
	 */
	@Test
	public void testEsitoElezione_MolVotazioneOrdMolPartEMolCand() {
		List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		
		Elezione elezione = Elezione.createElezioneForTestingJUNIT(0, 
				null, 
				false, 
				false, 
				TipologiaElezione.VotazioneOrdinale, 
				false);
		List<Candidato> candidatiVotati = new ArrayList<Candidato>();
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(0, "Matteo", "Rizzi", new Date(System.currentTimeMillis())));
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(1, "Giovanni", "Torta", new Date(System.currentTimeMillis())));
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(2, "Gino", "Strada", new Date(System.currentTimeMillis())));
		List<Partito> partitiVotati = new ArrayList<Partito>();
		partitiVotati.add(Partito.createPartitoForTestingJUNIT(0, "PartitoA"));
		partitiVotati.add(Partito.createPartitoForTestingJUNIT(1, "PartitoB"));

		List<Candidato> candidatiVotati2 = new ArrayList<Candidato>();
		candidatiVotati2.add(Candidato.createCandidatoForTestingJUNIT(1, "Giovanni", "Torta", new Date(System.currentTimeMillis())));
		candidatiVotati2.add(Candidato.createCandidatoForTestingJUNIT(0, "Matteo", "Rizzi", new Date(System.currentTimeMillis())));
		candidatiVotati2.add(Candidato.createCandidatoForTestingJUNIT(3, "Pietro", "Scalzo", new Date(System.currentTimeMillis())));
		List<Partito> partitiVotati2 = new ArrayList<Partito>();
		partitiVotati2.add(Partito.createPartitoForTestingJUNIT(0, "PartitoA"));
		partitiVotati2.add(Partito.createPartitoForTestingJUNIT(1, "PartitoB"));
		partitiVotati2.add(Partito.createPartitoForTestingJUNIT(2, "PartitoC"));

		ElezioneVote ev = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev);
		ElezioneVote ev1 = new ElezioneVote(elezione, candidatiVotati2, partitiVotati2);
		votiElezione.add(ev1);
		
		EsitoElezione esito = EsitoElezione.getEsitoElezioneForJUnitTesting(votiElezione, elezione.getTipoElezione(),elezione);
		assertEquals(esito.getNumeroSchedeTotali(),2);
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeValide()+esito.getNumeroSchedeBianche());
		assertEquals(esito.getVotiCandidati().size(), 4);
		assertEquals(esito.getVotiPartiti().size(), 3);
		assertEquals(esito.getVotiCandidati().get(0).getNumeroVoti(), "1,5");
		assertEquals(esito.getVotiPartiti().get(1).getNumeroVoti(), "1");
		assertEquals(esito.getIsValid(), true);
	}
	
	/*
	 * Serve per testare che una votazione non sia considerata
	 * valida se è a maggioranza assoluta.
	 * Non potendola testare sul numero totale di elettori la si
	 * testa (solo per testing) considerandola valida se il numero
	 * di voti validi è maggiore del numero di schede bianche.
	 * 
	 * Aspettattive:
	 * 	- Numero schede totali = 3
	 * 	- Numero schede totali = numero schede bianche + 
	 * 		numero schede valide
	 * 	- Array voti Candidati abbia 1 elemento
	 * 	- Array voti Partiti abbia 1 elemento
	 * 	- VotoIsValid sia false
	 * 
	 * Risultati ottenuti coerenti con le aspettative.
	 * 
	 * Copertura di:
	 * 	- EsitoElezione.getEsitoElezioneForJUnitTesting al 52.9%
	 * 	  
	 */
	@Test
	public void testEsitoElezione_InvalidVotazione() {
		List<ElezioneVote> votiElezione = new ArrayList<ElezioneVote>();
		
		Elezione elezione = Elezione.createElezioneForTestingJUNIT(0, 
				null, 
				false, 
				false, 
				TipologiaElezione.VotazioneOrdinale, 
				true);
		List<Candidato> candidatiVotati = new ArrayList<Candidato>();
		candidatiVotati.add(Candidato.createCandidatoForTestingJUNIT(0, "Matteo", "Rizzi", new Date(System.currentTimeMillis())));
		List<Partito> partitiVotati = new ArrayList<Partito>();
		partitiVotati.add(Partito.createPartitoForTestingJUNIT(0, "PartitoA"));

		ElezioneVote ev = new ElezioneVote(elezione, candidatiVotati, partitiVotati);
		votiElezione.add(ev);
		ElezioneVote ev1 = new ElezioneVote(elezione, new ArrayList<Candidato>(), new ArrayList<Partito>());
		votiElezione.add(ev1);
		ElezioneVote ev2 = new ElezioneVote(elezione, new ArrayList<Candidato>(), new ArrayList<Partito>());
		votiElezione.add(ev2);
		
		EsitoElezione esito = EsitoElezione.getEsitoElezioneForJUnitTesting(votiElezione, elezione.getTipoElezione(), elezione);
		assertEquals(esito.getNumeroSchedeTotali(),3);
		assertEquals(esito.getNumeroSchedeTotali(),esito.getNumeroSchedeValide()+esito.getNumeroSchedeBianche());
		assertEquals(esito.getVotiCandidati().size(), 1);
		assertEquals(esito.getVotiPartiti().size(), 1);
		assertEquals(esito.getIsValid(), false);
	}

}