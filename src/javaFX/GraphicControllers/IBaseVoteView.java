package javaFX.GraphicControllers;

public interface IBaseVoteView {
	
	public void initializeTimer();
	
	public void setHeaderContent(String nominativoElettore, String ruoloElettore);
	
	public void getPreviousPage();
	
	
	public void segnalaErrore(String nomeErrore, String contenutoErrore);
	
	public Boolean chiediConferma(String titolo, String contenuto);
	
}
