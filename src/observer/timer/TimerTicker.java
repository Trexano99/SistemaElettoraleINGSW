package observer.timer;

import java.util.ArrayList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;

import javafx.application.Platform;

public class TimerTicker  {
	
	private Timer timer;
	private int seconds;
	private List<ITimerObserver> observers = new ArrayList<ITimerObserver>();

	private TimerTicker(int durata,  List<ITimerObserver>observers) {
		this.timer = new Timer();
		this.seconds = durata;
		for (ITimerObserver obs : observers) {
			addObserver(obs);
		}
		timer.schedule(timerTask,1, 1000);
	}
	
	
	private void addObserver(ITimerObserver obs) {
		this.observers.add(obs);
	}
	
	private void removeObserver(ITimerObserver obs) {
		this.observers.remove(obs);
	}
	
	private void timerTicked() {
		for (ITimerObserver obs : observers) {
			obs.thickedTimer(this);
			if(seconds==0)
				obs.endedTimer();
		}
	}
	
	private TimerTask timerTask = new TimerTask() {
		
		@Override
	    public void run() {
			Platform.runLater(() -> {
		    	seconds--;
		        timerTicked();
			});
	    }
	};
	
	public int getSeconds() {
		return seconds;
	}
	public String getSecondsString() {
		return String.format("%02d:%02d", (seconds % 3600)/60, seconds%60);
	}
	
	private static TimerTicker instance;

	public static void createTimer(int durata, List<ITimerObserver>observers) {
		instance = new TimerTicker(durata,observers);
	}
	
	
	
}
