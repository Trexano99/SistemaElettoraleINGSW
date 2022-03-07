package observer.timer;

import java.util.Timer;

public interface ITimerObserver {

	public void thickedTimer(TimerTicker timer);
	
	public void endedTimer();
	
}
