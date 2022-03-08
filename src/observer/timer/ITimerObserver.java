package observer.timer;

public interface ITimerObserver {

	public void thickedTimer(TimerTicker timer);
	
	public void endedTimer();
	
}
