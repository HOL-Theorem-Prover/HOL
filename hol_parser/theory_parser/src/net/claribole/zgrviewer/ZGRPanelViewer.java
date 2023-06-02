package net.claribole.zgrviewer;
import java.io.File;

import javax.swing.JComponent;
import javax.swing.JPanel;


public class ZGRPanelViewer
{

	public ZGRViewer _zgrViewer;
	private JPanel _panelView;

	public ZGRPanelViewer()
	{
		_zgrViewer = new ZGRViewer();

		_panelView = _zgrViewer.getPanelView();
	}

	public JPanel getPanel()
	{
		return _panelView;
	}

	public void loadFile(File dotFile)
	{
		_zgrViewer.setFile(dotFile);
	}

	public JComponent getGlassPane()
	{
		return _zgrViewer.getGlassPane();
	}
}
