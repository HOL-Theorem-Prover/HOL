//created by haoyang
package net.claribole.zgrviewer;

import java.awt.Container;
import java.io.File;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JMenuBar;


public class FrameDesign 
{
    static ConfigManager cfgMngr;
    static DOTManager dotMngr;

    public GVLoader gvLdr;
    GraphicsManager grMngr;

	public void display(String fileName) 
	{


		File graphFile = new File(fileName);
		ZGRPanelViewer zgrPanel = new ZGRPanelViewer();
		zgrPanel.loadFile(graphFile);
		JFrame jFrame = new JFrame();
        JMenuBar jmb = zgrPanel._zgrViewer.initViewMenu();
		
        jFrame.setJMenuBar(jmb);
		Container contentPane = jFrame.getContentPane();
		contentPane.add(zgrPanel.getPanel());
		JComponent glassPane = zgrPanel.getGlassPane();
		jFrame.setGlassPane(glassPane);
		jFrame.setSize(1080, 1080);
		jFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		jFrame.setVisible(true);
	}
}
