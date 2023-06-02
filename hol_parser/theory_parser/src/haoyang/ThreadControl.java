package haoyang;

import java.awt.*;

import javax.swing.*;

import animator.InfiniteProgressPanel;

public class ThreadControl extends Thread

{
    private String messages = "please wait for graph generation";
    public JDialog clueDiag = null;
    private Dimension dimensions = Toolkit.getDefaultToolkit().getScreenSize();
    private int width = dimensions.width / 4, height = 400;

    public ThreadControl()
    {
        initDiag();
    }

    protected void initDiag()

    {
        clueDiag = new JDialog();
        clueDiag.setCursor(new Cursor(Cursor.WAIT_CURSOR));
        JPanel testPanel = new JPanel();
        testPanel.setSize(width, 400);
        JLabel testLabel = new JLabel(messages);
        clueDiag.getContentPane().add(testPanel);
        testPanel.add(testLabel);

		InfiniteProgressPanel glasspane = new InfiniteProgressPanel();
		glasspane.setBounds((dimensions.width - width-300)/2, (dimensions.height - height)/2, width-80, height);
		clueDiag.setGlassPane(glasspane);
		glasspane.start();


 


        //create a end thread to close the diag after generation
        Thread EndThread = new Thread(new Runnable() {
            @Override
            public void run() {
                
                try {
                    do{
			        Thread.sleep(100);
		            }while(GraphUtil.dotprogram.isAlive()==true);
                } catch (InterruptedException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
                clueDiag.dispose();
            }
        });
        EndThread.start();
        
    }

    public void run()
    {
        
        // //thread active when the dot process is runnnig
        // while(GraphUtil.dotprogram.isAlive()==true)
        int left = (dimensions.width - width)/2;
        int top = (dimensions.height - height)/2;
        // clueDiag.setSize(new Dimension(width,height));
        clueDiag.setLocation(left, top);
        clueDiag.setSize(width, height);
        clueDiag.setVisible(true);
    }

}
