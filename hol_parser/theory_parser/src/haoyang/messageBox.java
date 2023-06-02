package haoyang;

import javax.swing.*;
import java.awt.*;

public class messageBox extends JFrame {
    public messageBox(String s,String title){
        this.setVisible(true);
        this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        this.setTitle(title);
        Dimension d = Toolkit.getDefaultToolkit().getScreenSize();//get windows
        int width = 600;
        int height = 360;
        this.setBounds((d.width-width)/2, (d.height-height)/2, width, height);//

        //new a TextArea
        JTextArea textArea = new JTextArea(560, 300);
        textArea.setText(s);
        textArea.setLineWrap(true);        
        textArea.setWrapStyleWord(true); 
        //new JScrollPane and add textArea to jScrollPane
        JScrollPane jScrollPane = new JScrollPane(textArea, JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
        //add js to container
        
        JScrollBar jscrollBar = jScrollPane.getVerticalScrollBar();
        SwingUtilities.invokeLater(new Runnable(){
            public void run(){
                jscrollBar.setValue(jscrollBar.getMinimum());
            }
        });
        
        Container contentPane = this.getContentPane();
        contentPane.add(jScrollPane);
    }
}


