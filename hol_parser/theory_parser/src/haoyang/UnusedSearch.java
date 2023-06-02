package haoyang;

import java.awt.Container;

import java.awt.GridLayout;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import java.io.IOException;
import java.awt.event.KeyListener;
import java.awt.event.KeyEvent;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;

import javax.swing.JTextField;



public class UnusedSearch extends JFrame implements KeyListener {

    static int FRAME_WIDTH = 300;
    static int FRAME_HEIGHT = 110;

    JButton prevBt, nextBt;
    JTextField searchText;

    public UnusedSearch(){
    super();
    Container cp = this.getContentPane();
    cp.setLayout(new GridLayout(2,1));
    JPanel p1 = new JPanel();
    JPanel p2 = new JPanel();
    cp.add(p1);
    cp.add(p2);
    p1.add(new JLabel("Put the theory:"));
    searchText = new JTextField(32);
    p1.add(searchText);
    searchText.addKeyListener(this);

    //window
    WindowListener w0=new WindowAdapter(){
        public void windowClosing(WindowEvent e){
            dispose();
        }
        };
    this.addWindowListener(w0);
    this.setTitle("Unused Check");
    this.pack();
    this.setResizable(false);
    }

    public void keyPressed(KeyEvent e){
    if (e.getKeyCode()==KeyEvent.VK_ENTER){
        String thyname=searchText.getText();
        System.out.println(thyname);
        try {
            TheoremParser.unused_check(FileReader.loadCurrentTheory(),thyname);
        } catch (IOException | InterruptedException e1) {
            // TODO Auto-generated catch block
            e1.printStackTrace();
        }
    }
    }

    public void keyReleased(KeyEvent e){}

    public void keyTyped(KeyEvent e){}

}