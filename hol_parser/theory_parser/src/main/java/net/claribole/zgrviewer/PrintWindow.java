/*   FILE: PrintWindow.java
 *   DATE OF CREATION:  Wed Jun  1 16:28:18 2005
 *   Copyright (c) INRIA, 2004-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: PrintWindow.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.image.BufferedImage;
import java.awt.print.PageFormat;
import java.awt.print.Printable;
import java.awt.print.PrinterException;
import java.awt.print.PrinterJob;

import java.io.File;
import java.util.Vector;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JSpinner;
import javax.swing.JTextField;
import javax.swing.SpinnerNumberModel;
import javax.swing.SwingConstants;
import javax.swing.border.TitledBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class PrintWindow
{
    private final static String units[] = { "pixels", "inches", "cm", "mm" };
    private final static int PIXEL = 0;
    private final static int INCH = 1;
    private final static int CM = 2;
    private final static int MM = 3;

    private final static double CM_PER_INCH = 2.54;
    private final static double MM_PER_INCH = 25.4;

    private int last_dpi = 72;
    private int last_width_unit = PIXEL;
    private int last_height_unit = PIXEL;

    private JFrame frame;

    private JPanel content;
    private JPanel options;
    private JPanel buttons;

    private JButton cancel;
    private JButton export;

    private TitledBorder optionsBorder;

    private SpinnerNumberModel width;
    private SpinnerNumberModel height;

    private JComboBox widthUnit;
    private JComboBox heightUnit;

    private SpinnerNumberModel dpiSpinner;

    private FlowLayout layout;

    private double realWidth;
    private double realHeight;

    /* since using setValue causes a stateChange event, we need to
     * stop recursion by locking the state so subsequent functions
     * called by the changeStated handlers quietly exists
     */

    boolean stateLock = false;

    private int dpi = last_dpi;

    GraphicsManager grMngr;

    /**
     * Constructor for objects of class PrintWindow
     * @param   w   starting pixel width
     * @param   h   starting pixel height
     *@param gm GraphicsManager instantiated by the parent ZGRViewer/ZGRApplet
     */
    public PrintWindow(double w, double h, GraphicsManager gm){
    this.grMngr = gm;
    if ( w < 1 || h < 1){
        JOptionPane.showMessageDialog(grMngr.mainView.getFrame(), "Can not export visible region of size 0.", "Export to PNG error", JOptionPane.ERROR_MESSAGE);
        return;
    }

    realWidth = w;
        realHeight = h;

    // generate the window, but don't show it
        frame = new JFrame("Print Options");
        frame.setResizable(false);



        // construct the content pane
        content = new JPanel(new BorderLayout());
        frame.setContentPane(content);

        // create the options panel
        options = new JPanel(new GridLayout(3, 3));
        optionsBorder = BorderFactory.createTitledBorder("Print options");
        options.setBorder(optionsBorder);

        // define some helper classes
        class UnitActionListener implements ActionListener{
            public void actionPerformed(ActionEvent e){
                updateTextFields(false);
            }
        }

        class DPIChangeListener implements ChangeListener{
            public void stateChanged(ChangeEvent e){
                dpi = dpiSpinner.getNumber().intValue();
                updateTextFields(false);
        last_dpi = dpi;
            }
        }

        class TextChangeListener implements ChangeListener{
            public void stateChanged(ChangeEvent e){
                updateTextFields(true);
            }
        }

        UnitActionListener unitListener = new UnitActionListener();
        TextChangeListener textListener = new TextChangeListener();

        width = new SpinnerNumberModel(realWidth,1,Double.MAX_VALUE,1.0);
        width.addChangeListener(textListener);
        widthUnit = new JComboBox(units);
        widthUnit.addActionListener(unitListener);

        options.add(new JLabel("Image width: ", SwingConstants.RIGHT));
        options.add(new JSpinner(width));
        options.add(widthUnit);

        height = new SpinnerNumberModel(realHeight,1,Double.MAX_VALUE,1.0);
        height.addChangeListener(textListener);
        heightUnit = new JComboBox(units);
        heightUnit.addActionListener(unitListener);

        options.add(new JLabel("Image height: ", SwingConstants.RIGHT));
        options.add(new JSpinner(height));
        options.add(heightUnit);

        dpiSpinner = new SpinnerNumberModel(last_dpi,72,9999,1);
        dpiSpinner.addChangeListener(new DPIChangeListener());

        options.add(new JLabel("Dots per inch: ", SwingConstants.RIGHT));
        options.add(new JSpinner(dpiSpinner));

        content.add(options, BorderLayout.CENTER);

        // create the buttons panel
        buttons = new JPanel(new FlowLayout(FlowLayout.RIGHT));

        class CancelActionListener implements ActionListener{
            public void actionPerformed(ActionEvent e)
            {
                hide();
            }
        }

        class ExportActionListener implements ActionListener{
        public void actionPerformed(ActionEvent e){
        hide();
        grMngr.mainView.setStatusBarText("Sending image to printer ... (This operation can take some time)");

        realWidth = unitToPixel(realWidth, widthUnit.getSelectedIndex());
        realHeight = unitToPixel(realHeight, heightUnit.getSelectedIndex());

        Vector layers = new Vector();
        layers.add(grMngr.mainCamera);

        java.awt.image.BufferedImage bi = grMngr.mainView.rasterize((int)realWidth, (int)realHeight, layers);

        if (bi!=null){
            PrintUtilities pu=new PrintUtilities(bi);
            pu.print();
        }

        grMngr.mainView.setStatusBarText("Sending image to printer ...done");
        }
        }

        export = new JButton("Export");
        export.addActionListener(new ExportActionListener());

        cancel = new JButton("Cancel");
        cancel.addActionListener(new CancelActionListener());

        buttons.add(cancel);
        buttons.add(export);

        content.add(buttons, BorderLayout.SOUTH);

        updateTextFields(false);

        // prepare it for display
        frame.getRootPane().setDefaultButton(export);
        content.setPreferredSize(new Dimension(400,200));
        frame.pack();
    frame.setLocationRelativeTo(grMngr.mainView.getFrame());
        frame.setVisible(true);
    }

    /**
     * Displays the window
     */
    public void show(){
        frame.setVisible(true);
    }

    /**
     * Hides the window
     */
    public void hide(){
        frame.setVisible(false);
    }

    /**
     * updates all the text fields according to new selected unit and dpi informaion
     * @param   textChange  whether or not the text fields have changed
     */
    private void updateTextFields(boolean textChange){
        // only one instance of this method, ever
        if ( stateLock)
            return;

        stateLock = true;

        String text = "";

        if ( textChange ){
            realWidth = width.getNumber().doubleValue();
            realHeight = height.getNumber().doubleValue();
        }

        // calculate what to display for width
        double pixels = realWidth;

        // found out how many pixels we had before
        pixels = unitToPixel(realWidth, last_width_unit);
    pixels = pixelToUnit(pixels, widthUnit.getSelectedIndex());

        if (widthUnit.getSelectedIndex() == PIXEL){
            text = "" + (int)pixels;
        }
        else{
            text = "" + pixels;
        }

        if ( text.indexOf(".")>=0){
            text = text.substring(0,text.indexOf(".")+2);
        }
        width.setValue(new Double(text));

        // record the real value to avoid loss of precision during unit conversion
        realWidth = pixels;

        // now do height
        pixels = realHeight;

        // found out how many pixels we had before
        pixels = unitToPixel(realHeight, last_height_unit);
    pixels = pixelToUnit(pixels, heightUnit.getSelectedIndex());

        if (heightUnit.getSelectedIndex() == PIXEL){
            text = "" + (int)pixels;
        }
        else{
            text = "" + pixels;
        }

        if ( text.indexOf(".") >=0){
            text = text.substring(0,text.indexOf(".")+2);
        }
        height.setValue(new Double(text));

        // record the real value to avoid loss of precision during unit conversion
        realHeight = pixels;

        // set the last unit information
        last_width_unit = widthUnit.getSelectedIndex();
        last_height_unit = heightUnit.getSelectedIndex();

        stateLock = false;
    }


    /** Converts the given unit into pixels
     *  @param  number  number to convert
     *  @param  unit    unit to convert from
     *  @return         number of pixels
     */
    private double unitToPixel(double number, int unit){
    //System.out.print("converting " + number + " " + units[unit] + " to " );
    switch(unit){
    case INCH:
        number *= last_dpi;
        break;

    case PIXEL:
        break;

    case CM:
        number = number / CM_PER_INCH * last_dpi;
        break;

    case MM:
        number = number / MM_PER_INCH * last_dpi;
        break;
    }
    //System.out.println(number + " pixels");
    return number;
    }

    /** Converts pixels to the given unit
     *  @param  pixels  number of pixels to convert
     *  @param  unit    unit to conver to
     *  @return         number of units the given number of pixels represent
     */
    private double pixelToUnit(double pixels, int unit){
    //System.out.print("converting " + pixels + " pixels to ");
    switch(unit){
    case INCH:
        pixels = pixels / last_dpi;
        break;

    case PIXEL:
        pixels = pixels * dpi/last_dpi;
        break;

    case CM:
        pixels = pixels / last_dpi * CM_PER_INCH;
        break;

    case MM:
        pixels  = pixels / last_dpi * MM_PER_INCH;
        break;
    }
    //System.out.println(pixels +" " + units[unit]);
    return pixels;
    }
}

class PrintUtilities extends JPanel implements Printable {

    private BufferedImage bufferedImage;

    /**
     *@param bufferedImage image to be printed
     */
    public PrintUtilities( BufferedImage bufferedImage ){
    this.bufferedImage = bufferedImage;
    }


    /**
     * Launchs the printer job and call the method {@link #print(Graphics, PageFormat, int)} method
     */
    public void print(){
    PrinterJob printJob = PrinterJob.getPrinterJob();
    PageFormat pf = new PageFormat();
    pf.setOrientation(PageFormat.LANDSCAPE);
    printJob.setPrintable(this, pf);
//  pf = printJob.validatePage(pf);
    if (printJob.printDialog()){
            try {
        printJob.print();
        }
            catch(PrinterException pe) {
        JOptionPane.showMessageDialog(null, "Error while printing", "Error", JOptionPane.ERROR_MESSAGE);
        System.err.println("** Error printing: " + pe);
        pe.printStackTrace();
        }
    }
    }

    public int print(Graphics g, PageFormat pf, int pageIndex){
    Graphics2D g2d=(Graphics2D)g;
    int panelWidth=bufferedImage.getWidth(); //width in pixels
    int panelHeight=bufferedImage.getHeight(); //height in pixels
    double pageHeight=pf.getImageableHeight(); //height of printer page
    double pageWidth=pf.getImageableWidth(); //width of printer page
    if (pageIndex >= 1){
        return Printable.NO_SUCH_PAGE;
    }
    // To place the top right corner at the center of the shit page :
    setSize(new Dimension(panelWidth, panelHeight));
        g2d.translate(pf.getImageableX(),pf.getImageableY());
        g2d.translate(pf.getImageableWidth()/2, pf.getImageableHeight()/2);
        // To place at the center of the page :
    Dimension d=getSize();
        double scale=Math.min(pf.getImageableWidth()/d.width,pf.getImageableHeight()/d.height);
        if (scale < 1.0){g2d.scale(scale, scale);}
        g2d.translate(-d.width / 2.0, -d.height / 2.0);
        setOpaque(true);
    this.paint(g2d);
    return Printable.PAGE_EXISTS;
    }

    public void paint(Graphics g){
        if (getSize().width <= 0 || getSize().height <= 0){return;}
        Graphics2D g2 = (Graphics2D) g;
        if (bufferedImage != null){
            g2.drawImage(bufferedImage, 0, 0, this);
        }
    }

}
