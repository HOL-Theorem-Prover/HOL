/**
 * Displays an export dialogue similar to photoshop
 *
 * @author shu ning bian
 * @version 07.02.2005
 *
 * Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: PNGExportWindow.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.IOException;
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

import java.awt.image.BufferedImage;
import javax.imageio.ImageIO;

public class PNGExportWindow {

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
    private JPanel fileSelection;
    private JPanel buttons;

    private JButton export;
    private JButton cancel;
    private JButton browse;

    private TitledBorder optionsBorder;

    private JTextField filePath;
    private SpinnerNumberModel width;
    private SpinnerNumberModel height;

    private JComboBox widthUnit;
    private JComboBox heightUnit;

    private SpinnerNumberModel dpiSpinner;

    private FlowLayout layout;

    private double realWidth;
    private double realHeight;

    private static File selectedFile = null;
    /* since using setValue causes a stateChange event, we need to
     * stop recursion by locking the state so subsequent functions
     * called by the changeStated handlers quietly exists
     */

    boolean stateLock = false;

    private int dpi = last_dpi;

    GraphicsManager grMngr;

    /**
     * Constructor for objects of class PNGExportWindow
     * @param   w   starting pixel width
     * @param   h   starting pixel height
     *@param gm GraphicsManager instantiated by the parent ZGRViewer/ZGRApplet
     */
    public PNGExportWindow(double w, double h, GraphicsManager gm){
    this.grMngr = gm;
    if ( w < 1 || h < 1){
        JOptionPane.showMessageDialog(grMngr.mainView.getFrame(), "Can not export visible region of size 0.", "Export to PNG error", JOptionPane.ERROR_MESSAGE);
        return;
    }

    realWidth = w;
        realHeight = h;

    // generate the window, but don't show it
        frame = new JFrame("PNG Export Options");
        frame.setResizable(false);



        // construct the content pane
        content = new JPanel(new BorderLayout());
        frame.setContentPane(content);

        // construct the file selection pane
        fileSelection = new JPanel(new FlowLayout(FlowLayout.RIGHT));
        filePath = new JTextField();
        filePath.setColumns(19);

        if ( selectedFile != null){
        filePath.setText(selectedFile.getPath());
        }

        class BrowseActionListener implements ActionListener{
            public void actionPerformed(ActionEvent e){
                JFileChooser fc;

                if ( selectedFile == null ){
            fc = new JFileChooser();
                }
                else{
            fc = new JFileChooser(selectedFile.getParentFile());
                }

                fc.setDialogTitle("Export PNG");
                if ( fc.showSaveDialog(frame) == fc.APPROVE_OPTION){
                    // set the filePath text box
                    selectedFile = fc.getSelectedFile();

                    if ( selectedFile != null){
                        filePath.setText(selectedFile.getPath());
                        export.setEnabled(true);
                    }
                    else{
                        export.setEnabled(false);
                        filePath.setText("");
                    }
                }
            }
        }
        browse = new JButton("Browse");
        browse.addActionListener(new BrowseActionListener());

        fileSelection.add(new JLabel("File path: ", SwingConstants.RIGHT));
        fileSelection.add(filePath);
        fileSelection.add(browse);

        content.add(fileSelection, BorderLayout.NORTH);

        // create the options panel
        options = new JPanel(new GridLayout(3, 3));
        optionsBorder = BorderFactory.createTitledBorder("Export options");
        options.setBorder(optionsBorder);

        // define some helper classes
        class UnitActionListener implements ActionListener{
            public void actionPerformed(ActionEvent e){
                updateTextFields(false);
            }
        }

        class DPIChangeListener implements ChangeListener
        {
            public void stateChanged(ChangeEvent e)
            {
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
            public void actionPerformed(ActionEvent e){
                hide();
            }
        }

        class ExportActionListener implements ActionListener{
            public void actionPerformed(ActionEvent e){
                hide();
                grMngr.mainView.setStatusBarText("Exporting to PNG "+filePath.getText()+" ... (This operation can take some time)");

                realWidth = unitToPixel(realWidth, widthUnit.getSelectedIndex());
                realHeight = unitToPixel(realHeight, heightUnit.getSelectedIndex());

                Vector layers = new Vector();
                layers.add(grMngr.mainCamera);
                BufferedImage bi = grMngr.mainView.rasterize((int)realWidth, (int)realHeight, layers);
                try {
                    ImageIO.write(bi, "png", new File(filePath.getText()));
                }
                catch (IOException ex){
                    System.err.println("ZGRViewer::Error while exporting current view to PNG file "+filePath.getText());
                    ex.printStackTrace();
                }
                grMngr.mainView.setStatusBarText("Exporting to PNG "+filePath.getText()+" ...done");
            }
        }

        export = new JButton("Export");
        export.addActionListener(new ExportActionListener());
        export.setEnabled(false);

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

        if ( text.indexOf(".") >=0) {
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
