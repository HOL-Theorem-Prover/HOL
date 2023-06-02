package animator;
 
/*
 * Created on 25 juin 2004
 * AnimatedPanel.java
 * Panneau anim茅.
 */
 
import java.awt.AlphaComposite;
import java.awt.Color;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Image;
import java.awt.RenderingHints;
import java.awt.font.FontRenderContext;
import java.awt.font.TextLayout;
import java.awt.geom.Rectangle2D;
import java.awt.image.BufferedImage;
import java.awt.image.BufferedImageOp;
import java.awt.image.ConvolveOp;
import java.awt.image.Kernel;
 
import javax.swing.ImageIcon;
import javax.swing.JPanel;
 
/**
 * Affiche un panneau anim茅. L'animation consiste en l'highlight d'une image.
 * 
 * @author Romain Guy
 */
public class AnimatedPanel extends JPanel {
 
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private float gradient;
	private String message;
	private Thread animator;
	private BufferedImage convolvedImage;
	private BufferedImage originalImage;
	private Font font;
	private static AlphaComposite composite = AlphaComposite.getInstance(AlphaComposite.SRC_OVER);
 
	/**
	 * Cr茅e un panneau anim茅 contenant l'image pass茅e en param猫tre. L'animation
	 * ne d茅marre que par un appel 脿 start().
	 * 
	 * @param message Le message 脿 afficher
	 * @param icon L'image 脿 afficher et 脿 animer
	 * @author Romain Guy
	 */
	public AnimatedPanel(String message, ImageIcon icon) {
		this.message = message;
		this.font = getFont().deriveFont(14.0f);
 
		Image image = icon.getImage();
		originalImage = new BufferedImage(icon.getIconWidth(), icon.getIconHeight(), BufferedImage.TYPE_INT_ARGB);
		convolvedImage = new BufferedImage(icon.getIconWidth(), icon.getIconHeight(), BufferedImage.TYPE_INT_ARGB);
		Graphics g = originalImage.createGraphics();
		g.drawImage(image, 0, 0, this);
		g.dispose();
 
		setBrightness(1.0f);
		setOpaque(false);
	}
 
	@Override
	public void paintComponent(Graphics g) {
		super.paintComponent(g);
 
		if (convolvedImage != null) {
			int width = getWidth();
			int height = getHeight();
 
			synchronized (convolvedImage) {
				Graphics2D g2 = (Graphics2D) g;
				g2.setRenderingHint(RenderingHints.KEY_RENDERING, RenderingHints.VALUE_RENDER_QUALITY);
				g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
				g2.setRenderingHint(RenderingHints.KEY_FRACTIONALMETRICS, RenderingHints.VALUE_FRACTIONALMETRICS_ON);
 
				FontRenderContext context = g2.getFontRenderContext();
				TextLayout layout = new TextLayout(message, font, context);
				Rectangle2D bounds = layout.getBounds();
 
				int x = (width - convolvedImage.getWidth(null)) / 2;
				int y = (int) (height - (convolvedImage.getHeight(null) + bounds.getHeight() + layout.getAscent())) / 2;
 
				g2.drawImage(convolvedImage, x, y, this);
				g2.setColor(new Color(0, 0, 0, (int) (gradient * 255)));
				layout.draw(g2, (float) (width - bounds.getWidth()) / 2,
						(float) (y + convolvedImage.getHeight(null) + bounds.getHeight() + layout.getAscent()));
			}
		}
	}
 
	/**
	 * Modifie la luminosit茅 de l'image.
	 * 
	 * @param multiple Le taux de luminosit茅
	 */
	private void setBrightness(float multiple) {
		float[] brightKernel = { multiple };
		RenderingHints hints = new RenderingHints(RenderingHints.KEY_RENDERING, RenderingHints.VALUE_RENDER_QUALITY);
		BufferedImageOp bright = new ConvolveOp(new Kernel(1, 1, brightKernel), ConvolveOp.EDGE_NO_OP, hints);
		bright.filter(originalImage, convolvedImage);
		repaint();
	}
 
	/**
	 * Modifie le d茅grad茅 du texte.
	 * 
	 * @param gradient Le coefficient de d茅grad茅
	 */
	private void setGradientFactor(float gradient) {
		this.gradient = gradient;
	}
 
	/**
	 * D茅marre l'animation du panneau.
	 */
	public void start() {
		this.animator = new Thread(new HighlightCycler(), "Highlighter");
		this.animator.start();
	}
 
	/**
	 * Arr锚te l'animation.
	 */
	public void stop() {
		if (this.animator != null) {
			this.animator.interrupt();
		}
		this.animator = null;
	}
 
	/**
	 * Fait cycler la valeur d'highlight de l'image.
	 * 
	 * @author Romain Guy
	 */
	class HighlightCycler implements Runnable {
 
		private int way = 1;
		private final int LOWER_BOUND = 10;
		private final int UPPER_BOUND = 35;
		private int value = LOWER_BOUND;
 
		@Override
		public void run() {
			while (true) {
				try {
					Thread.sleep(1000 / (UPPER_BOUND - LOWER_BOUND));
				} catch (InterruptedException e) {
					return;
				}
 
				value += this.way;
				if (value > UPPER_BOUND) {
					value = UPPER_BOUND;
					this.way = -1;
				} else if (value < LOWER_BOUND) {
					value = LOWER_BOUND;
					this.way = 1;
				}
 
				synchronized (convolvedImage) {
					setBrightness((float) value / 10);
					setGradientFactor((float) value / UPPER_BOUND);
				}
			}
		}
 
	}
}