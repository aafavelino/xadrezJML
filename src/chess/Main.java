package chess;
import javax.imageio.ImageIO;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.ListIterator;


/**
 * @author Ashish Kedia and Adarsh Mohata
 *
 */


/**
 * This is the Main Class of our project.
 * All GUI Elements are declared, initialized and used in this class itself.
 * It is inherited from the JFrame Class of Java's Swing Library. 
 * 
 */

public class Main extends JFrame implements MouseListener
{
	private /*@ spec_public @*/ static final long serialVersionUID = 1L;
	/*@ public constraint serialVersionUID == 1; @*/
	
	//Variable Declaration
	public /*@ non_null @*/static final  String caminho_diretorio = System.getProperty("user.dir") + "/src/chess/";
	
	
	private static final int Height=700;
	private static final int Width=1110;
	private /*@ spec_public nullable @*/ static  Rook wr01,wr02,br01,br02;
	private /*@ spec_public nullable @*/ static  Knight wk01,wk02,bk01,bk02;
	private /*@ spec_public nullable @*/ static  Bishop wb01,wb02,bb01,bb02;
	private /*@ spec_public nullable @*/ static  Pawn wp[],bp[];
	private /*@ spec_public nullable @*/ static  Queen wq,bq;
	private /*@ spec_public nullable @*/ static  King wk,bk;
	private /*@ spec_public nullable @*/ Cell c,previous;
	private /*@ spec_public @*/ int chance=0;
	private /*@ spec_public nullable @*/ Cell boardState[][];
	private /*@ spec_public non_null @*/ ArrayList<Cell> destinationlist = new ArrayList<Cell>();
	private /*@ spec_public nullable @*/ Player White=null,Black=null;
	private /*@ spec_public non_null @*/ JPanel board=new JPanel(new GridLayout(8,8));
	private /*@ spec_public non_null @*/ JPanel wdetails=new JPanel(new GridLayout(3,3));
	private /*@ spec_public non_null @*/ JPanel bdetails=new JPanel(new GridLayout(3,3));
	private /*@ spec_public non_null @*/ JPanel wcombopanel=new JPanel();
	private /*@ spec_public non_null @*/ JPanel bcombopanel=new JPanel();
	private /*@ spec_public nullable @*/ JPanel controlPanel,WhitePlayer,BlackPlayer,temp,displayTime,showPlayer,time;
	private /*@ spec_public nullable @*/ JSplitPane split;
	private /*@ spec_public nullable @*/ JLabel label,mov;
	private static /*@ spec_public nullable @*/ JLabel CHNC;
	private /*@ spec_public nullable @*/ Time timer;
	public /*@ nullable @*/ static Main Mainboard;
	private /*@ spec_public @*/ boolean selected=false,end=false;
	private /*@ spec_public nullable @*/ Container content;
	private /*@ spec_public nullable @*/ ArrayList<Player> wplayer,bplayer;
	private /*@ spec_public nullable @*/ ArrayList<String> Wnames=new ArrayList<String>();
	private /*@ spec_public nullable @*/ ArrayList<String> Bnames=new ArrayList<String>();
	private /*@ spec_public nullable @*/ JComboBox<String> wcombo,bcombo;
	private /*@ spec_public nullable @*/ String wname=null,bname=null,winner=null;
	static /*@ spec_public nullable @*/ String move;
	private /*@ spec_public nullable @*/ Player tempPlayer;
	private /*@ spec_public nullable @*/ JScrollPane wscroll,bscroll;
	private /*@ spec_public nullable @*/ String[] WNames={},BNames={};
	private /*@ spec_public nullable @*/ JSlider timeSlider;
	private /*@ spec_public nullable @*/ BufferedImage image;
	private /*@ spec_public nullable @*/ Button start,wselect,bselect,WNewPlayer,BNewPlayer;
	public static int timeRemaining=60;
	/*@ public constraint (timeRemaining % 60 == 0); @*/
	

	
	public static void main(String[] args){
	
	//variable initialization
		wr01 = new Rook("WR01", caminho_diretorio + "White_Rook.png", 0);
		wr02 = new Rook("WR02", caminho_diretorio + "White_Rook.png", 0);
		br01 = new Rook("BR01", caminho_diretorio + "Black_Rook.png", 1);
		br02 = new Rook("BR02", caminho_diretorio + "Black_Rook.png", 1);
		wk01 = new Knight("WK01", caminho_diretorio + "White_Knight.png", 0);
		wk02 = new Knight("WK02", caminho_diretorio + "White_Knight.png", 0);
		bk01 = new Knight("BK01", caminho_diretorio + "Black_Knight.png", 1);
		bk02 = new Knight("BK02", caminho_diretorio + "Black_Knight.png", 1);
		wb01 = new Bishop("WB01", caminho_diretorio + "White_Bishop.png", 0);
		wb02 = new Bishop("WB02", caminho_diretorio + "White_Bishop.png", 0);
		bb01 = new Bishop("BB01", caminho_diretorio + "Black_Bishop.png", 1);
		bb02 = new Bishop("BB02", caminho_diretorio + "Black_Bishop.png", 1);
		wq = new Queen("WQ", caminho_diretorio + "White_Queen.png", 0);
		bq = new Queen("BQ", caminho_diretorio + "Black_Queen.png", 1);
		wk = new King("WK", caminho_diretorio + "White_King.png", 0, 7, 3);
		bk = new King("BK", caminho_diretorio + "Black_King.png", 1, 0, 3);
	wp=new Pawn[8];
	bp=new Pawn[8];
	for(int i=0;i<8;i++)
	{
		wp[i]=new Pawn("WP0"+(i+1),caminho_diretorio+"White_Pawn.png",0);
		bp[i]=new Pawn("BP0"+(i+1),caminho_diretorio+"Black_Pawn.png",1);
	}
	
	//Setting up the board
	Mainboard = new Main();
	Mainboard.setVisible(true);	
	Mainboard.setResizable(false);
	}
	
	//Constructor
	/*@ public initially timeRemaining == 60; 
	  @ public initially move.equals("White");
	  @ public initially 
	  @		(\forall int i; i < 8; 
	  @			(\forall int e; e < 8; boardState[i][e] != null));
	  @ requires wr01 != null && wr02 != null && br01 != null && br02 != null;
	  @ requires wk01 != null && wk02 != null && bk01 != null && bk02 != null;
	  @ requires wb01  != null && wb02  != null && bb01  != null && bb02  != null;
	  @ requires (\forall int i; i >= 0 && i < wp.length; wp[i] != null );
	  @ requires (\forall int i; i >= 0 && i < bp.length; bp[i] != null );
	  @ requires wq != null && bq != null;
	  @ requires wk != null && bk != null;
	  @ ensures (\forall int i; 0 <= i && i < 8; boardState[1][i].getpiece() == bp[i]);
	  @ ensures (\forall int i; 0 <= i && i < 8; boardState[6][i].getpiece() == wp[i]);
	  @ ensures boardState[0][0].getpiece() == br01;
	  @ ensures boardState[7][1].getpiece() == wk01; 
	  @ ensures boardState[0][1].getpiece() == bk01;
	  @ ensures boardState[7][2].getpiece() == wb01;
	  @ ensures boardState[7][0].getpiece() == wr01; 
	  @ ensures boardState[0][2].getpiece() == bb01;
	  @ ensures boardState[7][4].getpiece() == wq;
	  @ ensures boardState[0][4].getpiece() == bq;
	  @ ensures boardState[0][3].getpiece() == bk;
	  @ ensures boardState[7][3].getpiece() == wk;
	  @ ensures boardState[0][5].getpiece() == bb02;
	  @ ensures boardState[7][7].getpiece() == wr02;
	  @ ensures boardState[7][5].getpiece() == wb02;
	  @ ensures boardState[0][6].getpiece() == bk02;
	  @ ensures boardState[7][6].getpiece() == wk02;
      @ ensures boardState[0][7].getpiece() == br02;  
	  @*/
	private Main()
    {
		timeRemaining=60;
		timeSlider = new JSlider();
		move="White";
		wname=null;
		bname=null;
		winner=null;
		board=new JPanel(new GridLayout(8,8));
		wdetails=new JPanel(new GridLayout(3,3));
		bdetails=new JPanel(new GridLayout(3,3));
		bcombopanel=new JPanel();
		wcombopanel=new JPanel();
		Wnames=new ArrayList<String>();
		Bnames=new ArrayList<String>();
		board.setMinimumSize(new Dimension(800,700));
		ImageIcon img = new ImageIcon(caminho_diretorio + "icon.png");
		this.setIconImage(img.getImage());
		
		//Time Slider Details
		timeSlider.setMinimum(1);
		timeSlider.setMaximum(15);
		timeSlider.setValue(1);
		timeSlider.setMajorTickSpacing(2);
		timeSlider.setPaintLabels(true);
		timeSlider.setPaintTicks(true);
		timeSlider.addChangeListener(new TimeChange());
		
		
		//Fetching Details of all Players
		wplayer= Player.fetch_players();
		Iterator<Player> witr=wplayer.iterator();
		while(witr.hasNext())
			Wnames.add(witr.next().name());
				
		bplayer= Player.fetch_players();
		Iterator<Player> bitr=bplayer.iterator();
		while(bitr.hasNext())
			Bnames.add(bitr.next().name());
	    WNames=Wnames.toArray(WNames);	
		BNames=Bnames.toArray(BNames);
		
		Cell cell;
		board.setBorder(BorderFactory.createLoweredBevelBorder());
		Piece P;
		content=getContentPane();
		setSize(Width,Height);
		setTitle("Chess");
		content.setBackground(Color.black);
		controlPanel=new JPanel();
		content.setLayout(new BorderLayout());
		controlPanel.setLayout(new GridLayout(3,3));
		controlPanel.setBorder(BorderFactory.createTitledBorder(null, "Statistics", TitledBorder.TOP,TitledBorder.CENTER, new Font("Lucida Calligraphy",Font.PLAIN,20), Color.ORANGE));
		
		//Defining the Player Box in Control Panel
		WhitePlayer=new JPanel();
		WhitePlayer.setBorder(BorderFactory.createTitledBorder(null, "White Player", TitledBorder.TOP,TitledBorder.CENTER, new Font("times new roman",Font.BOLD,18), Color.RED));
		WhitePlayer.setLayout(new BorderLayout());
		
		BlackPlayer=new JPanel();
		BlackPlayer.setBorder(BorderFactory.createTitledBorder(null, "Black Player", TitledBorder.TOP,TitledBorder.CENTER, new Font("times new roman",Font.BOLD,18), Color.BLUE));
	    BlackPlayer.setLayout(new BorderLayout());
		
	    JPanel whitestats=new JPanel(new GridLayout(3,3));
		JPanel blackstats=new JPanel(new GridLayout(3,3));
		wcombo=new JComboBox<String>(WNames);
		bcombo=new JComboBox<String>(BNames);
		wscroll=new JScrollPane(wcombo);
		bscroll=new JScrollPane(bcombo);
		wcombopanel.setLayout(new FlowLayout());
		bcombopanel.setLayout(new FlowLayout());
		wselect=new Button("Select");
		bselect=new Button("Select");
		wselect.addActionListener(new SelectHandler(0));
		bselect.addActionListener(new SelectHandler(1));
		WNewPlayer=new Button("New Player");
		BNewPlayer=new Button("New Player");
		WNewPlayer.addActionListener(new Handler(0));
		BNewPlayer.addActionListener(new Handler(1));
		wcombopanel.add(wscroll);
		wcombopanel.add(wselect);
		wcombopanel.add(WNewPlayer);
		bcombopanel.add(bscroll);
		bcombopanel.add(bselect);
		bcombopanel.add(BNewPlayer);
		WhitePlayer.add(wcombopanel,BorderLayout.NORTH);
		BlackPlayer.add(bcombopanel,BorderLayout.NORTH);
		whitestats.add(new JLabel("Name   :"));
		whitestats.add(new JLabel("Played :"));
		whitestats.add(new JLabel("Won    :"));
		blackstats.add(new JLabel("Name   :"));
		blackstats.add(new JLabel("Played :"));
		blackstats.add(new JLabel("Won    :"));
		WhitePlayer.add(whitestats,BorderLayout.WEST);
		BlackPlayer.add(blackstats,BorderLayout.WEST);
		controlPanel.add(WhitePlayer);
		controlPanel.add(BlackPlayer);
		
		
		//Defining all the Cells
		boardState=new Cell[8][8];
		for(int i=0;i<8;i++)
			for(int j=0;j<8;j++)
			{	
				P=null;
				if(i==0&&j==0)
					P=br01;
				else if(i==0&&j==7)
					P=br02;
				else if(i==7&&j==0)
					P=wr01;
				else if(i==7&&j==7)
					P=wr02;
				else if(i==0&&j==1)
					P=bk01;
				else if (i==0&&j==6)
					P=bk02;
				else if(i==7&&j==1)
					P=wk01;
				else if (i==7&&j==6)
					P=wk02;
				else if(i==0&&j==2)
					P=bb01;
				else if (i==0&&j==5)
					P=bb02;
				else if(i==7&&j==2)
					P=wb01;
				else if(i==7&&j==5)
					P=wb02;
				else if(i==0&&j==3)
					P=bk;
				else if(i==0&&j==4)
					P=bq;
				else if(i==7&&j==3)
					P=wk;
				else if(i==7&&j==4)
					P=wq;
				else if(i==1)
				P=bp[j];
				else if(i==6)
					P=wp[j];
				cell=new Cell(i,j,P);
				cell.addMouseListener(this);
				board.add(cell);
				boardState[i][j]=cell;
			}
		showPlayer=new JPanel(new FlowLayout());  
		showPlayer.add(timeSlider);
		JLabel setTime=new JLabel("Set Timer(in mins):"); 
		start=new Button("Start");
		start.setBackground(Color.black);
		start.setForeground(Color.white);
	    start.addActionListener(new START());
		start.setPreferredSize(new Dimension(120,40));
		setTime.setFont(new Font("Arial",Font.BOLD,16));
		label = new JLabel("Time Starts now", JLabel.CENTER);
		  label.setFont(new Font("SERIF", Font.BOLD, 30));
	      displayTime=new JPanel(new FlowLayout());
	      time=new JPanel(new GridLayout(3,3));
	      time.add(setTime);
	      time.add(showPlayer);
	      displayTime.add(start);
	      time.add(displayTime);
	      controlPanel.add(time);
		board.setMinimumSize(new Dimension(800,700));
		
		//The Left Layout When Game is inactive
		temp=new JPanel(){
			private static final long serialVersionUID = 1L;
			     
			@Override
			/*@	requires g != null;
			 @	assignable image;
			 @*/
		    public void paintComponent(Graphics g) {
				  try {
			          image = ImageIO.read(new File(caminho_diretorio + "clash.jpg"));
			       } catch (IOException ex) {
			            System.out.println("not found");
			       }
			   
				g.drawImage(image, 0, 0, null);
			}         
	    };

		temp.setMinimumSize(new Dimension(800,700));
		controlPanel.setMinimumSize(new Dimension(285,700));
		split = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,temp, controlPanel);
		
	    content.add(split);
		setDefaultCloseOperation(EXIT_ON_CLOSE);
    }
	
	// A function to change the chance from White Player to Black Player or vice verse
	// It is made public because it is to be accessed in the Time Class
	/*@	requires chance == 0 || chance == 1;
	 @	requires (\forall int i; i >= 0 && i < boardState.length; (\forall int e; e >= 0 && e < boardState[i].length; boardState[i][e] != null));
	 @	ensures \old(chance) != chance;
	 @*/
	public void changechance()
	{
		if (boardState[getKing(chance).getx()][getKing(chance).gety()].ischeck())
		{
			chance^=1;
			gameend();
		}
		if(destinationlist.isEmpty()==false)
			cleandestinations(destinationlist);
		if(previous!=null)
			previous.deselect();
		previous=null;
		chance^=1;
		if(!end && timer!=null)
		{
			timer.reset();
			timer.start();
			showPlayer.remove(CHNC);
			if(Main.move=="White")
				Main.move="Black";
			else
				Main.move="White";
			CHNC.setText(Main.move);
			showPlayer.add(CHNC);
		}
	}
	
	//A function to retrieve the Black King or White King
	/*@ requires color >= 0;
	 @	ensures \result == wk || \result == bk;
	 @*/
	private /*@ pure @*/ King getKing(int color)
	{
		if (color==0)
			return wk;
		else
			return bk;
	}
	
	//A function to clean the highlights of possible destination cells
	/*@ requires destlist != null;
	 @	requires (\forall int i; i >= 0 && i < destlist.size(); destlist.get(i) != null);
	 @*/
    private void cleandestinations(ArrayList<Cell> destlist)      //Function to clear the last move's destinations
    {
    	ListIterator<Cell> it = destlist.listIterator();
    	while(it.hasNext())
    		it.next().removepossibledestination();
    }
    
    //A function that indicates the possible moves by highlighting the Cells
    /*@	requires destlist != null;
     @	requires (\forall int i; i >= 0 && i < destlist.size(); destlist.get(i) != null);
     @	ensures	(\forall int i; i >= 0 &&  i < destlist.size(); ( (Cell) destlist.get(i)).ispossibledestination() ==  true);
     @*/
    private void highlightdestinations(ArrayList<Cell> destlist)
    {
    	ListIterator<Cell> it = destlist.listIterator();
    	while(it.hasNext())
    		it.next().setpossibledestination();
    }
    
    
  //Function to check if the king will be in danger if the given move is made
    /*@	requires fromcell != null;
    @	requires tocell != null;
    @	requires (\forall int i; i >= 0 && i < boardState.length; (\forall int e; e >= 0 && e < boardState[i].length; boardState[i][e] != null));
    @	ensures ((King)(boardState[getKing(chance).getx()][getKing(chance).gety()].getpiece())).isindanger(boardState) == true ==> \result == true;
    @*/
    private boolean willkingbeindanger(Cell fromcell,Cell tocell)
    {
    	Cell newboardstate[][] = new Cell[8][8];
    	for(int i=0;i<8;i++)
    		for(int j=0;j<8;j++)
    		{	try { newboardstate[i][j] = new Cell(boardState[i][j]);} catch (CloneNotSupportedException e){e.printStackTrace(); System.out.println("There is a problem with cloning !!"); }}
    	
    	if(newboardstate[tocell.x][tocell.y].getpiece()!=null)
			newboardstate[tocell.x][tocell.y].removePiece();
    	
		newboardstate[tocell.x][tocell.y].setPiece(newboardstate[fromcell.x][fromcell.y].getpiece());
		if(newboardstate[tocell.x][tocell.y].getpiece() instanceof King)
		{
			((King)(newboardstate[tocell.x][tocell.y].getpiece())).setx(tocell.x);
			((King)(newboardstate[tocell.x][tocell.y].getpiece())).sety(tocell.y);
		}
		newboardstate[fromcell.x][fromcell.y].removePiece();
		if (((King)(newboardstate[getKing(chance).getx()][getKing(chance).gety()].getpiece())).isindanger(newboardstate)==true)
			return true;
		else
			return false;
    }
    
    //A function to eliminate the possible moves that will put the King in danger
    /*@	requires destlist != null;
     @	requires fromcell != null;
     @	requires (\forall int i; i >= 0 && i < destlist.size(); destlist.get(i) != null);
     @	ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
     @*/
    private ArrayList<Cell> filterdestination (ArrayList<Cell> destlist, Cell fromcell)
    {
    	ArrayList<Cell> newlist = new ArrayList<Cell>();
    	Cell newboardstate[][] = new Cell[8][8];
    	ListIterator<Cell> it = destlist.listIterator();
    	int x,y;
    	while (it.hasNext())
    	{
    		for(int i=0;i<8;i++)
        		for(int j=0;j<8;j++)
        		{	try { newboardstate[i][j] = new Cell(boardState[i][j]);} catch (CloneNotSupportedException e){e.printStackTrace();}}
    		
    		Cell tempc = it.next();
    		if(newboardstate[tempc.x][tempc.y].getpiece()!=null)
    			newboardstate[tempc.x][tempc.y].removePiece();
    		newboardstate[tempc.x][tempc.y].setPiece(newboardstate[fromcell.x][fromcell.y].getpiece());
    		x=getKing(chance).getx();
    		y=getKing(chance).gety();
    		if(newboardstate[fromcell.x][fromcell.y].getpiece() instanceof King)
    		{
    			((King)(newboardstate[tempc.x][tempc.y].getpiece())).setx(tempc.x);
    			((King)(newboardstate[tempc.x][tempc.y].getpiece())).sety(tempc.y);
    			x=tempc.x;
    			y=tempc.y;
    		}
    		newboardstate[fromcell.x][fromcell.y].removePiece();
    		if ((((King)(newboardstate[x][y].getpiece())).isindanger(newboardstate)==false))
    			newlist.add(tempc);
    	}
    	return newlist;
    }
    
    //A Function to filter the possible moves when the king of the current player is under Check 
    /*@	requires destlist != null;
     @	requires fromcell != null;
     @ 	requires color == 0 || color == 1;
     @	requires (\forall int i; i >= 0 && i < destlist.size(); destlist.get(i) != null);
     @	ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
     @	ensures (\forall int i; 0 <= i && i < \result.size(); destlist.contains(\result.get(i)) == true);
     @*/
    private ArrayList<Cell> incheckfilter (ArrayList<Cell> destlist, Cell fromcell, int color)
    {
    	ArrayList<Cell> newlist = new ArrayList<Cell>();
    	Cell newboardstate[][] = new Cell[8][8];
    	ListIterator<Cell> it = destlist.listIterator();
    	int x,y;
    	while (it.hasNext())
    	{
    		for(int i=0;i<8;i++)
        		for(int j=0;j<8;j++)
        		{	try { newboardstate[i][j] = new Cell(boardState[i][j]);} catch (CloneNotSupportedException e){e.printStackTrace();}}
    		Cell tempc = it.next();
    		if(newboardstate[tempc.x][tempc.y].getpiece()!=null)
    			newboardstate[tempc.x][tempc.y].removePiece();
    		newboardstate[tempc.x][tempc.y].setPiece(newboardstate[fromcell.x][fromcell.y].getpiece());
    		x=getKing(color).getx();
    		y=getKing(color).gety();
    		if(newboardstate[tempc.x][tempc.y].getpiece() instanceof King)
    		{
    			((King)(newboardstate[tempc.x][tempc.y].getpiece())).setx(tempc.x);
    			((King)(newboardstate[tempc.x][tempc.y].getpiece())).sety(tempc.y);
    			x=tempc.x;
    			y=tempc.y;
    		}
    		newboardstate[fromcell.x][fromcell.y].removePiece();
    		if ((((King)(newboardstate[x][y].getpiece())).isindanger(newboardstate)==false))
    			newlist.add(tempc);
    	}
    	return newlist;
    }
    
    //A function to check if the King is check-mate. The Game Ends if this function returns true.
    /*@ requires color == 0 || color == 1;
     @	ensures \result == true || \result == false;
     @*/
    public boolean checkmate(int color)
    {
    	ArrayList<Cell> dlist = new ArrayList<Cell>();
    	for(int i=0;i<8;i++)
    	{
    		for(int j=0;j<8;j++)
    		{
    			if (boardState[i][j].getpiece()!=null && boardState[i][j].getpiece().getcolor()==color)
    			{
    				dlist.clear();
    				boolean ok = kingCantMove(dlist, i, j, color);
    				if(!ok) {
    					return false;
    				}
    			}
    		}
    	}
    	return true;
    }
    
    /*@ requires dlist != null;
     @	requires 0 <= i && i < 8;
     @	requires 0 <= j && j < 8;
     @	requires color == 0 || color == 1;
     @ ensures dlist.size() != 0 ==> \result == false;
     @ ensures dlist.size() == 0 ==> \result == true;
     @*/
    public boolean kingCantMove(ArrayList<Cell> dlist, int i, int j, int color) {
		dlist=boardState[i][j].getpiece().move(boardState, i, j);
		dlist=incheckfilter(dlist,boardState[i][j],color);
		if(dlist.size()!=0){
			return false;
		}
		else {
			return true;
		}
    }
	
    
    @SuppressWarnings("deprecation")
	private void gameend()
    {
    	cleandestinations(destinationlist);
    	displayTime.disable();
    	timer.countdownTimer.stop();
    	if(previous!=null)
    		previous.removePiece();
    	if(chance==0)
		{	White.updateGamesWon();
			White.Update_Player();
			winner=White.name();
		}
		else
		{
			Black.updateGamesWon();
			Black.Update_Player();
			winner=Black.name();
		}
		JOptionPane.showMessageDialog(board,"Checkmate!!!\n"+winner+" wins");
		WhitePlayer.remove(wdetails);
		BlackPlayer.remove(bdetails);
		displayTime.remove(label);
		
		displayTime.add(start);
		showPlayer.remove(mov);
		showPlayer.remove(CHNC);
		showPlayer.revalidate();
		showPlayer.add(timeSlider);
		
		split.remove(board);
		split.add(temp);
		WNewPlayer.enable();
		BNewPlayer.enable();
		wselect.enable();
		bselect.enable();
		end=true;
		Mainboard.disable();
		Mainboard.dispose();
		Mainboard = new Main();
		Mainboard.setVisible(true);
		Mainboard.setResizable(false);
    }
    
    //These are the abstract function of the parent class. Only relevant method here is the On-Click Fuction
    //which is called when the user clicks on a particular cell
	@Override
	public void mouseClicked(MouseEvent arg0){
		// TODO Auto-generated method stub
		c=(Cell)arg0.getSource();
		if (previous==null)
		{
			if(c.getpiece()!=null)
			{
				if(c.getpiece().getcolor()!=chance)
					return;
				c.select();
				previous=c;
				destinationlist.clear();
				destinationlist=c.getpiece().move(boardState, c.x, c.y);
				if(c.getpiece() instanceof King)
					destinationlist=filterdestination(destinationlist,c);
				else
				{
					if(boardState[getKing(chance).getx()][getKing(chance).gety()].ischeck())
						destinationlist = new ArrayList<Cell>(filterdestination(destinationlist,c));
					else if(destinationlist.isEmpty()==false && willkingbeindanger(c,destinationlist.get(0)))
						destinationlist.clear();
				}
				highlightdestinations(destinationlist);
			}
		}
		else
		{
			if(c.x==previous.x && c.y==previous.y)
			{
				c.deselect();
				cleandestinations(destinationlist);
				destinationlist.clear();
				previous=null;
			}
			else if(c.getpiece()==null||previous.getpiece().getcolor()!=c.getpiece().getcolor())
			{
				if(c.ispossibledestination())
				{
					if(c.getpiece()!=null)
						c.removePiece();
					c.setPiece(previous.getpiece());
					if (previous.ischeck())
						previous.removecheck();
					previous.removePiece();
					if(getKing(chance^1).isindanger(boardState))
					{
						boardState[getKing(chance^1).getx()][getKing(chance^1).gety()].setcheck();
						if (checkmate(getKing(chance^1).getcolor()))
						{
							previous.deselect();
							if(previous.getpiece()!=null)
								previous.removePiece();
							gameend();
						}
					}
					if(getKing(chance).isindanger(boardState)==false)
						boardState[getKing(chance).getx()][getKing(chance).gety()].removecheck();
					if(c.getpiece() instanceof King)
					{
						((King)c.getpiece()).setx(c.x);
						((King)c.getpiece()).sety(c.y);
					}
					changechance();
					if(!end)
					{
						timer.reset();
						timer.start();
					}
				}
				if(previous!=null)
				{
					previous.deselect();
					previous=null;
				}
				cleandestinations(destinationlist);
				destinationlist.clear();
			}
			else if(previous.getpiece().getcolor()==c.getpiece().getcolor())
			{
				previous.deselect();
				cleandestinations(destinationlist);
				destinationlist.clear();
				c.select();
				previous=c;
				destinationlist=c.getpiece().move(boardState, c.x, c.y);
				if(c.getpiece() instanceof King)
					destinationlist=filterdestination(destinationlist,c);
				else
				{
					if(boardState[getKing(chance).getx()][getKing(chance).gety()].ischeck())
						destinationlist = new ArrayList<Cell>(filterdestination(destinationlist,c));
					else if(destinationlist.isEmpty()==false && willkingbeindanger(c,destinationlist.get(0)))
						destinationlist.clear();
				}
				highlightdestinations(destinationlist);
			}
		}
		if(c.getpiece()!=null && c.getpiece() instanceof King)
		{
			((King)c.getpiece()).setx(c.x);
			((King)c.getpiece()).sety(c.y);
		}
	}
    
    //Other Irrelevant abstract function. Only the Click Event is captured.
	@Override
	public void mouseEntered(MouseEvent arg0) {
		// TODO Auto-generated method stub
	}
	@Override
	public void mouseExited(MouseEvent arg0) {
		// TODO Auto-generated method stub
	}
	@Override
	public void mousePressed(MouseEvent arg0) {
		// TODO Auto-generated method stub
	}
	@Override
	public void mouseReleased(MouseEvent arg0) {
		// TODO Auto-generated method stub		
	}
	
	
	class START implements ActionListener
	{

	@SuppressWarnings("deprecation")
	@Override
	public void actionPerformed(ActionEvent arg0) {
		// TODO Auto-generated method stub
		
		if(White==null||Black==null)
			{JOptionPane.showMessageDialog(controlPanel, "Fill in the details");
			return;}
		White.updateGamesPlayed();
		White.Update_Player();
		Black.updateGamesPlayed();
		Black.Update_Player();
		WNewPlayer.disable();
		BNewPlayer.disable();
		wselect.disable();
		bselect.disable();
		split.remove(temp);
		split.add(board);
		showPlayer.remove(timeSlider);
		mov=new JLabel("Move:");
		mov.setFont(new Font("Comic Sans MS",Font.PLAIN,20));
		mov.setForeground(Color.red);
		showPlayer.add(mov);
		CHNC=new JLabel(move);
		CHNC.setFont(new Font("Comic Sans MS",Font.BOLD,20));
		CHNC.setForeground(Color.blue);
		showPlayer.add(CHNC);
		displayTime.remove(start);
		displayTime.add(label);
		timer=new Time(label);
		timer.start();
	}
	}
	
	class TimeChange implements ChangeListener
	{
		@Override
		public void stateChanged(ChangeEvent arg0)
		{
			timeRemaining=timeSlider.getValue()*60;
		}
	}
	
	
	class SelectHandler implements ActionListener
	{
		private int color;
		
		SelectHandler(int i)
		{
			color=i;
		}
			@Override
			public void actionPerformed(ActionEvent arg0)
			{
				// TODO Auto-generated method stub
				tempPlayer=null;
				String n=(color==0)?wname:bname;
				JComboBox<String> jc=(color==0)?wcombo:bcombo;
				JComboBox<String> ojc=(color==0)?bcombo:wcombo;
				ArrayList<Player> pl=(color==0)?wplayer:bplayer;
				//ArrayList<Player> otherPlayer=(color==0)?bplayer:wplayer;
				ArrayList<Player> opl=Player.fetch_players();
				if(opl.isEmpty())
					return;
				JPanel det=(color==0)?wdetails:bdetails;
				JPanel PL=(color==0)?WhitePlayer:BlackPlayer; 
				if(selected==true)
					det.removeAll();
				n=(String)jc.getSelectedItem();
				Iterator<Player> it=pl.iterator();
				Iterator<Player> oit=opl.iterator();
				while(it.hasNext())
				{	
					Player p=it.next();
					if(p.name().equals(n))
						{tempPlayer=p;
						break;}
				}
				while(oit.hasNext())
				{	
					Player p=oit.next();
					if(p.name().equals(n))
						{opl.remove(p);
						break;}
				}
				
				if(tempPlayer==null)
					return;
				if(color==0)
					White=tempPlayer;
				else
					Black=tempPlayer;
				bplayer=opl;
				ojc.removeAllItems();
				for (Player s:opl)
					ojc.addItem(s.name());
				det.add(new JLabel(" "+tempPlayer.name()));
				det.add(new JLabel(" "+tempPlayer.gamesplayed()));
				det.add(new JLabel(" "+tempPlayer.gameswon()));
				
				PL.revalidate();
				PL.repaint();
				PL.add(det);
				selected=true;
			}
			
		}
		
		
		
		class Handler implements ActionListener{
			private int color;
			Handler(int i)
			{
				color=i;
			}
			@Override
			public void actionPerformed(ActionEvent e) {
				// TODO Auto-generated method stub
				String n=(color==0)?wname:bname;
				JPanel j=(color==0)?WhitePlayer:BlackPlayer;
				ArrayList<Player> N=Player.fetch_players();
				Iterator<Player> it=N.iterator();
				JPanel det=(color==0)?wdetails:bdetails;
				n=JOptionPane.showInputDialog(j,"Enter your name");
					
					if(n!=null)
					{
					
					while(it.hasNext())
					{
						if(it.next().name().equals(n))
						{JOptionPane.showMessageDialog(j,"Player exists");
						return;}
					}
			
						if(n.length()!=0)
						{Player tem=new Player(n);
						tem.Update_Player();
						if(color==0)
							White=tem;
						else
							Black=tem;
						}
						else return;
					}
				else
					return;
				det.removeAll();
				det.add(new JLabel(" "+n));
				det.add(new JLabel(" 0"));
				det.add(new JLabel(" 0"));
				j.revalidate();
				j.repaint();
				j.add(det);
				selected=true;
			}
			}	 
}