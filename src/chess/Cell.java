package chess;

import java.awt.*;
import javax.swing.*;



/**
 * This is the Cell Class. It is the token class of our GUI.
 * There are total of 64 cells that together makes up the Chess Board
 *
 */
public class Cell extends JPanel implements Cloneable{
	
/*@ public invariant x >= 0 && x < 8 && y >= 0 && y < 8; @*/
	
	//Member Variables
	private /*@ spec_public @*/ static final long serialVersionUID = 1L;
	/*@ public constraint serialVersionUID == 1; @*/
	private /*@ spec_public @*/ boolean ispossibledestination;
	private  /*@ spec_public nullable @*/ JLabel content;
	private  /*@ spec_public nullable @*/ Piece piece;
	/*@ spec_public @*/ int x,y;                             //is public because this is to be accessed by all the other class
	private /*@ spec_public @*/ boolean isSelected=false;
	private /*@ spec_public @*/ boolean ischeck=false;
	
	//Constructors
	/*@ requires  tx >= 0 && tx < 8 && ty >= 0 && ty < 8;
	 @  assignable x, y;
	 @  ensures tx == x && ty == y && p == piece;
	 */
	public Cell(int tx,int ty, /*@ nullable @*/  Piece p)
	{		
		this.x=tx;
		this.y=ty;
		
		setLayout(new BorderLayout());
	
	 if((tx+ty)%2==0)
	  setBackground(new Color(113,198,113));
	
	 else
	  setBackground(Color.white);
	 
	 if(p!=null)
		 setPiece(p);
	}
	
	//A constructor that takes a cell as argument and returns a new cell will the same data but different reference
	/*@ requires cell != null;
	 @  assignable x, y, piece;
	 @  ensures cell.x == x && cell.y == y && (piece == null || piece == cell.piece);
	 @*/
	public Cell(Cell cell) throws CloneNotSupportedException
	{
		this.x=cell.x;
		this.y=cell.y;
		setLayout(new BorderLayout());
		if((x+y)%2==0)
			setBackground(new Color(113,198,113));
		else
			setBackground(Color.white);
		if(cell.getpiece()!=null)
		{
			setPiece(cell.getpiece().getcopy());
		}
		else
			piece=null;
	}

	/*@ requires  p != null;
	 @  assignable piece;
	 @  ensures p == piece;
	 @*/
	public void setPiece(Piece p)    //Function to inflate a cell with a piece
	{
		piece=p;
		ImageIcon img=new javax.swing.ImageIcon(p.getPath());
		content=new JLabel(img);
		this.add(content);
	}

	/*@ assignable piece;
	 @  ensures piece == null;
	 @*/
	public void removePiece()      //Function to remove a piece from the cell
	{
		if (piece instanceof King)
		{
			piece=null;
			this.remove(content);
		}
		else
		{
			piece=null;
			this.remove(content);
		}
	}	

	//@  ensures \result == piece;
	public /*@ pure nullable @*/ Piece getpiece()    //Function to access piece of a particular cell
	{
		return this.piece;
	}

	/*@ 
	 @  assignable isSelected;
	 @  ensures isSelected == true;
	 @*/
	public void select()       //Function to mark a cell indicating it's selection
	{
		this.setBorder(BorderFactory.createLineBorder(Color.red,6));
		this.isSelected=true;
	}

	//@  ensures isSelected == \result;
	public /*@ pure @*/  boolean isselected()   //Function to return if the cell is under selection
	{
		return this.isSelected;
	}
	
	/*@ 
	 @  assignable isSelected;
	 @  ensures isSelected == false;
	 @*/
	public void deselect()      //Function to delselect the cell
	{
		this.setBorder(null);
		this.isSelected=false;
	}

	
	
	/*@ 
	 @  assignable ispossibledestination;
	 @  ensures ispossibledestination == true;
	 @*/
	public void setpossibledestination()     //Function to highlight a cell to indicate that it is a possible valid move
	{
		this.setBorder(BorderFactory.createLineBorder(Color.blue,4));
		this.ispossibledestination=true;
	}
	
	/*@ 
	 @  assignable ispossibledestination;
	 @  ensures ispossibledestination == false;
	 @*/
	public void removepossibledestination()      //Remove the cell from the list of possible moves
	{
		this.setBorder(null);
		this.ispossibledestination=false;
	}

	//@  ensures ispossibledestination == \result;
	public /*@ pure @*/  boolean ispossibledestination()    //Function to check if the cell is a possible destination 
	{
		return this.ispossibledestination;
	}
	
	/*@ requires piece != null;
	 @  assignable ischeck;
	 @  ensures ischeck == true;
	 @*/
	public void setcheck()     //Function to highlight the current cell as checked (For King)
	{
		this.setBackground(Color.RED);
		this.ischeck=true;
	}
	
	/*@ 
	 @  assignable ischeck;
	 @  ensures ischeck == false;
	 @*/
	public void removecheck()   //Function to deselect check
	{
		this.setBorder(null);
		if((x+y)%2==0)
			setBackground(new Color(113,198,113));
		else
			setBackground(Color.white);
		this.ischeck=false;
	}

	//@  ensures ischeck == \result;
	public /*@ pure @*/  boolean ischeck()    //Function to check if the current cell is in check
	{
		return ischeck;
	}
}