package chess;

import java.util.ArrayList;

import chess.Cell;


/**
 * This is the Piece Class. It is an abstract class from which all the actual pieces are inherited.
 * It defines all the function common to all the pieces
 * The move() function an abstract function that has to be overridden in all the inherited class
 * It implements Cloneable interface as a copy of the piece is required very often
 */
public abstract class Piece implements Cloneable{

	// public invariant color >= 0;
	// public invariant (\forall int i; 0 <= i && i < possiblemoves.size(); possiblemoves.get(i) != null);
	
	//Member Variables
	private /*@ spec_public @*/ int color;
	private /*@ spec_public nullable @*/ String id=null;
	private /*@ spec_public nullable @*/ String path;
	protected /*@ spec_public nullable @*/ ArrayList<Cell> possiblemoves = new ArrayList<Cell>();  //Protected (access from child classes)
	public abstract ArrayList<Cell> move(Cell state[][],int x,int y);  //Abstract Function. Must be overridden
	
	//Id Setter
	/*@ public initially id != null; 
	 @  requires  id != null;
	 @  assignable id;
	 @  ensures \old(id) == id;
	 @*/
	public void setId(String id)
	{
		this.id=id;
	}
	
	//Path Setter
	/*@ requires  path != null;
      @  assignable path;
	  @  ensures \old(path) == path;
	  @ */
	public void setPath(String path)
	{
		this.path=path;
	}
	
	//Color Setter
	/*@ requires  c >= 0;
	 @  assignable c;
	 @  ensures \old(c) == c;
	 @*/
	public void setColor(int c)
	{
		this.color=c;
	}
	
	//Path getter
	// @ ensures this.path == \result
	public /*@ pure @*/ String getPath()
	{
		return path;
	}
	
	//Id getter
	// @ ensures this.id == \result	
	public /*@ pure @*/ String getId()
	{
		return id;
	}
	
	//Color Getter
	// @ ensures this.color == \result
	public /*@ pure @*/ int getcolor()
	{
		return this.color;
	}
	
	//Function to return the a "shallow" copy of the object. The copy has exact same variable value but different reference
	/*@ requires  path != null;
	 @  assignable path;
	 @  ensures \result.color == color && 
	 @   \result.id == id && 
	 @   \result.path == path && 
	 @   \result.possiblemoves == possiblemoves;
	 @*/
	public Piece getcopy() throws CloneNotSupportedException
	{
		return (Piece) this.clone();
	}
}