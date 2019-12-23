/* Reasoning About Programs - Robot Maze
 * Author: Ayoob
 * Creation date: 12/10/2019
 */
MACHINE
    Robot

// Include the functions and methods from Maze.mch
INCLUDES
    Maze
    
PROMOTES
    isVisitedSquare
// Include the functions and methods from Maze.mch

SETS
    DIRECTIONS = {North, South, East, West};

    STATUS_MESSAGE = {TeleportedSuccessfully,InvalidTeleportToEndWhileInStart,InvalidTeleportToBlockedSquare,MovedSuccessfully,InvalidMoveBorderWall,InvalidMoveBlockedSquare,InvalidInput}
    
VARIABLES

    travelledDirection,vacatedPath,currentX,currentY

/* State Invariants and their Initialization
 * 
 */
INVARIANT
    
    travelledDirection: seq(DIRECTIONS) & vacatedPath: seq(INTEGER * INTEGER) & 
    currentX: NATURAL & currentY:NATURAL &
    currentX: lengthRange & currentY: widthRange
    
INITIALISATION
    
    travelledDirection := [] ||
    vacatedPath := [] ||
    currentX := 1 ||
    currentY := 1

/* Create the animation functions for the grid.
 *
 */
DEFINITIONS
    ANIMATION_FUNCTION_DEFAULT == ({ y,x,c |y:1..5 & x:1..7 & c=0 });
    ANIMATION_FUNCTION1 == ({ y,x,c |y:1..5 & x:1..7 & c=1 & (x,(y - 6) * -1) : BlockedSquares });
    ANIMATION_FUNCTION2		== ({ y,x,c |y:1..5 & x:1..7 & c=2 & x = currentX & (y - 6) * -1 = currentY });
    //Image loading
    ANIMATION_IMG0 == "images/noblock.gif";
    ANIMATION_IMG1 == "images/block.gif";
    ANIMATION_IMG2 == "images/robot.gif";


OPERATIONS
// Enquiry Methods for Robot - As specified by the coursework specifications

/* Gets the Current position of the Robot - Checks for the following set constraints
 * 1. Returns a maplet of the X and Y coordinate.
 */

   getPosition  <-- getCurrentPosition  =
   BEGIN 
       getPosition := (currentX, currentY)
   END;

/* Gets whether the Robot has found the exit square in Maze.
 * 1. Returns a boolean SET.
 */
   foundExit  <-- foundEndSquare  =
   IF
       ((xCurrent |-> yCurrent) : EndingSquare) 
   THEN
       foundExit := Yes
   ELSE
       foundExit := No
   END;

//Robots path travelled through the maze .

   robotsRoute  <-- getPath  =
   BEGIN 
       robotsRoute := travelledPath
   END;

// Operations Methods
/* Moves the Robot North - Checks for the following set constraints
 * 1. Moved square is not a Blocked Square
 * 2. Moved square is not outside the border of the wall
 */

   movedStatus  <-- moveNorth  =
    IF
        ((currentX|-> currentY  + 1 ) /: BlockedSquares & 
        (currentY + 1 : widthRange))
    THEN
        currentY := currentY + 1 ||
        travelledDirection := travelledDirection <- North ||
        vacatedPath := vacatedPath <- (currentX |-> currentY) ||
        currentStatus(currentX, currentY +1, vacatedPath <- (currentX  |-> currentY)) ||
        movedStatus := MovedSuccessfully
    ELSIF
        (currentY +1 /:  widthRange)
	      THEN 
	          movedStatus := InvalidMoveBorderWall
	 ELSE 
	     movedStatus := InvalidMoveBlockedSquare
    END;

/* Moves the Robot South - Checks for the following set constraints
 * 1. Moved square is not a Blocked Square
 * 2. Moved square is not outside the border of the wall
 */ 

   movedStatus  <-- moveSouth  =
    IF
        ((currentX |-> currentY -1) /: BlockedSquares & 
        (currentY - 1 :  widthRange))
    THEN
        currentY := currentY - 1 ||
        travelledDirection := travelledDirection <- South ||
        vacatedPath := vacatedPath <- (currentX |-> currentY) ||
        currentStatus(currentX, currentY -1, vacatedPath <- (currentX  |-> currentY)) ||
        movedStatus := MovedSuccessfully
    ELSIF
        (currentY - 1 /:  widthRange)
	      THEN 
	          movedStatus := InvalidMoveBorderWall
	 ELSE 
	     movedStatus := InvalidMoveBlockedSquare
    END;

/* Moves the Robot East - Checks for the following set constraints
 * 1. Moved square is not a Blocked Square
 * 2. Moved square is not outside the border of the wall
 */

   movedStatus  <-- moveEast  =
    IF
        ((currentX +1  |-> currentY) /: BlockedSquares & 
        (currentX + 1 : lengthRange))
    THEN
        currentX := currentX + 1 ||
        travelledDirection := travelledDirection <- East ||
        vacatedPath := vacatedPath <- (currentX  |-> currentY) ||
        currentStatus(currentX + 1, currentY, vacatedPath <- (currentX  |-> currentY)) ||
        movedStatus := MovedSuccessfully
    ELSIF
        (currentX + 1 /:  lengthRange)
	      THEN 
	          movedStatus := InvalidMoveBorderWall
	 ELSE 
	     movedStatus := InvalidMoveBlockedSquare
    END;
    
/* Moves the Robot West - Checks for the following set constraints
 * 1. Moved square is not a Blocked Square
 * 2. Moved square is not outside the border of the wall
 */

   movedStatus  <-- moveWest  =
    IF
        ((currentX  - 1 |-> currentY) /: BlockedSquares & 
        (currentX - 1 : lengthRange))
    THEN
        currentX := currentX - 1 ||
        travelledDirection := travelledDirection <- West ||
        vacatedPath := vacatedPath <- (currentX |-> currentY) ||
        currentStatus(currentX - 1, currentY, vacatedPath <- (currentX  |-> currentY)) ||
        movedStatus := MovedSuccessfully
    ELSIF
        (currentX - 1 /: lengthRange)
	      THEN 
	          movedStatus := InvalidMoveBorderWall
	 ELSE 
	     movedStatus := InvalidMoveBlockedSquare
    END;

/* Attempts to Teleport the Robot - Checks for the following set constraints
 * 1. X and Y within range of the border wall
 * 2. X and Y not a element of Blocked square AND
 * 3. Not in the starting square OR ending square 
 */

   teleportStatus  <-- teleport(xTeleport, yTeleport)  =
   IF
       xTeleport : lengthRange &
       yTeleport : widthRange 
   THEN
       IF
           ((xTeleport |-> yTeleport) /: BlockedSquares &
            ((xTeleport |-> yTeleport) /: EndingSquare or
            (currentX |-> currentY) /: StartingSquare))
       THEN
           currentX := xTeleport ||
           currentY := yTeleport ||
           teleportStatus := TeleportedSuccessfully ||
		     vacatedPath := vacatedPath <- (currentX |-> currentY) ||
		     currentStatus(xTeleport, yTeleport, vacatedPath <- (currentX  |-> currentY))
       ELSE IF
               ((xTeleport |-> yTeleport) : BlockedSquares)
           THEN
               teleportStatus := InvalidTeleportToBlockedSquare
       ELSE
            teleportStatus := InvalidTeleportToEndWhileInStart
    
           END
       END

    ELSE
        teleportStatus := InvalidInput
   END
   
END
