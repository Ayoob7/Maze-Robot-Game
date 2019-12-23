/* Reasoning About Programs - Robot Maze
 * Author: Ayoob
 * Creation date: 12/10/2019
 */
MACHINE
    Maze

// Static variable initialization. Start Square, End Square, length and width of the grid and the Blocked Squares.
CONSTANTS

    StartingSquare,
    EndingSquare,
    lengthRange,
    widthRange,
    BlockedSquares

// Variable setting Start Square, End Square, length and width of the grid and the Blocked Squares.
PROPERTIES
    
    lengthRange <: NATURAL & lengthRange = 1..7 &
    widthRange <: NATURAL & widthRange = 1..5 &
    StartingSquare: NATURAL <-> NATURAL & StartingSquare = {(1 |-> 1)} &
    EndingSquare: NATURAL <-> NATURAL & EndingSquare = {(1 |-> 5)} & 
    BlockedSquares: NATURAL <-> NATURAL &
    BlockedSquares = {(1 |-> 3), (2 |-> 3), (2 |-> 5), (2 |-> 1), (4 |-> 2), (4 |-> 3), (4 |-> 4), (3 |-> 3), (6 |-> 1), (6 |-> 2), (6 |-> 4), (7 |-> 4)}


// State varibles such as the current position of robot in grid in X and Y coordinates and travelled path.
VARIABLES

    xCurrent,
    yCurrent,
    travelledPath

SETS
    BOOLEAN_SET = {No, Yes, InputInvalid}

// Invariants
INVARIANT
    
    xCurrent: NATURAL &
    yCurrent: NATURAL &
    travelledPath: seq(INTEGER * INTEGER)

// Invariants initialisation
INITIALISATION
    
    travelledPath := [] ||
    xCurrent := 0 ||
    yCurrent := 0

OPERATIONS

// Enquiry Methods for Maze - As specified by the coursework specifications

/* Gets the Current status of the Maze - Checks for the following set constraints
 * 1. Returns current X and Y coordinate and travelled path.
 */

   currentStatus(xValue, yValue, path)  =
   PRE
       xValue: NATURAL & yValue: NATURAL & path: seq(INTEGER * INTEGER)    
   THEN
       travelledPath := path ||
       xCurrent := xValue ||
       yCurrent := yValue
   END;


/* Get to see whether the square is visited by robot or not.
 * Pre conditions are the inputs should be within the border.
 * if its true then we get the range if 
 */

   visitedSquare  <-- isVisitedSquare(xValue, yValue)  =
    IF (xValue : lengthRange & yValue : widthRange)

    THEN
        IF
            (xValue |-> yValue : ran(travelledPath)) 
        THEN
            visitedSquare := Yes
        ELSE
            visitedSquare := No
        END

     ELSE
        visitedSquare := InputInvalid
     END
   
END
