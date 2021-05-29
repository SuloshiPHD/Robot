/* Reasoning About Programs coursework
 * Machine : Robot
 * Robot.mch
 * Author: Duneesha Suloshini
 * ID : 2017336/ w1697801
 * Creation date: 25/11/2020
 */
 
MACHINE
    Robot

INCLUDES
    Maze
    
PROMOTES
    foundExit, hasVisitedSquare, robotsRoute
    
SETS
    DIRECTIONS = {North, South, East, West};
  

    STATUS_MESSAGE = {
        SuccessfullyMoved, 
        CannotMoveInternalMazewallDetected,
        CannotMoveExternalBoundarywallDetected,       
        SuccessfullyTeleported,
        CannotTeleportToExitOrOnStartSquare,
        CannotTeleportToMazeInternalWalls
    }
    
VARIABLES

    visitedRobotDirections, visitedPathofRobot, xPosition, yPosition
        
INVARIANT
    
    visitedRobotDirections: seq(DIRECTIONS) &
    visitedPathofRobot: seq(INTEGER * INTEGER) &
    xPosition: NATURAL1 &
    yPosition: NATURAL1 &
    xPosition: xAxisRobot &
    yPosition: yAxisRobot
    
INITIALISATION
    
    visitedRobotDirections := [] ||
    visitedPathofRobot := [] ||
    xPosition := 1 ||
    yPosition := 1

OPERATIONS

//Robot's movement to the North direction

   outputMessage  <-- moveNorth  =
    IF
        // xPosition and yPosition as an ordered pair(maplet)
        ((xPosition |-> yPosition  + 1 ) /: mazeWallbarriers & (yPosition + 1 : yAxisRobot)) 
    THEN
        yPosition := yPosition + 1 ||
        //append element North to tail of the sequences of visited directions
        visitedRobotDirections := visitedRobotDirections <- North ||
        //append element of route (x and y position) to the tail of the visited paths sequence
        visitedPathofRobot := visitedPathofRobot <- (xPosition |-> yPosition) ||
        updateMaze(xPosition, yPosition +1, visitedPathofRobot <- (xPosition  |-> yPosition)) ||
        outputMessage := SuccessfullyMoved
    ELSIF
        (yPosition +1 /:  yAxisRobot)
	      THEN 
	          outputMessage := CannotMoveExternalBoundarywallDetected
	 ELSE 
	     outputMessage := CannotMoveInternalMazewallDetected
    END;

//Robot's movement to the South direction 

   outputMessage  <-- moveSouth  =
    IF
        ((xPosition |-> yPosition -1) /: mazeWallbarriers &  (yPosition - 1 :  yAxisRobot))
    THEN
        yPosition := yPosition - 1 ||
        visitedRobotDirections := visitedRobotDirections <- South ||
        visitedPathofRobot := visitedPathofRobot <- (xPosition |-> yPosition) ||
        updateMaze(xPosition, yPosition -1, visitedPathofRobot <- (xPosition  |-> yPosition)) ||
        outputMessage := SuccessfullyMoved
    ELSIF
        (yPosition - 1 /:  yAxisRobot)
	      THEN 
	          outputMessage := CannotMoveExternalBoundarywallDetected
	 ELSE 
	     outputMessage := CannotMoveInternalMazewallDetected
    END;

//Robot's movement to the East direction

   outputMessage  <-- moveEast  =
    IF
        ((xPosition +1  |-> yPosition) /: mazeWallbarriers &  (xPosition + 1 : xAxisRobot))
    THEN
        xPosition := xPosition + 1 ||
        visitedRobotDirections := visitedRobotDirections <- East ||
        visitedPathofRobot := visitedPathofRobot <- (xPosition  |-> yPosition) ||
        updateMaze(xPosition + 1, yPosition, visitedPathofRobot <- (xPosition  |-> yPosition)) ||
        outputMessage := SuccessfullyMoved
    ELSIF
        (xPosition + 1 /:  xAxisRobot)
	      THEN 
	          outputMessage := CannotMoveExternalBoundarywallDetected
	 ELSE 
	     outputMessage := CannotMoveInternalMazewallDetected
    END;
    
// Robot's movement to the West direction

   outputMessage  <-- moveWest  =
    IF
        ((xPosition  - 1 |-> yPosition) /: mazeWallbarriers & 
        (xPosition - 1 : xAxisRobot))
    THEN
        xPosition := xPosition - 1 ||
        visitedRobotDirections := visitedRobotDirections <- West ||
        visitedPathofRobot := visitedPathofRobot <- (xPosition |-> yPosition) ||
        updateMaze(xPosition - 1, yPosition, visitedPathofRobot <- (xPosition  |-> yPosition)) ||
        outputMessage := SuccessfullyMoved
    ELSIF
        (xPosition - 1 /: xAxisRobot)
	      THEN 
	          outputMessage := CannotMoveExternalBoundarywallDetected
	 ELSE 
	     outputMessage := CannotMoveInternalMazewallDetected
    END;
    
//outputs the current position of the robot in the maze. 

   currentPosition  <-- getPosition  =
   BEGIN 
       currentPosition := {(xPosition, yPosition)}
   END;

//Teleport to a path square within the maze
/* The operation inputs a square that the Robot attempts to teleport to.
If the input square is suitable for the Robot to teleport to it does so and reports success.*/

   teleportMessage  <-- teleport(xCellpoint, yCellpoint)  =
   PRE
       xCellpoint : xAxisRobot & yCellpoint : yAxisRobot 
   THEN
       IF
           ((xCellpoint |-> yCellpoint) /: mazeWallbarriers &
            ((xCellpoint |-> yCellpoint) /: exitSquare or (xPosition |-> yPosition) /: entrySquare))
       THEN
           xPosition := xCellpoint ||
           yPosition := yCellpoint ||
           teleportMessage := SuccessfullyTeleported ||
		     visitedPathofRobot := visitedPathofRobot <- (xPosition |-> yPosition) ||
		     updateMaze(xCellpoint, yCellpoint, visitedPathofRobot <- (xPosition  |-> yPosition))
       ELSE IF
               ((xCellpoint |-> yCellpoint) : mazeWallbarriers)
           THEN
               teleportMessage := CannotTeleportToMazeInternalWalls
       ELSE
            teleportMessage := CannotTeleportToExitOrOnStartSquare
    
           END
       END
   END
   
END


