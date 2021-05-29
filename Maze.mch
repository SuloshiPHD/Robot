/* Reasoning About Programs coursework
 * Machine : Maze
 * Maze.mch
 * Author: Duneesha Suloshini
 * ID : 2017336/ w1697801
 * Creation date: 25/11/2020
 */
MACHINE
    Maze

SETS
   MESSAGE = {Yes, No}

CONSTANTS

    entrySquare, exitSquare, xAxisRobot, yAxisRobot, mazeWallbarriers

PROPERTIES
    
    xAxisRobot <: NATURAL1 &  xAxisRobot = 1..7 &
    yAxisRobot <: NATURAL1 &  yAxisRobot = 1..5 &
    entrySquare: NATURAL1 <-> NATURAL1 &  entrySquare = {(1 |-> 1)} &
    exitSquare: NATURAL1 <-> NATURAL1 & exitSquare = {(1 |-> 5)} & 
    mazeWallbarriers: NATURAL1 <-> NATURAL1 &
    mazeWallbarriers = {(1 |-> 3), (2 |-> 1), (2 |-> 3), (2 |-> 5), (3 |-> 3), (4 |-> 2), (4 |-> 3), (4 |-> 4), (6 |-> 1), (6 |-> 2), (6 |-> 4), (7 |-> 4)}

VARIABLES

    visitedXsquare, visitedYsquare, visitedRobotpath

INVARIANT
    
    visitedXsquare: NATURAL &
    visitedYsquare: NATURAL &
    visitedRobotpath: seq(INTEGER * INTEGER)

INITIALISATION
    
    visitedRobotpath := [] || visitedXsquare := 0 || visitedYsquare := 0

OPERATIONS

// updating the robot's route on the maze
/*  keeping a record of the squares visited a square "has been visited" only after the robot
has been on it and then has moved off it. */

   updateMaze(xAxis, yAxis, robotRoute)  =
   PRE
       xAxis: NATURAL1 & yAxis: NATURAL1 & robotRoute: seq(INTEGER * INTEGER)    
   THEN
       visitedRobotpath := robotRoute ||
       visitedXsquare := xAxis ||
       visitedYsquare := yAxis
   END;
   
// searching whether the Robot has arrived to destination (exit square)
/* outputs yes if the robot is currently in the exit square of the maze, no otherwise. */

   hasExitFound  <-- foundExit  =
   IF
       ((visitedXsquare |-> visitedYsquare) : exitSquare) 
   THEN
       hasExitFound := Yes
   ELSE
       hasExitFound := No
   END;

// method to get the already visited squares on the maze
/* - inputs a square(x,y) and reports yes if that square has been previously visited by
the robot, no otherwise. */

   isVisited  <-- hasVisitedSquare(xCellpoint, yCellpoint)  =
   PRE    
       xCellpoint : xAxisRobot & yCellpoint : yAxisRobot
   THEN
       IF
           (xCellpoint |-> yCellpoint : ran(visitedRobotpath)) 
       THEN
           isVisited := Yes
       ELSE
           isVisited := No
       END
   END;

//Fetch the route  through the maze of the robot

   path  <-- robotsRoute =
   BEGIN 
       path := visitedRobotpath
   END
   
END

