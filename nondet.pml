/*
Joseph Eremondi
UU# 4229924
Program Verification Project 2: Extension
April 8, 2015
*/

//Change these values to make the program run faster or slower
//They indicate the max and minimum number of processes allowed in our ring
#define NMIN 4
#define NMAX 4


#define NOT_SET 255

#define VOTE 0
#define FOUND_LEADER 1

byte N = NMAX;

//First bit denotes whether we're sending our vote for leader 
//Or whether we're passing on which leader was found
chan Msg[NMAX] = [1] of {bit, byte};

//We use this to verify that all processes agree on the leader
byte globalLeader = NOT_SET;

//Just used for printing, to show that different PID's 
//don't always get the same ID
byte leaderPID = NOT_SET;

//We use this to verify that all processes terminate
byte numDone = 0;

//This serves as a "lock", whichever thread grabs it first becomes the leader
bool leaderFound = false;

//Loops, starting N processes, giving them id's in order
init
{
  //Non-deterministically choose an N less than our max
  //This unforunately can be quite slow, so we choose a small range
  do
    :: N > NMIN -> {N--}
    :: true -> {break}
  od;
  
  //Array for which IDs have been assiged so far
  bool idAssigned[NMAX] = false;
  
  
  
  
  //Create our ring-voting processes
  //We keep track of the number of IDs we've assigned so far
  //For each iteration of our outer loop, we non-deterministically skip some
  //number of indices
  byte i = 0;
  do
    :: i < N -> {
      byte numSkipped = 0;
      byte j = 0;
      do 
	//Option 1: skip a free value and record that we skipped it
	:: ( j < N-1 && (!idAssigned[j]) && numSkipped < (N - i - 1)) -> {j++ ; numSkipped++ }
	//Option 2: start a process with the current value, then break
	:: !idAssigned[j] -> {idAssigned[j] = true; run RingMember(j); break}
	//Option 3: skip an already used ID
	:: idAssigned[j] && j < N-1 -> {j++}
      od;
      i++
    }
    :: else -> {break}
  od;
  
  do
    :: numDone == N -> {
      printf("Found leader with PID %d, ID %d, out of %d processes\n", leaderPID, globalLeader, N);
      break
    }
  od;
  

}

//Our main procedure
//Basic idea: Each process non-deterministically decides whether or
//not to discard a vote for an ID less than its own
//When a process sees its own ID, it sends a FOUND_LEADER message
//around the ring. Each process decides that the leader is the first
//id it sees in a FOUND_LEADER message twice.
//Because FOUND_LEADER messages are never discarded,
//the messages never "pass" each other in the ring, so there
//is a unique first id that each process sees twice
proctype RingMember(byte id) {
  byte msg;
  bool msgType;
  byte foundLeader = NOT_SET;
  
  byte skipsAllowed = 0;
  
  printf("Starting process %d with id %d\n", _pid, id);
  
  Msg[(id + 1) % N] ! VOTE, id;
  
  do
    //If we have a waiting message, take it from the queue
    //And perform the corresponding action
    :: foundLeader == NOT_SET && nempty(Msg[id])  -> {
	Msg[id] ? msgType, msg ;
	if
	  //Option 1: If we've skipped less than N times, send our ID
	  //instead of the one we recieved in the message
	  :: msgType == VOTE && msg != id && skipsAllowed > 0 -> {
	      Msg[(id + 1) % N] ! VOTE, id;
	      skipsAllowed--;
	  }
	  //Option 2: If it's not our ID, pass along the message
	  :: msgType == VOTE && msg != id  ->
	    {
	      Msg[(id + 1) % N] ! VOTE, msg;
	    }
	  //Is it our ID? Then we check of another thread has declared itself the leader
	  //If not, we declare ourselves the leader, and
	  //Send the next process in the ring a message saying that we're the leader
	  :: msgType == VOTE && msg == id -> 
	    atomic{
	      if
		:: !leaderFound -> {
		  leaderFound = true;
		  Msg[(id + 1) % N] ! FOUND_LEADER, id
		}
	        :: else -> {skip}
	      fi
	      //Set the winning pid to our pid, used for printing
	      leaderPID = _pid;
	    }
	  //Get a notification of who the leader is
	  //And if it isn't us, pass it along
	  :: msgType == FOUND_LEADER -> 
	    {
	      foundLeader = msg;
	      if
		:: msg != id -> {Msg[(id + 1) % N] ! FOUND_LEADER, msg}
		:: else -> {skip}
	      fi
	    }

	fi
      }
      
    //If we've determined who the leader is, exit the loop
    //We store our leader in globalLeader, but this does not affect the flow of the program
    //Rather, it is used in the LTL formulas to ensure all processes agree on the leader
    :: foundLeader != NOT_SET ->
	{ 
	  printf("Proc %d found leader %d\n", id, foundLeader, globalLeader );
	  //Assert that, unless we're the first to set it, we are not changing the leader value
	  //This is redundant in the deterministic version
	  assert(globalLeader == NOT_SET || globalLeader == foundLeader );
	  globalLeader = foundLeader; 
	  break
	}
  od;
  
  //Mark that this process halted
  numDone++;
}

//Our verification conditions
//We check that the number of halted processes 
//Is equal to the total number of processes (not including init).
//We verify this by checking that eventually, 
//the number of halted processes is always N.
//
//We also check that the the leader value is not set 
//until a process sets it to the correct value
//and that once the leader has a value,
//its value never changes
ltl allHaltAndAgree { 
    //Eventually all processes halt
    (<>( [] ( (numDone == N)  ) )) 
    //Once the leader is set, it is never "un"-set
    &&  []((globalLeader != NOT_SET) -> [](globalLeader != NOT_SET) ) 
  } 
