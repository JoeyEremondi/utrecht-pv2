/*
Joseph Eremondi
UU# 4229924
Program Verification Project 2
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

//Array storing the ID for each process
byte idVals[NMAX];

//We use this to verify that all processes agree on the leader
byte globalLeader = NOT_SET;
byte leaderPID = NOT_SET;

//We use this to verify that all processes terminate
byte numDone = 0;

//Loops, starting N processes, giving them id's in order
//TODO make non-deterministic
active proctype starter()
{
  //Non-deterministically choose an N less than our max
  //This unforunately can be quite slow, so we choose a small range
  do
    :: N > NMIN -> {N--}
    :: true -> {break}
  od;
  
  
  byte i;
  byte j;
  
  //Initialize our array of ID values in order
  i = 0;
  do
    :: i < N -> {idVals[i] = i; i++ }
    :: else -> {break;}
  od;
  
  //Non-deterministically shuffle our array of process IDs
  //Performing at most N^2 swaps
  byte numSwaps = 0;
  do
    :: numSwaps < N*N -> {
      i = 0;
      j = 0;
      byte counter = 0;
      do
	:: counter < N-1 -> {i++; counter++}
	:: break
      od;
      counter = 0;
      do
	:: counter < N-1 -> {j++; counter++}
	:: break
      od;
      byte tmp = idVals[i];
      idVals[i] = idVals[j];
      idVals[j] = tmp;
      numSwaps++
    }
    :: {break}
  od;

  //Create our ring-voting processes
  i = 0;
  do
    :: i < N -> {run RingMember(idVals[i]); i++ }
    :: else -> {break}
  od;
  
  /*
  //Print our result when the output has finished
  do
    :: numDone == N -> 
    { 
      printf("%d processes, leader had ID %d and _pid %d\n", N, globalLeader, leaderPID ); 
      break 
      
    }
    :: else -> skip
  od */

}

//Our main procedure
proctype RingMember(byte id) {
  byte msg;
  bool msgType;
  byte foundLeader = NOT_SET;
  
  printf("Starting process %d with id %d\n", _pid, id);
  
  Msg[(id + 1) % N] ! VOTE, id;
  
  do
    //If we have a waiting message, take it from the queue
    //And perform the corresponding action
    :: foundLeader == NOT_SET && nempty(Msg[id])  -> {
	Msg[id] ? msgType, msg ;
	if
	  //Less than our ID? Ignore it.
	  :: msgType == VOTE && msg < id -> 
	    {skip;}
	  //Greater than us? Pass it along in the chain
	  :: msgType == VOTE && msg > id ->
	    {
	      Msg[(id + 1) % N] ! VOTE, msg;
	    }
	  //Is it our ID? Then we are the leader.
	  //Send the next process in the ring a message saying that we're the leader
	  :: msgType == VOTE && msg == id -> 
	    {
	      Msg[(id + 1) % N] ! FOUND_LEADER, id;
	      //Set the winning pid to our pid, used for printing
	      leaderPID = _pid;
	    }
	  //Did the process before us find the leader?
	  //If so, we store it
	  :: msgType == FOUND_LEADER -> 
	    {
	      foundLeader = msg;
	      Msg[(id + 1) % N] ! FOUND_LEADER, msg
	    }

	fi
      }
      
    //If we've determined who the leader is, exit the loop
    //We store our leader in globalLeader, but this does not affect the flow of the program
    //Rather, it is used in the LTL formulas to ensure all processes agree on the leader
    :: foundLeader != NOT_SET ->
	{ 
	  globalLeader = foundLeader; 
	  break
	}
  od;
  
  //Mark that this process halted
  numDone++  
}

//Our verification conditions
//We check that the number of halted processes 
//Is equal to the total number of processes (not including init).
//We verify this by checking that eventually, 
//the number of halted processes is always N.
//
//We also check that the the leader value is not set 
//until a process sets it to the correct value
//and that once the leader has the correct value,
//its value never changes
ltl allHaltAndAgree { 
    (<>( [] ( (numDone == N)  ) )) 
    && ( globalLeader == NOT_SET U globalLeader == N-1 )
    &&  []((globalLeader == N-1) -> [](globalLeader == N-1) ) 
  } 
