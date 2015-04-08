/*
Joseph Eremondi
UU# 4229924
Program Verification Project 2
April 8, 2015
*/

//The number of processes allowed in our ring
#ifndef N
#define N 5
#endif

#define NOT_SET N+1

#define VOTE 0
#define FOUND_LEADER 1

//First bit denotes whether we're sending our vote for leader 
//Or whether we're passing on which leader was found
chan Msg[N] = [1] of {bit, byte};

//We use this to verify that all processes agree on the leader
byte globalLeader = NOT_SET;
byte leaderPID = NOT_SET;

//We use this to verify that all processes terminate
byte numDone = 0;

//Loops, starting N processes, giving them id's in order
init
{

  //Array for which IDs have been assiged so far
  bool idAssigned[N] = false;
  
  
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
//and that once the leader has a value,
//its value never changes
ltl allHaltAndAgree { 
    //Eventually all processes halt
    (<>( [] ( (numDone == N)  ) )) 
    // The leader is not set until it has the correct value
    && ( globalLeader == NOT_SET U globalLeader == N-1 )
    // Once the leader has the correct value, it stays correct
    &&  []((globalLeader == N-1) -> [](globalLeader == N-1) ) 
  } 
