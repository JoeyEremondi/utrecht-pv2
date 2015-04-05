/*
Joseph Eremondi
UU# 4229924
Program Verification Project 2: Extension
April 8, 2015
*/

//Change these values to make the program run faster or slower
//The number of processes in our ring
#define N 7


#define NOT_SET (N+1)

#define VOTE 0
#define FOUND_LEADER 1

//byte N = N;

//First bit denotes whether we're sending our vote for leader 
//Or whether we're passing on which leader was found
chan Msg[N] = [1] of {bit, byte};

//We use this to verify that all processes agree on the leader
//And as a "lock" ensuring that once a process sees itself
//no other processes think they are the leader
byte globalLeader = NOT_SET;

//We use this to verify that all processes terminate
byte numDone = 0;


//Loops, starting N processes, giving them id's in order
init
{

  
  //Create our ring-voting processes
  //Since our process is non-deterministic, we don't bother assigning different IDs to PIDs
  byte i = 0;
  do
    :: i < N -> { run RingMember(i); i++ }
    :: else -> {break}
  od;
  
  
  do
    :: numDone == N -> {
      printf("Found leader with  ID %d, out of %d processes\n", globalLeader, N);
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
      
  Msg[(id + 1) % N] ! VOTE, id;
  
  do
    //If we have a waiting message, take it from the queue
    //And perform the corresponding action
    :: foundLeader == NOT_SET && nempty(Msg[id])  -> {
	Msg[id] ? msgType, msg ;
	if
	  //Pass on all votes that aren't for us
	  //This makes the process non-deterministic: the order the processes run
	  //determine the order votes are passed on
	  :: msgType == VOTE && msg != id  ->
	    {
	      Msg[(id + 1) % N] ! VOTE, msg
	    }
 
	  //Is it our ID? Then we check of another thread has declared itself the leader
	  //If not, we declare ourselves the leader, and
	  //Send the next process in the ring a message saying that we're the leader
	  :: msgType == VOTE && msg == id -> 
	    atomic{
	      if
		:: globalLeader == NOT_SET -> {
		  globalLeader = id;
		  Msg[(id + 1) % N] ! FOUND_LEADER, id
		}
	        :: else -> {skip}
	      fi

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
	  //Assert that, unless we're the first to set it, we are not changing the leader value
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
