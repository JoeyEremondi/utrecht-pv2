/*
Joseph Eremondi
UU# 4229924
Program Verification Project 2
April 8, 2015
*/

#define N 4

#define NOT_SET 255

//#define VOTE 0
//#define FOUND_LEADER 1

//byte N = 1;

//First bit denotes whether we're sending our vote for leader 
//Or whether we're passing on which leader was found
chan Msg[N] = [1] of {byte}//{bit, byte};

//We use this to verify that all processes agree on the leader
byte globalLeader = NOT_SET;

//We use this to verify that all processes terminate
byte numDone = 0;

//Loops, starting N processes, giving them id's in order
//TODO make non-deterministic
active proctype starter()
{

  byte i = 0;
  do
    :: i < N -> {run RingMember(i); i++ }
    :: else -> {break;}
  od;

}

//Our main procedure
proctype RingMember(byte id) {
  byte msg;
  bool msgType;
  byte foundLeader = NOT_SET;
  
  printf("!! Starting process %d", id);
  Msg[(id + 1) % N] ! id;
  //printf("Sending %d %d to %d\n", VOTE, id, (id + 1) % N);  
  
  do
    //If we have a waiting message, take it from the queue
    //And perform the corresponding action
    //:: empty(Msg[id]) -> {printf("DO 1 id %d\n", id); skip;}
    :: 
	//nempty(Msg[id]) -> {
	globalLeader == NOT_SET && nempty(Msg[id])  -> {
	printf("DO 2 id %d\n", id);
	Msg[id] ? msg ;
	printf("Recieved %d %d\n", msgType, msg);
	if
	  //Less than our ID? Ignore it.
	  :: msg < id -> 
	    {skip;}
	  //Greater than us? Pass it along in the chain
	  :: msg > id ->
	    {
	      Msg[(id + 1) % N] ! msg;
	      //printf("Sending %d %d\n", VOTE, msg)
	    }
	  //Is it our ID? Then we are the leader.
	  //Send the next process in the ring a message saying that we're the leader
	  :: msg == id -> 
	    {
	      //foundLeader = id;
	      //printf("Sending %d %d\n", FOUND_LEADER, id);
	      Msg[(id + 1) % N] ! id;
	      globalLeader = id
	    }

	fi;
      }
      
    //Or, if we got a message telling us who the leader is,
    //store it as the global leader (only used for verification)
    //then exit the loop
    :: globalLeader != NOT_SET -> //TODO fix
	{ 
	  numDone++; 
	  printf("DO 3 id %d\n", id);
	  //globalLeader = foundLeader; 
	  break
	}
  od;
  
  printf("Done in thread %d\n", id);
  //numDone++;
  printf("NumDone %d\n", numDone)
  
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
     //&& ( globalLeader == NOT_SET U globalLeader == N-1 ) 
    //&&  ((globalLeader == N-1) -> [](globalLeader == N-1) ) 
  } 
