
-- 3-state MSI protocal

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------

const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  -- TODO: What is VC?
  VC0: 0;                -- low priority
  VC1: 1;
  VC2: 2;
  QMax: 2;
  NumVCs: VC2 - VC0 + 1;
  NetMax: ProcCount+1;

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------

type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };

  VCType: VC0..NumVCs-1;

  MessageType: enum {  ReadReq,         -- request for data / shared
                       ReadAck,         -- read ack (w/ data)

                       ReadExReq,      -- request for data / exclusivity
                       ReadExAck,      -- read exclusive ack (w/ data)
                                             
					             WBReq,           -- writeback request (w/ data)
					             WBAck,           -- writeback ack 
                           
                       RecallReq, 				-- Request & invalidate a valid copy
                       InvReq,             -- Request & invalidate a shared copy
                       DowngradeReq,			-- Request & downgrade a modified copy to shared state
                       DowngradeAck,			-- Acknowledge a downgrade request
                       AutoDowngradeReq			-- Request HomeNode, Send by Modified processor
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
      vc: VCType;
      val: Value;
    End;

  HomeState:
    Record
      state: enum { H_Modified, H_Invalid, H_Shared,					--stable states
      							HT_Pending, HT_S2MPending }; 								--transient states during recall
      owner: Node;	
      sharers: multiset [ProcCount] of Node;    --No need for sharers in this protocol, but this is a good way to represent them
      val: Value; 
    End;

  ProcState:
    Record
      state: enum { P_Modified, P_Invalid, P_Shared,
                  PT_I2SPending, PT_I2MPending, PT_S2MPending, PT_WritebackPending, PT_M2SPending
                  };
      val: Value;
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;  -- One multiset for each destination - messages are arbitrarily reordered by the multiset
  InBox: array [Node] of array [VCType] of Message; -- If a message is not processed, it is placed in InBox, blocking that virtual channel
  msg_processed: boolean;
  LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
	       dst:Node;
	       src:Node;
         vc:VCType;
         val:Value;
         );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.val   := val;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;

-- These arent needed for Valid/Invalid protocol, but this is a good way of writing these functions
Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Function IsSharer(n:Node) : Boolean;
Begin
  return MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        -- Send invalidation message here
        -- TODO: Check if VC is correct
        Send(InvReq, n, HomeType, VC2, UNDEFINED); 
        -- RemoveFromSharersList(n);
      endif;
    endif;
  endfor;
End;

Procedure SendAckToSharers(mtype:MessageType; val:Value; rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        -- Send message here
        Send(mtype, n, HomeType, VC1, val); 
      endif;
    endif;
  endfor;
End;

Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;  -- for counting sharers
Begin
-- Debug output may be helpful:
  put "Receiving "; put msg.mtype; put " from "; put msg.src; put " on VC"; put msg.vc; 
  put " at home -- "; put HomeNode.state;

  -- The line below is not needed in Valid/Invalid protocol.  However, the 
  -- compiler barfs if we put this inside a switch, so it is useful to
  -- pre-calculate the sharer count here
  cnt := MultiSetCount(i:HomeNode.sharers, true);


  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case H_Invalid:
    Assert (IsUndefined(HomeNode.owner) = true);
    Assert (cnt = 0) "HomeNode has sharers, but line is Invalid";
    switch msg.mtype
    case ReadReq:
      HomeNode.state := H_Shared;
      AddToSharersList(msg.src);
      Send(ReadAck, msg.src, HomeType, VC1, HomeNode.val);

    case ReadExReq:
      Assert (cnt = 0) "ReadExReq with sharers";
      HomeNode.state := H_Modified;
      HomeNode.owner := msg.src;
      Send(ReadExAck, msg.src, HomeType, VC1, HomeNode.val);
      -- LastWrite := msg.val; -- TODO: Check if this is correct

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_Modified:
    Assert (IsUndefined(HomeNode.owner) = false); 
    Assert (cnt = 0) "HomeNode has sharers, but line is Modified";

    switch msg.mtype
    case ReadReq:
      -- TODO: How to handle this case?
      Assert (msg.src != HomeNode.owner) "ReadReq from owner";
      HomeNode.state := HT_Pending;
      Send(DowngradeReq, HomeNode.owner, HomeType, VC0, UNDEFINED);
      AddToSharersList(msg.src);
      AddToSharersList(HomeNode.owner);
      undefine HomeNode.owner;
    
    case ReadExReq:
      -- TODO: VC0 or VC1?
      Assert (msg.src != HomeNode.owner) "ReadExReq from owner";
      HomeNode.state := HT_Pending;
      Send(RecallReq, HomeNode.owner, HomeType, VC0, UNDEFINED);
      HomeNode.owner := msg.src;
            
    case WBReq:
    	assert (msg.src = HomeNode.owner) "Modified state: Writeback from non-owner";
      HomeNode.state := H_Invalid;
      HomeNode.val := msg.val;
      Send(WBAck, msg.src, HomeType, VC1, UNDEFINED);
      undefine HomeNode.owner

    case AutoDowngradeReq:
      Assert (msg.src = HomeNode.owner) "Modified state: AutoDowngradeReq from non-owner";
      HomeNode.state := H_Shared;
      HomeNode.val := msg.val;
      AddToSharersList(msg.src);
      Send(ReadAck, msg.src, HomeType, VC1, HomeNode.val);
      undefine HomeNode.owner;

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
  
  case H_Shared:
    Assert (IsUndefined(HomeNode.owner) = true); 
    Assert (cnt > 0) "HomeNode has no sharers, but line is Shared";

    switch msg.mtype
    case ReadReq:
      Assert (IsSharer(msg.src) = false) "ReadReq from sharer";
      Send(ReadAck, msg.src, HomeType, VC1, HomeNode.val);
      AddToSharersList(msg.src);

    case ReadExReq:
      -- TODO: Maybe another pending state? Or no pending state?
      -- Assert ((cnt > 1) | (cnt = 1 & IsSharer(msg.src))) "Error ReadExReq";
      HomeNode.state := HT_S2MPending;
      SendInvReqToSharers(msg.src);
      if (IsSharer(msg.src))
      then
         if cnt = 1
         then
           HomeNode.state := H_Modified;
           Send(ReadExAck, msg.src, HomeType, VC1, HomeNode.val);
         endif;
         RemoveFromSharersList(msg.src);
      endif;
      HomeNode.owner := msg.src;

    case WBReq:
      Assert (IsSharer(msg.src) = true) "Writeback from non-sharer";
      RemoveFromSharersList(msg.src);
      Send(WBAck, msg.src, HomeType, VC1, UNDEFINED);
      Assert (IsSharer(msg.src) = false) "Sharer not removed";
      if cnt = 1
      then
        HomeNode.state := H_Invalid;
      endif;
    -- TODONOW: Not gonna happen
    case AutoDowngradeReq:
      put "cnt = "; put cnt;
      put "Proc = "; put msg.src;
      put Procs[msg.src].state;
      Assert (IsSharer(msg.src) = true) "AutoDowngradeReq from non-sharer";
      Assert (false) "AutoDowngradeReq in shared state";
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HT_Pending:
    switch msg.mtype
    case DowngradeAck:
      Assert (IsSharer(msg.src) = true) "DowngradeAck from non-sharer";
      Assert (cnt = 2) "More than 2 sharers";
      HomeNode.state := H_Shared;
      HomeNode.val := msg.val;
      Send(ReadAck, msg.src, HomeType, VC1, HomeNode.val);
      SendAckToSharers(ReadAck, HomeNode.val, msg.src);
    case AutoDowngradeReq:
      Assert (cnt = 0 | IsSharer(msg.src) = true) "DowngradeAck from non-sharer";
      if (IsSharer(msg.src))
      then
        Assert (cnt = 2) "More than 2 sharers";
        HomeNode.state := H_Shared;
        HomeNode.val := msg.val;
        SendAckToSharers(ReadAck, HomeNode.val, msg.src);
      else
        Assert (cnt = 0) "More than 0 sharers";
        Assert (!IsUnDefined(HomeNode.owner)) "owner undefined";
        HomeNode.state := H_Modified;
        HomeNode.val := msg.val;
        Send(ReadExAck, HomeNode.owner, HomeType, VC1, HomeNode.val);
      endif;
    case WBReq:
      -- TODO: How to make sure all sharer are invalidated?
      if cnt = 0
      then
        Assert (!IsUnDefined(HomeNode.owner)) "owner undefined";
        HomeNode.state := H_Modified;
        HomeNode.val := msg.val;
        Send(ReadExAck, HomeNode.owner, HomeType, VC1, HomeNode.val);
      else
        -- case 1: The original modified processor is writing back while home is requesting it to downgrade
        -- case 2: The original modified processor is changed to shared but downgradeACK is delayed
        --         The original modified/now shared processor is writing back and that WB arrives first
        -- case 2 is now impossible, because the om/ns processor will enter PT_I2SPending state and cannot wb until acked.
        Assert (IsUnDefined(HomeNode.owner)) "Owner is defined"; 
        Assert (cnt = 2) "Sharers count is not 2";
        Assert (IsSharer(msg.src) = true) "Writeback from non-sharer";
        -- Assert (!IsUnDefined(msg.val)) "Writeback value is undefined";
        if (IsUnDefined(msg.val))
        then
          msg_processed := false; -- stall message in InBox
        else
          HomeNode.state := H_Shared;
          HomeNode.val := msg.val;
          SendAckToSharers(ReadAck, msg.val, msg.src);
          RemoveFromSharersList(msg.src);
        endif;
      endif;

    case ReadReq:
    	msg_processed := false; -- stall message in InBox

    case ReadExReq:
      msg_processed := false; -- stall message in InBox

    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HT_S2MPending:
    switch msg.mtype
    case WBReq:
      Assert (HomeNode.owner != msg.src) "Writeback from owner";
      Assert (IsSharer(msg.src) = true) "Writeback from non-sharer";
      RemoveFromSharersList(msg.src);
      if (cnt = 1)
      then
        HomeNode.state := H_Modified;
        Send(ReadExAck, HomeNode.owner, HomeType, VC1, HomeNode.val);
      endif;
    case ReadReq:
      msg_processed := false; -- stall message in InBox
    case ReadExReq:
      msg_processed := false; -- stall message in InBox
    case AutoDowngradeReq:
      -- TODONOW: Not gonna happen
      put "cnt = "; put cnt;
      Assert (IsSharer(msg.src) = true) "DowngradeReq from non-sharer";
      Assert (false) "AutoDowngradeReq in HT_S2MPending state";
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  endswitch;
End;

Procedure ProcReceive(msg:Message; p:Proc);
Begin
  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
  put " at proc "; put p; put " -- "; put Procs[p].state;

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do
  alias pv:Procs[p].val do

  switch ps
  case P_Modified:

    switch msg.mtype
    case RecallReq:
      Send(WBReq, msg.src, p, VC1, pv);
      Undefine pv;
      ps := P_Invalid;
    case DowngradeReq:
      Send(DowngradeAck, msg.src, p, VC1, pv);
      ps := PT_I2SPending;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case P_Shared:

    switch msg.mtype
    case InvReq:
      -- No need to send anything? 
      Send(WBReq, msg.src, p, VC1, pv);
      Undefine pv;
      ps := P_Invalid;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_I2SPending:

    -- TODO: Maybe need an another pending state? Do differentiate between rd and rdx
    -- Upgrade pending
    switch msg.mtype
    case ReadAck:
      pv := msg.val;
      ps := P_Shared;
    case InvReq:
    	msg_processed := false; -- stall message in InBox
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_I2MPending:

    -- TODO: Maybe need an another pending state? Do differentiate between rd and rdx
    -- Upgrade pending
    switch msg.mtype
    case ReadExAck:
      pv := msg.val;
      ps := P_Modified;
    case RecallReq:
      -- TODO: How is this possible?
    	msg_processed := false; -- stall message in InBox
    case DowngradeReq:
      msg_processed := false; -- stall message in InBox
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_M2SPending:
  -- The proc is auto downgrading
  Assert (!isundefined(pv)) "Error: Unexpected undefined value";
    switch msg.mtype
    case ReadAck:
      ps := P_Shared;
    case RecallReq:
      -- Only case: The proc is auto downgrading itself, while home is recalling it because Rdx.
      -- Maybe another case: The proc is downgrading itself, the home rdack it, but the home is recalling it and arrives first. A readack on the way.
      -- case 2 impossible, the proc will receive the invreq instead of the recallreq.
      undefine pv;
      ps := P_Invalid;
    case DowngradeReq:
      -- TODO: Maybe a better way to handle this?
      -- Only case: The proc is auto downgrading itself, while home is also downgrading it.
      ps := P_Shared;
    case InvReq:
    	msg_processed := false; -- stall message in InBox
    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_S2MPending: 
    switch msg.mtype
    case ReadExAck:
      pv := msg.val;
      ps := P_Modified;
    case InvReq:
      -- case 1: this shared proc ask to upgrade while home is recalling due to another ReadExReq.
      --         proc need to respond with a writeback, otherwise deadlock.
      -- case 2: this shared proc ask to upgrade and home granted it, but home is recalling due to another ReadExReq.
      --         the recalling message arrive first.
      --         the proc need to stall the message.
      -- case 2 might be impossible, because the home node is in HT_S2MPending state.
      -- case 2 now possible, because when this proc is the only sharer, the home node will not enter HT_S2MPending state.
      ps := PT_I2MPending;
      Send(WBReq, msg.src, p, VC1, pv);
      Undefine pv;
    case RecallReq:
      msg_processed := false; -- stall message in InBox
    case DowngradeReq:
      msg_processed := false; -- stall message in InBox
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;


  case PT_WritebackPending:    

    switch msg.mtype
    case WBAck:
      ps := P_Invalid;
      undefine pv;
    case RecallReq:				-- treat a recall request as a Writeback acknowledgement
      ps := P_Invalid;
      undefine pv;
    case InvReq:
      ps := P_Invalid;
      undefine pv;
    case DowngradeReq:				-- treat a downgrade request as a Writeback acknowledgement -- TODO: Req or Ack?
      -- Sending wb & Receiving downgrade same time
      ps := P_Invalid;
      undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;
  
  endalias;
  endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)

ruleset n:Proc Do
  alias p:Procs[n] Do

  -- TOASK: What if the downgrade/recall request is delayed? Are we sending the right value?
  -- TOASK: If modified ever going to downgrade itself? NO?
	ruleset v:Value Do
  	rule "store new value"
   	 (p.state = P_Modified)
    	==>
 		   p.val := v;      
 		   LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
  	endrule;
	endruleset;

  rule "read exclusive request"
    (p.state = P_Invalid)
  ==>
    Send(ReadExReq, HomeType, n, VC0, UNDEFINED);
    p.state := PT_I2MPending;
  endrule;

  rule "upgrade request"
    (p.state = P_Shared)
  ==>
    Send(ReadExReq, HomeType, n, VC0, UNDEFINED);
    p.state := PT_S2MPending;
  endrule;

  rule "read request"
    (p.state = P_Invalid)
  ==>
    Send(ReadReq, HomeType, n, VC0, UNDEFINED);
    p.state := PT_I2SPending;
  endrule;

  rule "writeback from modified"
  -- TOASK: Is shared ever going to do wb? YES?
     p.state = P_Modified
  ==>
    Send(WBReq, HomeType, n, VC1, p.val); 
    p.state := PT_WritebackPending;
    undefine p.val;
  endrule;

  rule "writeback from shared"
    (p.state = P_Shared)
  ==>
    -- TODONOW: Change back from real value
    Send(WBReq, HomeType, n, VC1, UNDEFINED); 
    p.state := PT_WritebackPending;
    undefine p.val;
  endrule;

  rule "self-downgrade"
    (p.state = P_Modified)
  ==>
    -- TOCHECK: Using VC1
    Send(AutoDowngradeReq, HomeType, n, VC2, p.val);
    p.state := PT_M2SPending;
  endrule;

  endalias;
endruleset;

-- Message delivery rules
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do
    alias box:InBox[n] do

		-- Pick a random message in the network and delivier it
    rule "receive-net"
			(isundefined(box[msg.vc].mtype))
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(msg, n);
			endif;

			if ! msg_processed
			then
				-- The node refused the message, stick it in the InBox to block the VC.
	  		box[msg.vc] := msg;
			endif;
	  
		  MultiSetRemove(midx, chan);
	  
    endrule;
  
    endalias
    endalias;
    endalias;
  endchoose;  

	-- Try to deliver a message from a blocked VC; perhaps the node can handle it now
	ruleset vc:VCType do
    rule "receive-blocked-vc"
			(! isundefined(InBox[n][vc].mtype))
    ==>
      if IsMember(n, Home)
      then
        HomeReceive(InBox[n][vc]);
      else
        ProcReceive(InBox[n][vc], n);
			endif;

			if msg_processed
			then
				-- Message has been handled, forget it
	  		undefine InBox[n][vc];
			endif;
	  
    endrule;
  endruleset;

endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
-- No modification is needed.
startstate

	For v:Value do
  -- home node initialization
  HomeNode.state := H_Invalid;
  undefine HomeNode.owner;
  HomeNode.val := v;
	endfor;
	LastWrite := HomeNode.val;
  
  -- processor initialization
  for i:Proc do
    Procs[i].state := P_Invalid;
    undefine Procs[i].val;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Invalid implies empty owner"
  HomeNode.state = H_Invalid
    ->
      IsUndefined(HomeNode.owner);

invariant "value in memory matches value of last write, when invalid"
     HomeNode.state = H_Invalid 
    ->
			HomeNode.val = LastWrite;

invariant "values in valid state match last write"
  Forall n : Proc Do	
     (Procs[n].state = P_Shared | 
      Procs[n].state = P_Modified)
    ->
			Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
	end;
	
invariant "value is undefined while invalid"
  Forall n : Proc Do	
     Procs[n].state = P_Invalid
    ->
			IsUndefined(Procs[n].val)
	end;
	

-- Here are some invariants that are helpful for validating shared state.

invariant "modified implies empty sharers list"
  HomeNode.state = H_Modified
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = H_Invalid
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do	
     HomeNode.state = H_Shared | HomeNode.state = H_Invalid
    ->
			HomeNode.val = LastWrite
	end;

invariant "values in shared state match memory"
  Forall n : Proc Do	
     HomeNode.state = H_Shared & Procs[n].state = P_Shared
    ->
			HomeNode.val = Procs[n].val
	end;

invariant "Shared implies undifined owner"
  HomeNode.state = H_Shared
    ->
      IsUndefined(HomeNode.owner);

invariant "Shared implies no modified processors"
  Forall n : Proc Do	
     HomeNode.state = H_Shared
    ->
      Procs[n].state != P_Modified
  end;

invariant "Invalid implies no modified or shared processors"
  Forall n : Proc Do	
     HomeNode.state = H_Invalid
    ->
      Procs[n].state != P_Modified &
      Procs[n].state != P_Shared
  end;

invariant "Modified implies no shared processors"
  Forall n : Proc Do	
     HomeNode.state = H_Modified
    ->
      Procs[n].state != P_Shared
  end;

invariant "Modified implies only one modified processor"
  Forall n1: Proc Do	
      Forall n2: Proc Do
        HomeNode.state = H_Modified
        ->
          (n1 = n2) | 
          (Procs[n1].state != P_Modified | Procs[n2].state != P_Modified)
      end
  end;

invariant "Shared implies at least one sharer"
  HomeNode.state = H_Shared
    ->
      MultiSetCount(i:HomeNode.sharers, true) > 0;
