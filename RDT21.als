module RDT21
open util/ordering[State]

abstract sig SequenceNumber {}
one sig One extends SequenceNumber{}
one sig Zero extends SequenceNumber{}
sig CheckSum{}
sig Data {
	chk: one CheckSum,
	sequenceNumber: one SequenceNumber
}
sig Ack extends Data{}
sig Nak extends Data{}

one sig CheckCalc{
	map: disjoint Data -> one CheckSum
}

sig State {
	packetStatus : SequenceNumber,
	send : set Data,
	rec : set Data
}

pred State.init[]{
	some d : Data - (Ack + Nak) | d in this.send
	no this.rec
	all d : this.send | d.chk = calc[d]
	//no d : Ack + Nak | d in this.send
}

run init for 1 State, exactly 10 Data, 15 CheckSum
pred sending[s, s', s'' : State] {
	(One in s.packetStatus and Zero in s''.packetStatus) implies (
	 	one d,d':Data | (
			d in s.send and
			(ErrorCheck[d',s,s'] implies ((s'.rec = s.rec + {d'}) and ACK[s,s',d])) and
			(not (ErrorCheck[d',s,s']) implies (NAK[s,s',d]))
		)
	)	
	(Zero in s.packetStatus and One in s''.packetStatus) implies (
	 	one d,d':Data | (
			d in s.send and
			(ErrorCheck[d',s,s'] implies ((s'.rec = s.rec + {d'}) and ACK[s,s',d])) and
			(not (ErrorCheck[d',s,s']) implies (NAK[s,s',d]))
		)
	)	
}
fact bugfix1{
	no d : Data | (d in Ack or d in Nak) and d in State.rec
}

fun calc[d:Data]: CheckSum{
	 CheckCalc.map[d]
}

fact {
	all d : Data | d in CheckCalc.map.CheckSum
}

pred ErrorCheck[d:Data, s,s' :State]{
	d.chk = calc[d] and 
	SequenceCheck[d,s,s']
}
pred SequenceCheck[d:Data, s,s':State] {
	d.sequenceNumber in s.packetStatus and 
	not d.sequenceNumber in s'.packetStatus 
}

pred ACK[s,s':State, d:Data]{ 
	one d':Data | 
	(
		(ErrorCheck[d',s,s'] and d' in Ack ) implies s'.send = s.send - {d}
	)
	
}
pred NAK[s,s':State, d:Data]{
	one d':Data | 
	(
		ErrorCheck[d',s,s'] and d' in Nak
	)
}

pred Progress[s, s' : State]{
	#s.rec < #s'.rec or s'.end
}
pred Possible {
	first.init
	all s: State - last |
		let s' = s.next |
		let s'' = s.prev |
			sending[s, s',s'']  
	last.end
}
pred State.end[] {
	no d:Data | d in this.send and
	all d:first.send | d in this.rec
	no d:this.rec | not d in first.send
}

run Possible for 4 State, exactly 5 Data,  5 CheckSum

assert AlwaysSend{
	first.init
	all s: State - last |
		let s' = s.next |
		let s'' = s.prev |
			sending[s, s',s''] 
	all d : Data | (d in first.send and d in last.rec 	and
			not (d in first.rec and d in last.send))
}

check AlwaysSend for 4 State, 5 Data, 5 CheckSum, exactly 1 Nak
