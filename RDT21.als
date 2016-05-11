module RDT21
open util/ordering[State]

abstract sig SequenceNumber {}
sig One extends SequenceNumber{}
sig Zero extends SequenceNumber{}
sig CheckSum{}
sig Data {
	chk: one CheckSum,
	sequenceNumber: one SequenceNumber
}

one sig CheckCalc{
	map: disjoint Data -> one CheckSum
}

sig State {
	packetStatus : set Data,
	send : set Data,
	rec : set Data
}

pred State.init[]{
	some d : Data | d in this.send
	no this.rec
	all d : this.send | d.chk = calc[d]
}

run init for 1 State, exactly 10 Data, 15 CheckSum
pred sending[s, s' : State] {
	 one d,d':Data | (
		d in s.send and
		ErrorCheck[d'] implies ((s'.rec = s.rec + {d'}) and ACK[s,s',d]) and
		not ErrorCheck[d]' implies (NAK[s,s',d])
	)
}

fun calc[d:Data]: CheckSum{
	 CheckCalc.map[d]
}

fact {
	all d : Data | d in CheckCalc.map.CheckSum
}

pred ErrorCheck[d:Data]{
	d.chk = calc[d]
}

pred ACK[s,s':State, d:Data]{
	s'.send = s.send - {d}
}
pred NAK[s,s':State, d:Data]{
	//idk
}

pred Progress[s, s' : State]{
	#s.rec < #s'.rec or s'.end
}
pred Possible {
	first.init
	all s: State - last |
		let s' = s.next |
			sending[s, s']  
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
			sending[s, s'] 
	all d : Data | d in first.send and d in last.rec 	and
			not (d in first.rec and d in last.send)
}

check AlwaysSend for 2 State, 2 Data, 2 CheckSum




