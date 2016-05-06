module RDT20

open util/ordering[State]
sig CheckSum{}
sig Data {
	chk: one CheckSum
}

one sig CheckCalc{
	map: disjoint Data -> one CheckSum
}

sig State {
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
		//(s'.rec = s.rec + {d'}) and
		ErrorCheck[d'] implies ((s'.rec = s.rec + {d'}) and ACK[s,s',d])
	)
}

fun calc[d:Data]: CheckSum{
	 CheckCalc.map[d]
}

fact {
	all d : Data | d in CheckCalc.map.CheckSum
	//all disjoint d,d': CheckCalc.map.CheckSum | not(d=d')
}

pred ErrorCheck[d:Data]{
	d.chk = calc[d]
}

pred ACK[s,s':State, d:Data]{
	s'.send = s.send - {d}
}

pred Progress[s, s' : State]{
	#s.rec < #s'.rec or s'.end
}
pred Possible {
	first.init
	all s: State - last |
		let s' = s.next |
			sending[s, s'] and last.end// and Progress[s,s']
}
pred State.end[] {
	no d:Data | d in this.send
}
//run end for 1 State, 5 Data, 5 CheckSum
fact bugfix1{
//	all s:State | no d : Data | d in s.send and d in s.rec
}

run Possible for 5 State, exactly 5 Data, 5 CheckSum

assert AlwaysSend{
	first.init
	all s: State - last |
		let s' = s.next |
			sending[s, s'] and Progress[s,s']
	all d : Data | d in first.send and d in last.rec 	and
			not (d in first.rec and d in last.send)
}

check AlwaysSend for 2 State, 2 Data, 2 CheckSum




