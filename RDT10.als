module RDT10

open util/ordering[State]

sig Data {}



sig State {
	send : set Data,
	rec : set Data
}

pred State.init[]{
	some d : Data | d in this.send
	no this.rec
}
run init for 1 State, 10 Data
pred sending[s, s' : State] {
	one d:Data | (
		(d in s.send and
		s'.send = s.send - {d}) and
		(s'.rec = s.rec + {d} or
		s'.rec = s.rec)
	)
}
pred Progress[s, s' : State]{
	#s.rec < #s'.rec or s'.end
}
pred Possible {
	first.init
	all s: State - last |
		let s' = s.next |
			sending[s, s'] and Progress[s,s']
}
pred State.end[] {
	no d:Data | d in this.send
}

fact bugfix1{
	all s:State | no d : Data | d in s.send and d in s.rec
}

run Possible for 5 State, 6 Data

assert AlwaysSend{
	first.init
	all s: State - last |
		let s' = s.next |
			sending[s, s'] and Progress[s,s']
	all d : Data | d in first.send and d in last.rec 	and
			not (d in first.rec and d in last.send)
}

check AlwaysSend for 2 State, 2 Data




