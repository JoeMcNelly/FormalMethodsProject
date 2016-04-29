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

pred Trace {
	first.init
	all s: State - last |
		let s' = s.next |
			sending[s, s'] and Progress[s,s']
}

pred State.end[] {
	no d:Data | d in this.send
	
}

run Trace for 5 State, 4 Data




