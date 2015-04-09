
module Part1_2a

sig State { }

one sig a extends State { }
one sig b extends State { }
one sig c extends State { }
one sig d extends State { }

one sig M {
	A: set State,
	R:   A -> A,
} { // Basic facts
	
	// All states, A = {a, b, c, d} 
	a in A
	b in A
	c in A
	d in A

	// Now we define the relation between states
	// R = {(b,c),(b,b),(b,a)}

	// Transitions from 'a' state
	a not in R[a]
	b not in R[a]
	c not in R[a]

	// transitions from ''b' state
	a in R[b]  // (b,a)
	b in R[b]  // (b,b)
	c in R[b]  // (b,c)

	// transitions from 'c' state
	a not in R[c]
	b not in R[c]
	c not in R[c]
}

// Dummy predicate to display the model details
pred show { }

// φ = ∀x ∀y ∃z (R(x, y) → R(y, z))
assert φ { all m:M | all x,y:m.A | some z:m.A | y in x.(m.R) => z in y.(m.R) }

run show
check φ
