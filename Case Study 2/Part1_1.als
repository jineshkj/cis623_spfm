
/*
 * Part 1.1 of CIS 623 Case Study 2
 */
module Part1_1

sig State { }

one sig a extends State { }
one sig b extends State { }
one sig c extends State { }

one sig M {
	A: set State,
	R:   A -> A,

	i : A,
	F: set A
} { // Basic facts
	
	// All states, A = {a, b, c} 
	a in A
	b in A
	c in A
	
	// Now we define the relation between states
	// R = {(a, a), (a, b), (a, c), (b, c), (c, c)}

	// Transitions from 'a' state
	a in R[a]  // (a,a)
	b in R[a]  // (a,b)
	c in R[a]  // (a,c)

	// transitions from ''b' state
	a not in R[b] 
	b not in R[b]
	c in R[b]  // (b,c)

	// transitions from 'c' state
	a not in R[c] 
	b not in R[c]
	c in R[c]  // (c,c)

	// Initial state
	i = a
	
	// Final states, F = {b, c}
	a not in F
	b in F
	c in F
}

// Dummy predicate to display the model details
pred show { }

// ∃y R(i, y)
assert initial { all m:M | some y:m.A | y in (m.F).(m.R) }

// ¬F (i)
assert final { all m:M | m.i not in m.F }

// ∀x∀y∀z (R(x, y) ∧ R(x, z) → y = z)
assert deterministic { all m:M | all x,y,z:m.A | (y in x.(m.R) && z in x.(m.R)) => (y = z) }

// ∀x∃y R(x, y)
assert nodeadlock { all m:M | all x:m.A | some y:m.A | y in x.(m.R) }

run show
check initial
check final
check deterministic
check nodeadlock
