
/***************************************************************************************
  Part I.a: In this we create the signature for the statemachine, states and properties
              and define basic facts that are applicable on it.
****************************************************************************************/

module KripkeModel

// Represents a property (atom) contained within each state
sig Prop { }

// Represents a state with mapping to its properties
sig State {
	prop: set Prop
}

// The model itself
sig StateMachine {
	// set of all states used in the model
	states: set State,

	// set of initial states
	init: set states,
	
	// state transitions
	next: states -> states,

	// set of final states
	final: set states
} {
	// basic facts about the model

	// We have non-empty set of initial states (as mentioned in text)
	some init

	// We have non-empty set of distinct final states (as given in case study)
	some final
	
	// Initial and final states are distinct
	no init & final

	// For all final states, if there'a next state, then its that state itself
	all f: final | f.next in { f }

	// Some non-final state need to transition to final state
	some s: (states - final) | some s.next and s.next in final

	// Initial state transitions need to be a non-initial state
	no init.next & init
}

pred show { }

run show for 3 State, 3 Prop, 1 StateMachine

/**************************************************************************************
   Part I.b: In this we define the 'Reaches' predicate that can test the reachability of
               a set of states from the initial states of a given model
***************************************************************************************/

// Predicate to check whether all states are reachable from initial state
pred Reaches [m: StateMachine, s: set State] { s in (m.init).*(m.next) }

// Run Reaches for 3 states, 3 properties and 1 state machine
run Reaches for exactly 5 State, exactly 3 Prop, exactly 1 StateMachine


/**************************************************************************************
  Part I.c: Implement DeadlockFree, Deterministic, Reachability and Liveness predicates
***************************************************************************************/

// i. Predicate to ensure that only final states can deadlock
pred DeadlockFree [m: StateMachine] { all s: m.states | (s.(m.next) = s) => (s in m.final) }

run DeadlockFree for exactly 5 State, exactly 3 Prop, exactly 1 StateMachine


// ii. Predicate to check that for every state reachable from init, it can have either
//    zero or one next states
pred Deterministic [m: StateMachine] { all s: (m.init).*(m.next) | lone s.(m.next) }

run Deterministic for exactly 5 State, exactly 3 Prop, exactly 1 StateMachine


// iii. Predicate to check that we can reach a state that has the given property set to true
pred Reachability [m: StateMachine, p: Prop] { some s: (m.init).*(m.next) | p in s.prop }

run Reachability for exactly 5 State, exactly 3 Prop, exactly 1 StateMachine


// iv. Predicate to check that starting from any reachable state, we can reach another state
//     that has given property
pred Liveness [m: StateMachine, p: Prop] { all r: (m.init).*(m.next) | some s: r.*(m.next) | p in s.prop }

run Liveness for exactly 5 State, exactly 3 Prop, exactly 1 StateMachine


/**************************************************************************************
  Part I.d: Implement Implies assertion
***************************************************************************************/
assert Implies { all m: StateMachine, p: Prop | Liveness[m, p] => Reachability[m, p] }

check Implies for exactly 15 State, exactly 5 Prop, exactly 1 StateMachine

/**************************************************************************************
  Part I.e: Implement Converse assertion which is the inverse of Part I.d
***************************************************************************************/
assert Converse { all m: StateMachine, p: Prop | Reachability[m, p] => Liveness[m, p] }

// As expected the Converse is not true because Reachability requires just a single path
// from init to reach to the state that contains p. But that does not mean for every other
// state in the model, there exists a path from that state to the state having property p.
check Converse for 3


/**************************************************************************************
  Part I.d: Predicate to check model for Figure 2.15 in the text book for the following
              properties:
                a. no non-final state deadlocks; which means that all non-final state
                   should have a next state
                b. two states with same properties are identical
***************************************************************************************/
pred Figure215 [m: StateMachine] {
	all s: m.states - m.final | some s.(m.next)
	all x,y: m.states | (x.prop = y.prop) => (x = y)
}

run Figure215 for 2 Prop, 3 State, 1 StateMachine

