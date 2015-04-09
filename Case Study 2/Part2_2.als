
/*
 * Model to check φ1 ^ φ3 does not imply φ2

   φ1 = ∀xP(x,x)
   φ3 = ∀x∀y∀z((P(x,y)∧P(y,z)→P(x,z)))
   φ2 = ∀x∀y(P(x,y) → P(y,x))

*/

module AboutGraphs

sig Element { }

one sig a extends Element { }
one sig b extends Element { }
one sig c extends Element { }

one sig Graph {
	nodes : set Element,
	edges : nodes -> nodes
} {
	a in nodes
	b in nodes
	c in nodes

	// edges a->a, a->b, a->c
	a in edges[a]
	b in edges[a]
	c in edges[a]

	// edges b->c, b->b but not b->a
	a not in edges[b]
	b in edges[b]
	c in edges[b]

	// edges c->c but not c->a, c->b
	a not in edges[c]
	b not in edges[c]
	c in edges[c]
}

pred show { }

// φ1 = ∀xP(x,x)
assert φ1 { all g:Graph | all x:g.nodes | x in x.(g.edges) }

// φ2 = ∀x∀y(P(x,y) → P(y,x))
assert φ2 { all g:Graph | all x,y:g.nodes | y in x.(g.edges) => x in y.(g.edges) }

// φ3 = ∀x∀y∀z((P(x,y)∧P(y,z)→P(x,z)))
assert φ3 { all g:Graph | all x,y,z:g.nodes | (x != z && y in x.(g.edges)) && (z in y.(g.edges)) => z in x.(g.edges) }

run show
check φ1
check φ2
check φ3
