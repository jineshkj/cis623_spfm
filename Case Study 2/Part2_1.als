
/*
 * Model to check φ1 ^ φ2 does not imply φ3

   φ1 = ∀xP(x,x)
   φ2 = ∀x∀y(P(x,y) → P(y,x))
   φ3 = ∀x∀y∀z((P(x,y)∧P(y,z)→P(x,z)))

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

	// edges a->a, a->b but not a->c
	a in edges[a]
	b in edges[a]
	c not in edges[a]

	// edges b->a, b->c, b->b
	a in edges[b]
	b in edges[b]
	c in edges[b]

	// edges c->b, c->c but not c->a
	a not in edges[c]
	b in edges[c]
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
