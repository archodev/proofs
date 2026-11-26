import KMO

-- Exact statements and the definitions that identify the mathematical problem.
#check @KMO.odd_edge_coloring
#check @KMO.conjecture_six
#print KMO.ConjectureSix
#print KMO.OddThree
#print KMO.ThreeConnected
#print KMO.ConnectedOn
#print KMO.Reach
#print KMO.Graph
#print KMO.Graph.degree
#print KMO.Graph.good
#print KMO.Graph.oddAt
#print KMO.card
#print KMO.total
#print KMO.Edge
#print KMO.Edge.ends
#print KMO.incidentDegree

-- The two coloring constructions and the parity argument.
#check @KMO.star_coloring
#print KMO.StarAt
#check @KMO.mixed_cycle_coloring
#print KMO.MixedCycle
#check @KMO.switch_odd_support
#check @KMO.odd_support_coloring

-- The separation results, their application, and the previously known cases.
#print KMO.TuttePeripheral
#print KMO.CycleOn
#print KMO.Three
#print KMO.Two
#check @KMO.tutte_peripheral
#print KMO.Piece.minimal
#print KMO.Piece.valid
#print KMO.Shore
#check @KMO.Piece.exists_minimal
#check @KMO.Piece.inner_conn
#check @KMO.Piece.torso_three
#check @KMO.Piece.lift_cycle
#check @KMO.Piece.lift_complement
#check @KMO.Leaf.has_star
#check @KMO.unique_even_of_tutte
#check @KMO.universal_coloring
#check @KMO.multiple_even
#check @KMO.four_connected_coloring

-- Transitive axioms used by the exported theorems and the main ingredients.
#print axioms KMO.odd_edge_coloring
#print axioms KMO.conjecture_six
#print axioms KMO.star_coloring
#print axioms KMO.mixed_cycle_coloring
#print axioms KMO.switch_odd_support
#print axioms KMO.odd_support_coloring
#print axioms KMO.tutte_peripheral
#print axioms KMO.Piece.exists_minimal
#print axioms KMO.Piece.torso_three
#print axioms KMO.Piece.lift_cycle
#print axioms KMO.Piece.lift_complement
#print axioms KMO.Leaf.has_star
#print axioms KMO.universal_coloring
#print axioms KMO.multiple_even
#print axioms KMO.four_connected_coloring

-- Make the audit fail if the dependency list of the main theorem changes.
/-- info: 'KMO.odd_edge_coloring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KMO.odd_edge_coloring
