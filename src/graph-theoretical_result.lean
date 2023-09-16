import combinatorics.simple_graph.degree_sum
import combinatorics.simple_graph.connectivity

open finset fintype simple_graph
open_locale big_operators classical

variables {V W : Type}

def is_bipartite (H : simple_graph (V ⊕ W)) : Prop := ∀ x y : V ⊕ W, H.adj x y → 
  (x.is_left ∧ y.is_right) ∨ (x.is_right ∧ y.is_left)

variables (H : simple_graph (V ⊕ W)) (hH : is_bipartite H) [fintype V] [fintype W] (v : V ⊕ W) [fintype (H.neighbor_set v)][fintype H.edge_set]

def density_bipartite_graph (h : is_bipartite H) : ℚ 
  := H.edge_finset.card/(fintype.card V * fintype.card W)

notation `Δ` := density_bipartite_graph

noncomputable def finset_path_length (v w : (V ⊕ W)) (n : ℕ) : 
  finset (H.walk v w) := ((H.finset_walk_length n v w).filter walk.is_path)
-- {p : H.walk v w| p.is_path ∧ p.length = n}

lemma path_three (H : simple_graph (V ⊕ W)) (hH : is_bipartite H) : 
  ∃ (V' : finset V), ∃ (W' : finset W), 
  (V'.card : ℚ) ≥ (Δ H hH) * (fintype.card V) / (8 * 2 ^ (1 / 2)) 
  ∧ (W'.card : ℚ) ≥ (Δ H hH) * (fintype.card W) / 4 
  ∧ (∀ (x : V'), ∀ (y : W'), ((finset_path_length H (sum.inl (x : V)) (sum.inr (y : W)) 3).card : ℚ) = 
  ((Δ H hH) * 2^(-13) * (fintype.card V) * (fintype.card W))) := sorry   
