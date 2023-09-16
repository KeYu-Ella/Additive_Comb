import order.partition.finpartition
import combinatorics.simple_graph.degree_sum
import combinatorics.simple_graph.connectivity
import probability.probability_mass_function.uniform

open finset fintype simple_graph
open_locale big_operators classical

variables {V W: Type}

def bipartite_graph (G : simple_graph V) : Prop := 
  ∃ (P : finpartition G), (P.parts).card = 2

def is_bipartite (H : simple_graph (V ⊕ W)) : Prop := ∀ x y : V ⊕ W, H.adj x y → 
  (x.is_left ∧ y.is_right) ∨ (x.is_right ∧ y.is_left) 

lemma dart_bi (H : simple_graph (V ⊕ W)) (hH : is_bipartite H) (d : H.dart) : d.fst.is_left ↔ d.snd.is_right :=
begin
  split,
  { intro h,
    specialize hH d.fst d.snd d.is_adj,
    cases hH,
    exact hH.2,
    exfalso,
    cases hH with h1 h2,
    exact sum.not_is_left.mpr h1 h, },
  { intro h,
    specialize hH d.fst d.snd d.is_adj,
    cases hH,
    exact hH.1,
    exfalso,
    cases hH with h1 h2,
    exact sum.not_is_right.mpr h2 h, },   
end

lemma dart_bi' (H : simple_graph (V ⊕ W)) (hH : is_bipartite H) (d : H.dart) : d.fst.is_left ↔ d.symm.fst.is_right:=
begin
  rw dart_bi H hH d,
  simp,
end

lemma dart_bipartite (H : simple_graph (V ⊕ W)) (hH: is_bipartite H) (d : H.dart): 
  ∃ v : V, d.fst = sum.inl v ↔ ∃ w : W, d.symm.fst= sum.inr w := 
begin
  have h := dart_bi H hH,
  simp,
  sorry,
end

def empty_bipartite_graph : simple_graph (V ⊕ W) := { adj := λ i j, false }

/-from mathlib-/
def mathlib_complete_bipartite_graph : simple_graph (V ⊕ W) := { adj := λ v w, (v.is_left ∧ w.is_right) ∨ (v.is_right ∧ w.is_left),
  symm := begin
    intros v w,
    cases v; cases w; simp,
  end,
  loopless := begin
    intro v,
    cases v; simp,
  end }

--------------------------------
variables (H : simple_graph (V ⊕ W)) (hH : is_bipartite H) [fintype V] [fintype W] (v : V ⊕ W) [fintype (H.neighbor_set v)][fintype H.edge_set]

def density_bipartite_graph (h : is_bipartite H) : ℚ 
  := H.edge_finset.card/(fintype.card V * fintype.card W)
notation `Δ` := density_bipartite_graph

def normalised_left_deg_bipartite (h : is_bipartite H) (v : V ⊕ W) (hv : v.is_left) 
  [fintype (H.neighbor_set v)] : ℚ := H.degree v / fintype.card W

def normalised_right_deg_bipartite (h : is_bipartite H) (v : V ⊕ W) (hv : v.is_right) 
  [fintype (H.neighbor_set v)] : ℚ := H.degree v / fintype.card V

noncomputable def codegree (h : is_bipartite H) (v v' : V ⊕ W) (hv : (v.is_left ∧ v'.is_left)∨ (v.is_right ∧ v'.is_right))
  [fintype (H.neighbor_set v)] [fintype (H.neighbor_set v')] : ℕ
  := ((H.neighbor_finset v) ∩ (H.neighbor_finset v')).card

-- noncomputable def codegree_right (h : is_bipartite H) (v v': V ⊕ W) (hv : v.is_right) (hv': v'.is_right)
--   [fintype (H.neighbor_set v)] [fintype (H.neighbor_set v')] : ℕ
--   := ((H.neighbor_finset v) ∩  (H.neighbor_finset v')).card

noncomputable def normalised_codegree_left (h : is_bipartite H) (v v': V ⊕ W) (hv : v.is_left ∧ v'.is_left)
  [fintype (H.neighbor_set v)] [fintype (H.neighbor_set v')] : ℚ
  := ((H.neighbor_finset v) ∩ (H.neighbor_finset v')).card / fintype.card W

noncomputable def normalised_codegree_right (h : is_bipartite H) (v v': V ⊕ W) (hv : v.is_right ∧ v'.is_right)
  [fintype (H.neighbor_set v)] [fintype (H.neighbor_set v')] : ℚ 
  := ((H.neighbor_finset v) ∩ (H.neighbor_finset v')).card / fintype.card V

noncomputable def deg : V ⊕ W → ℕ := λ (v : V ⊕ W), H.degree v 

noncomputable def average_degree_inl : V → ℚ := λ (v : V), (H.degree (sum.inl v)) / fintype.card W

noncomputable def average_degree_inr : W → ℚ := λ (w : W), (H.degree (sum.inr w)) / fintype.card V

lemma dart_fst_fiber_card_eq_degree_bipartite_left [decidable_eq V] (v : V) 
  (H : simple_graph (V ⊕ W)) (hH: is_bipartite H):
  (univ.filter (λ d : H.dart, d.fst = (sum.inl v))).card = H.degree (sum.inl v) :=
begin
  sorry,
end

lemma dart_fst_fiber_card_eq_degree_bipartite_right [decidable_eq W] (w : W) 
  (H : simple_graph (V ⊕ W)) (hH: is_bipartite H):
  (univ.filter (λ d : H.dart, d.fst = (sum.inr w))).card = H.degree (sum.inr w) :=
begin
  sorry,
end

lemma density_subset [decidable_eq V] (H : simple_graph (V ⊕ W)) (hH : is_bipartite H) (v : V) : 
  H.edge_finset.card = ∑ (v : V), H.degree (sum.inl v):= 
begin
  have := simple_graph.sum_degrees_eq_twice_card_edges H,
  -- have hfiberwise : dart_fst_fiber_card_eq_degree_bipartite v H hH,
  sorry,
end

noncomputable def den (H : simple_graph (V ⊕ W)): ℚ := H.edge_finset.card/(fintype.card V * fintype.card W)

lemma density_subset' [decidable_eq V] (H : simple_graph (V ⊕ W)) (hH : is_bipartite H) (v : V) : 
  den H = ∑ (v : V), H.degree (sum.inl v)/ (fintype.card V * fintype.card W):= 
begin
  unfold den, 
  sorry,
end
-------------------Paths of length 3----------------------
noncomputable def finset_path_length (v w : (V ⊕ W)) (n : ℕ) : 
  finset (H.walk v w) := ((H.finset_walk_length n v w).filter walk.is_path)
-- {p : H.walk v w| p.is_path ∧ p.length = n}

lemma path_three (H : simple_graph (V ⊕ W)) (hH : is_bipartite H) : 
  ∃ (V' : finset V), ∃ (W' : finset W), 
  (V'.card: ℚ) ≥ (Δ H hH) * (fintype.card V) / (8 * 2^(1/2)) 
  ∧ (W'.card: ℚ) ≥ (Δ H hH) * (fintype.card W) / 4 := sorry 
