import data.finset.pointwise
import combinatorics.additive.energy
import combinatorics.simple_graph.basic

open finset nat
open_locale big_operators
open_locale pointwise

variables {G : Type} [decidable_eq G] [add_comm_group G] (A : finset G)

example : has_add G := infer_instance

def single_additive_energy (A : finset G) : ℕ := finset.additive_energy A A

lemma additive_energy_eq_difference (A : finset G) : 
  single_additive_energy A = (((A ×ˢ A) ×ˢ A ×ˢ A).filter $ λ x : (G × G) × G × G, x.1.1 - x.2.1 = x.1.2 - x.2.2).card := sorry

def difference_map : A - A → ℕ := 
  λ (d : A - A), finset.card (finset.filter (λ (ab : G × G), ab.1 - ab.2 = d) (A ×ˢ A))

def sum_map : G → ℕ := 
  λ (x : G), finset.card (finset.filter (λ (ab : G × G), ab.1 + ab.2 = x) (A ×ˢ A))
notation `f'` := sum_map

def d_map : G → ℕ :=  λ (d : G), finset.card (finset.filter (λ (ab : G × G), ab.1 - ab.2 = d) (A ×ˢ A))

notation `f` := difference_map

lemma f_sum (A : finset G) : (∑ (x : A + A), f' A x) = (A.card) ^ 2 := sorry

lemma f_sum_square (A : finset G) : 
  (∑ (x : A + A), (f' A x) ^ 2) = single_additive_energy A := sorry

lemma fsum_diff (A : finset G) : (∑ (x : A - A), f A x) = (A.card) ^ 2 :=
begin
  unfold difference_map,
  sorry,
end

lemma fsum_square_diff (A : finset G) : 
  (∑ (x : A - A), (f A x) ^ 2) = single_additive_energy A := sorry

def pop_diff (θ : ℚ) (d : G) : Prop := ((d_map A d) : ℚ) ≥ θ * (A.card : ℚ)
def pop_sum (θ : ℚ) (s : G) : Prop := ((f' A s) : ℚ) ≥ θ * (A.card : ℚ)

def adj' (c : ℚ): A ⊕ A → A ⊕ A → Prop
| (sum.inl v) (sum.inl v') := false
| (sum.inl v) (sum.inr v') := pop_diff A (c / 2) (v - v') 
| (sum.inr v) (sum.inl v') := pop_diff A (c / 2) (v' - v) 
| (sum.inr v) (sum.inr v') := false

lemma popular_sum_lower_bound (A : finset G) (c : ℚ) 
  (h : ((single_additive_energy A) : ℚ) ≥ c * ((A.card : ℚ) ^ 3)) : 
  (finset.card (finset.filter (λ (s : G), ((f' A s) : ℚ) ≥ 
  (((c / 2) : ℚ) * (A.card : ℚ))) (A + A)) : ℚ) ≥ c * A.card / 2 := 
begin
  sorry,
end

lemma popular_diff (A : finset G) (c : ℚ) 
  (h : ((single_additive_energy A) : ℚ) ≥ c * ((A.card : ℚ) ^ 3)) : 
  finset.card (finset.filter (λ (d : G), ((d_map A d) : ℚ) ≥ 
  (((c/2) : ℚ) * (A.card : ℚ))) (A - A)) = 0 := 
begin
  sorry,
end

--Create a bipartite graph using relationship of popular differences. 
def bipartite_popular (c : ℚ) : simple_graph (A ⊕ A) := 
  { adj := adj' A c,
    symm := begin
    intros v w,
    cases v; cases w; unfold adj'; simp
    end,
  loopless := begin
    intro v,
    cases v; unfold adj'; simp, end }

  theorem BSG (A : finset G) (c : ℚ) (h : (single_additive_energy A : ℚ) ≥ c * (A.card)^3):
    ∃ A' ⊆ A, ((A'.card : ℚ) ≥ c ^ 2 * A.card / 16) ∧ 
    (((A' + A').card : ℚ) ≤ 2 ^ (68) * A'.card / (c ^ (36))) := 
  begin
    sorry,
  end