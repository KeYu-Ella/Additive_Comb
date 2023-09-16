import combinatorics.additive.energy
import combinatorics.simple_graph.basic
import combinatorics.double_counting
import data.finset.pointwise
import data.sym.card
import data.finset.card
import data.nat.parity
import data.rat.sqrt
import data.complex.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.basic
import data.nat.sqrt

open_locale big_operators
open finset nat
open_locale pointwise

variables {V : Type} [decidable_eq V] (H : simple_graph V)
variables {G : Type} [decidable_eq G] [has_add G]
variables {α : Type} [decidable_eq α] [add_comm_group α] [has_add α]

def single_additive_energy (A : finset G) : ℚ := (finset.additive_energy A A)/ A.card^3

--Take the square first to avoid taking the square root.
-- @Junyan Xu's proof
lemma cauchy_schwarz {α : Type*} [fintype α] (f g : α → ℝ) :
  (∑ x, f x * g x) ^ 2 ≤ (∑ x, f x ^ 2) * (∑ x, g x ^ 2) :=
begin
  change euclidean_space ℝ α at f,
  change euclidean_space ℝ α at g,
  sorry,
  -- have := abs_inner_le_norm ℝ _ _ _ f g,
  -- rw [← abs_norm_eq_norm f, ← abs_norm_eq_norm g, ← abs_mul,
  --   pi_Lp.inner_apply, is_R_or_C.abs_to_real] at this,
  -- convert sq_le_sq this using 1,
  -- simp_rw [mul_pow, ← real_inner_self_eq_norm_sq],
  -- simp only [sq, pi_Lp.inner_apply, is_R_or_C.inner_apply, is_R_or_C.conj_to_real],
end



lemma cauchy_schwarz_nat {α : Type*} [fintype α] (f g : α → ℕ) :
  (∑ x, f x * g x) ^ 2 ≤ (∑ x, f x ^ 2) * (∑ x, g x ^ 2) :=
by exact_mod_cast cauchy_schwarz (λ x, f x) (λ x, g x)

lemma cauchy_schwarz_sqrt {G : Type} [fintype G] (f : G → ℕ) :
  (∑ x, f x) ≤ sqrt (fintype.card G) * sqrt (∑ x, f x ^ 2) :=
begin
  have h: sqrt ((∑ x, f x) ^ 2) ≤ sqrt ((fintype.card G) * (∑ x, f x ^ 2)) := 
  begin
    apply nat.sqrt_le_sqrt,
  exact cauchy' f,
  end,
  rw nat.sqrt_eq' at h,
  rw sqrt_mul at h,
  exact h,
end

lemma sumset_additive_energy (A : finset G) {c : ℕ} (hc : 0 < c) (hA : (A + A).card ≤ c * A.card) :
  single_additive_energy A ≥ 1/c := 
begin
  -- let g : G × G → G := λ (x : G × G), x.1 + x.2,
  -- let f : G → ℕ := λ (d : G), finset.card (finset.filter (λ ab, g ab = d) (A ×ˢ A)),
  -- have h: ∀ d, d ∈ A + A ↔ f d ≠ 0 := sorry,
  -- let f0 : G →₀ ℕ := finsupp.mk (A + A) f h,    
  -- have f0card : (finsupp.sum f0 (λ a m, m)) = (A.card)^2 := sorry,
  let y := A + A,
  let f' : A + A → ℕ := λ (d : A + A), finset.card (finset.filter (λ (ab : G × G), ab.1 + ab.2 = d) (A ×ˢ A)),
  have fsum : (∑ x, f' x) = (A.card) ^ 2 := sorry,
  have fsum_square : (∑ x, (f' x) ^ 2) = (finset.additive_energy A A) := sorry,
  unfold single_additive_energy,
  have := cauchy_schwarz_sqrt' f',
  rw fsum at this,
  rw fsum_square at this,
  have hc_ineq : fintype.card ↥(A + A) ^ (1 / 2) * (A.additive_energy A) ^ (1 / 2) ≤ (c * A.card)^(1/2) * (A.additive_energy A) ^(1/2) := sorry,
  /-rearranging-/
  have hc'_ineq : A.card ^ 2 ≤ (c * A.card) ^ (1 / 2) * (A.additive_energy A) ^ (1 / 2) := le_trans this hc_ineq,
  sorry,
end