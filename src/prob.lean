import probability.variance
import probability.integration
import measure_theory.measurable_space
import probability.notation
import measure_theory.function.l2_space
import data.finset.basic
open measure_theory filter finset

noncomputable theory

open_locale big_operators measure_theory probability_theory ennreal nnreal

namespace probability_theory

variables {Ω : Type} {m : measurable_space Ω} {X : Ω → ℝ} {μ : measure Ω} [fintype Ω]

localized "notation (name := probability_theory.variance) `Var[` X `]` :=
  probability_theory.variance X measure_theory.measure_space.volume" in probability_theory

variables [measure_space Ω]

lemma variance_eq [is_probability_measure (ℙ : measure Ω)] (hX : mem_ℒp X 2 ℙ) : Var[X] = 𝔼[X^2] - 𝔼[X]^2 := variance_def' hX

lemma variance_eq' [is_finite_measure (ℙ : measure Ω)] (hX : mem_ℒp X 2 ℙ) : Var[X] = ℙ[(X - (λ ω, ℙ[X]))^2] := 
begin
  rw _root_.measure_theory.mem_ℒp.variance_eq hX,
end

lemma variance_iff [is_probability_measure (ℙ : measure Ω)]
  (hX : mem_ℒp X 2 ℙ): 𝔼[X^2] - 𝔼[X]^2 = ℙ[(X - (λ ω, ℙ[X]))^2] := 
begin
  rw ← variance_eq hX,
  rw ← variance_eq' hX, 
end

lemma expectation_square [is_probability_measure (ℙ : measure Ω)] (hX : mem_ℒp X 2 ℙ) : 
  𝔼[X^2] ≥ 𝔼[X]^2 := 
begin
  have h : Var[X] ≥ 0 := variance_nonneg X ℙ,
  rw variance_eq hX at h,
  exact sub_nonneg.mp h,
end
--Lemma 2.14 
--f : Y → interval, a more restricted X
lemma subset_func (f : Ω → ℝ) (hf : ∀ x : Ω, 0 ≤ f x) (a : ℝ) (h : 𝔼[f] ≥ a) : 
  ((univ.filter (λ x : Ω, f x ≥ a/2)).card : ℝ) ≥ a * ((fintype.card Ω) : ℝ)/2 := sorry

end probability_theory