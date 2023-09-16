import combinatorics.double_counting
import data.finset.pointwise
import data.sym.card
import data.rat.sqrt
import data.complex.basic

open finset 
open_locale pointwise

variables {G H : Type} [add_comm_group G] [decidable_eq G] {A B C : finset G}

def doubling_constant (A : finset G) : ℚ := (A + A).card / A.card
def doubling_constant_two_sets (A : finset G) (B : finset G) : ℚ := (A + B).card / rat.sqrt (A.card * B.card)
lemma doubling_constant_two_identitcal_sets (A : finset G) : doubling_constant A = doubling_constant_two_sets A A :=
begin
  unfold doubling_constant,
  unfold doubling_constant_two_sets,
  rw rat.sqrt_eq,
  simp,
end

def difference_constant (A : finset G) : ℚ := (A - A).card / A.card

notation `σ` := doubling_constant
notation `δ` := difference_constant

def g : sym2 G → G := sym2.lift ⟨(+), add_comm⟩

lemma sym2.add_set (A : finset G) : A + A = image g A.sym2 :=
begin
  ext, --Extend the statement elementwisely,
  split,
  { rw finset.mem_add, 
    rintro ⟨p, q, hp, hq, rfl⟩,
    rw finset.mem_image,
    use ⟦(p,q)⟧,
    split,
    { rw finset.mk_mem_sym2_iff,
      exact ⟨hp, hq⟩, },
    { refl}, },
  { rw [finset.mem_add, finset.mem_image],
    rintro ⟨p, hp, rfl⟩,
    revert hp,
    apply quotient.induction_on p,
    clear p,
    rintro ⟨a, b⟩ h,
    rw finset.mk_mem_sym2_iff at h,
    use [a, b],
    refine ⟨h.1, h.2, _⟩,
    refl, },
end

def sidon_set (A: finset G) : Prop := σ A = (A.card + 1) / 2

lemma doubling_constant_upper_bound (A : finset G) : σ A ≤ (A.card + 1) / 2:=
begin
  rw doubling_constant,
  sorry,
end

lemma card_leq_card_add (A : finset G) (ha : A.nonempty) : A.card ≤ (A + A).card :=
begin
  have := sym2.add_set A, 
  rw this,
  sorry,
end

lemma doubling_constant_lower_bound (A : finset G) (ha : A.nonempty) : 1 ≤ σ A:=
begin
  rw doubling_constant,
  have h : 0 < A.card := card_pos.mpr ha,
  rw one_le_div,
  exact nat.cast_le.mpr (card_leq_card_add A ha),
  exact nat.cast_pos.mpr h,
end

lemma difference_constant_upper_bound (A : finset G): δ A ≤ (A.card - 1) / 2 + 1 / A.card:=
begin
  sorry,
end

lemma difference_constant_lower_bound (A : finset G): δ A ≥ 1 :=
begin
  sorry,
end


def golomb_ruler (A: finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, (a = c ∧ b = d) ∨ (a = d ∧ b = c) ↔ a - b = c - d

lemma lift_mk (f : {f : G → G → H // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁}) (a₁ a₂ : G) :
  sym2.lift f ⟦(a₁, a₂)⟧ = (f : G → G → H) a₁ a₂ := rfl

lemma nat_2div_mul_self_add_mul (x : ℕ) : 2 ∣ x * (x + 1):=
begin
  have := nat.even_or_odd,-- A natural number is either even or odd
  specialize this x,
  cases this, -- Consider the cases when x is even or odd
  { rw even_iff_two_dvd at this,-- When x is even, 2 | x
    exact dvd_mul_of_dvd_left this (x + 1),-- then 2 ∣ x * (x + 1)
  },
  { have hx : even (x + 1) := odd.add_odd this odd_one, 
    --When x is odd, x + 1 is even
    rw even_iff_two_dvd at hx,
    exact dvd_mul_of_dvd_right hx x,}
end

example (A : finset G) : nonempty A ↔ A.nonempty := nonempty_coe_sort

lemma sidon_set_equiv_right (A : finset G) (ha : nonempty A) : 
  (∀ a ∈ (A ×ˢ A), ∀ b ∈ A ×ˢ A, ⟦(a.1, a.2)⟧ = ⟦(b.1, b.2)⟧ ↔ a.1 + a.2 = b.1 + b.2)
  → sidon_set A :=
begin
  rw [sidon_set, doubling_constant, div_eq_iff],
  --After rewriting, it suffices to prove |A+A|=(|A|+1)*|A|/2, and |A| ≠ 0
  { intro p,
    have h' : (finset.image g A.sym2).card = A.card * (A.card + 1) / 2,
    { rw ← card_sym2 A,
      rw finset.card_image_of_inj_on _,
      rw set.inj_on,
      rintros p1 hp1 p2,
      revert hp1,
      apply sym2.induction_on₂ p1 p2,
      intros a1 a2 b1 b2 ha hb hg,
      simp at ha hb,
      let a := (a1, a2),
      let b := (b1, b2),
      rw p a _ b _,
      change sym2.lift _ _ = sym2.lift _ _ at hg,
      rw [sym2.lift_mk, sym2.lift_mk] at hg,
      simp at hg,
      exact hg,
      exact mem_product.mpr ha,
      exact mem_product.mpr hb, },
    rw [sym2.add_set, h', rat.coe_nat_div],
    { simp,
      ring, },
    apply nat_2div_mul_self_add_mul,
    },
  { norm_cast,
    rw [nonempty_coe_sort, ← finset.card_pos] at ha,
    exact ha.ne'},
end
--not injective 
lemma card_less {X Y : Type} [decidable_eq Y] (f : X → Y) (s : finset X) (a b : X) (ha : a ∈ s) 
  (hb : b ∈ s) (h : a ≠ b) (h1 : f a = f b) : (finset.image f s).card < s.card :=
begin
  -- apply set.card_lt_card,
  sorry,
end
  
lemma card_sym2_rat (s : finset G) : (s.sym2.card : ℚ) = s.card * (s.card + 1) / 2 := sorry

lemma card_change (A : finset G) : (((A ×ˢ A).image quotient.mk : finset (sym2 G)).card : ℚ) =  
  (A.card + 1) / 2 * A.card := 
begin
  have hp : ((A.card : ℚ) + 1) / 2 * A.card = A.card * (A.card + 1)/ 2 := sorry,
  rw hp,
  rw ← card_sym2_rat A,
  rw finset.card_image_of_inj_on _,
  simp,
  sorry,
  rw set.inj_on,
  rintros p1 hp1 p2,
  revert hp1,
  sorry,
end

lemma sym2_lift_sum_eq (A : finset G) (a b : G × G) (hain : a ∈ A ×ˢ A) (hbin : b ∈ A ×ˢ A) 
  (h : a.fst + a.snd = b.fst + b.snd) : g ⟦a⟧ = g ⟦b⟧ := by tauto

lemma sidon_set_equiv_left  (A : finset G) (ha : nonempty A) :
  sidon_set A →
  ∀ a ∈ (A ×ˢ A), ∀ b ∈ A ×ˢ A, ⟦(a.1, a.2)⟧ = ⟦(b.1, b.2)⟧ ↔ a.1 + a.2 = b.1 + b.2 :=
begin
  rw sidon_set,
  rw doubling_constant,
  intros p a hain b hbin,
  split,
  { rw sym2.eq_iff,
    intro hyp,
    cases hyp,
    { rw hyp.1,
      simp,
      exact hyp.2, },
    { rw [hyp.1, hyp.2],
      exact add_comm b.snd b.fst,}
  },
  { intro hyp,
    rw div_eq_iff at p,
    { let g : sym2 G → G := sym2.lift ⟨(+), add_comm⟩,
      by_contra h,
      have := card_less g ((A ×ˢ A).image quotient.mk) ⟦a⟧ ⟦b⟧ _ _ _ _,
      suffices: ((A + A).card : ℚ) < ((A.card) + 1) / 2 * (A.card),
      { linarith,},
      {
        rw ← card_change A,
        norm_cast,
        convert this,
        rw sym2.add_set,
        tauto,},
      { exact mem_image_of_mem quotient.mk hain,},
      { exact mem_image_of_mem quotient.mk hbin,},
      { 
        have prod_eq_a : a = (a.fst, a.snd):= prod.ext rfl rfl,
        have prod_eq_b : b = (b.fst, b.snd):= prod.ext rfl rfl,
        rw [prod_eq_a, prod_eq_b],
        exact h,
      },
      { apply sym2_lift_sum_eq A,
        exact hain,
        exact hbin,
        exact hyp,
      }
    },
    { norm_cast,
      rw nonempty_coe_sort at ha,
      rw ← finset.card_pos at ha,
      exact ha.ne'}, 
  },
end