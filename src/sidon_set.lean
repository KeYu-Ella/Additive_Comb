import combinatorics.double_counting
import data.finset.pointwise
-- import analysis.special_functions.log.basic
import set_theory.zfc.basic
import data.finset.prod
import data.sym.sym2
import data.finset.sym
import data.finset.basic
import data.sym.card
import data.finset.card
import data.nat.parity
import data.rat.sqrt
import data.complex.basic

open finset nat
open_locale pointwise
universes u v

variables {α β: Type*} [add_comm_group α] [decidable_eq α] {A B C : finset α}
-- [add_comm_group β] [decidable_eq β] {X Y Z : finset β}

def doubling_constant (A: finset α): ℚ := (A + A).card / A.card
def doubling_constant_two_sets (A : finset α) (B : finset α): ℚ := (A + B).card/ rat.sqrt ((A.card)*(B.card))
lemma doubling_constant_two_identitcal_sets (A: finset α) : doubling_constant A = doubling_constant_two_sets A A :=
begin
  unfold doubling_constant,
  unfold doubling_constant_two_sets,
  rw rat.sqrt_eq,
  simp,
end

def difference_constant (A : finset α): ℚ := (A - A).card / A.card

notation `σ` := doubling_constant
notation `δ` := difference_constant

lemma doubling_constant_upper_bound (A : finset α): σ A ≤ (A.card + 1) / 2:=
begin
  rw doubling_constant,
  sorry,
end

lemma doubling_constant_lower_bound (A : finset α) (ha : nonempty A): 1 ≤ σ A:=
begin
  rw doubling_constant,
  have h: 0 < A.card:= by sorry,
  -- have h: 0 < A.card :=by rw ← finset.card_pos ha,
  -- rw ← le_mul_iff_one_le_right h,
  have h₁: A.card ≤ (A + A).card:= by sorry,

  sorry,
end

lemma difference_constant_upper_bound (A : finset α): δ A ≤ (A.card - 1) / 2 + 1 / A.card:=
begin
  sorry,
end

lemma difference_constant_lower_bound (A : finset α): δ A ≥ 1 :=
begin
  sorry,
end

def sidon_set (A: finset α): Prop :=
 σ A = (A.card + 1)/2

def golomb_ruler (A: finset ℕ): Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, (a = c ∧ b = d) ∨ (a = d ∧ b = c) ↔ a - b = c - d

-- def lift : {f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁} ≃ (sym2 α → β) :=
-- { to_fun := λ f, quotient.lift (uncurry ↑f) $ by { rintro _ _ ⟨⟩, exacts [rfl, f.prop _ _] },
--   inv_fun := λ F, ⟨curry (F ∘ quotient.mk), λ a₁ a₂, congr_arg F eq_swap⟩,
--   left_inv := λ f, subtype.ext rfl,
--   right_inv := λ F, funext $ sym2.ind $ by exact λ x y, rfl }

lemma lift_mk (f : {f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁}) (a₁ a₂ : α) :
  sym2.lift f ⟦(a₁, a₂)⟧ = (f : α → α → β) a₁ a₂ := rfl

-- set_option pp.notation false
lemma sym2.add_set (A: finset α): A + A = image (sym2.lift ⟨(+), add_comm⟩) A.sym2:=
begin
  ext,
  split,
  { rw finset.mem_add,
    rintro ⟨p, q, hp, hq, rfl⟩,
    rw finset.mem_image,
    use ⟦(p,q)⟧,
    split,
    { rw finset.mk_mem_sym2_iff,
    exact ⟨hp, hq⟩, },
    { refl},
  },
  { rw finset.mem_add,
    rw finset.mem_image,
    rintro ⟨p, hp, rfl⟩,
    revert hp,
    apply quotient.induction_on p,
    clear p,
    rintro ⟨a, b⟩ h,
    rw finset.mk_mem_sym2_iff at h,
    use [a, b],
    refine ⟨h.1, h.2, _⟩,
    refl,
  },
end

lemma nat_2div_mul_self_add_mul (x : ℕ) : 2 ∣ x * (x + 1):=
begin
  have := nat.even_or_odd',
  unfold has_dvd.dvd,
  sorry,
end

example (A : finset α) : nonempty A ↔ A.nonempty := nonempty_coe_sort

lemma sidon_set_equiv_right (A : finset α) (ha : nonempty A): 
(∀ a ∈ (A ×ˢ A), ∀ b ∈ A ×ˢ A, ⟦(a.1, a.2)⟧ = ⟦(b.1, b.2)⟧ ↔ a.1 + a.2 = b.1 + b.2)
→ sidon_set A:=
begin
  rw [sidon_set, doubling_constant, div_eq_iff],
  { intro p,
    let f': α × α → α := λ (x : α × α), x.1 + x.2,
    let g : sym2 α → α := sym2.lift ⟨(+), add_comm⟩,
    have h': (finset.image g A.sym2).card = A.card * (A.card + 1) / 2,
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

lemma card_less {X Y: Type*} [decidable_eq Y] (f : X → Y) (s : finset X) (a b : X) (ha : a ∈ s) 
(hb : b ∈ s) (h : a ≠ b) (h1 : f a = f b) : (finset.image f s).card < s.card :=
begin
  sorry,
end
  
example (a b c : ℚ) (h : b ≠ 0) : a/b = c ↔ a = c * b := div_eq_iff h
example (a b : ℚ) : a ≠ b ↔ ¬ a = b:= iff.rfl

lemma card_change (A : finset α) : (((A ×ˢ A).image quotient.mk : finset (sym2 α)).card : ℚ) =  
((A.card) + 1) / 2 * (A.card) := sorry

def g : sym2 α → α := sym2.lift ⟨(+), add_comm⟩
lemma sym2_lift_sum_eq (A : finset α) (a b : α × α) (hain : a ∈ A ×ˢ A) (hbin : b ∈ A ×ˢ A) 
(h : a.fst + a.snd = b.fst + b.snd): g⟦a⟧ = g⟦b⟧ := sorry

lemma sidon_set_equiv_left  (A : finset α) (ha : nonempty A):
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
    { let g : sym2 α → α := sym2.lift ⟨(+), add_comm⟩,
      by_contra h,
      have := card_less g ((A ×ˢ A).image quotient.mk) ⟦a⟧ ⟦b⟧ _ _ _ _,
      suffices: ((A + A).card : ℚ) < ((A.card) + 1) / 2 * (A.card),
      linarith,
      rw ← card_change A,
      norm_cast,
      convert this,
      { sorry},
      { exact mem_image_of_mem quotient.mk hain,},
      { exact mem_image_of_mem quotient.mk hbin,},
      -- {have h11: },
      { have h' : ⟦(a.fst, a.snd)⟧ ≠ ⟦(b.fst, b.snd)⟧ := sorry,
        sorry,
      },
      { apply sym2_lift_sum_eq A,
        exact hain,
        exact hbin,
        exact hyp,
      }
      -- { rw sym2_lift_sum_eq,},
    },
    { norm_cast,
      rw nonempty_coe_sort at ha,
      rw ← finset.card_pos at ha,
      exact ha.ne'}, 
    -- rw sym2.add_set at p,
  },
end
--TO DO: 1) prove sidon_set_equiv_left
--2) push github
--3) lemma about paths of length three