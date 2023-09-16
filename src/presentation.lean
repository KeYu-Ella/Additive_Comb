import combinatorics.double_counting
import data.finset.pointwise
import data.sym.card
import data.rat.sqrt
import data.complex.basic


open finset 
open_locale pointwise

variables {G : Type} [add_comm_group G] [decidable_eq G] {A : finset G}

def doubling_constant (A : finset G) : ℚ := (A + A).card / A.card
notation `σ` := doubling_constant

def sidon_set (A: finset G) : Prop := σ A = (A.card + 1) / 2

lemma nat_2div_mul_self_add_mul (x : ℕ) : 2 ∣ x * (x + 1) :=
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

--g (⟦(a.1, a.2)⟧ ) = a.1 + a.2
def g : sym2 G → G := sym2.lift ⟨(+), add_comm⟩

lemma sym2.add_set (A : finset G) : A + A = image g A.sym2 :=
begin
  ext, -- Extend the statement elementwisely,
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

lemma sidon_set_equiv_right (A : finset G) (ha : nonempty A) : 
  (∀ a ∈ (A ×ˢ A), ∀ b ∈ A ×ˢ A, ⟦(a.1, a.2)⟧ = ⟦(b.1, b.2)⟧ ↔ a.1 + a.2 = b.1 + b.2)
  → sidon_set A :=
begin
  rw [sidon_set, doubling_constant, div_eq_iff],
  --After rewriting, it suffices to prove |A+A|=(|A|+1)*|A|/2, and |A| ≠ 0
  { intro p,
    have h' : (finset.image g A.sym2).card = A.card * (A.card + 1) / 2,
    -- card_sym2 A states that for any finset A, 
    --|A.sym2| = |A| * (|A| + 1) / 2
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
  -- Proving |A| ≠ 0 
  { norm_cast,
    rw [nonempty_coe_sort, ← finset.card_pos] at ha,
    exact ha.ne'},
end