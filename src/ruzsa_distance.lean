import data.complex.basic
import data.finset.basic
import data.finset.card
import data.nat.parity

open finset nat
open_locale pointwise
universes u v

variables {α β: Type*} [add_comm_group α] [decidable_eq α] {A B C : finset α}
-- [add_comm_group β] [decidable_eq β] {X Y Z : finset β}

def ruzsa_distance (A : finset α) (B : finset α) : ℂ := real.log 