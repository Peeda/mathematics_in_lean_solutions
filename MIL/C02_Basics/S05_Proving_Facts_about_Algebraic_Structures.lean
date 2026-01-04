import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    trans x ⊓ y
    repeat apply inf_le_left
    apply le_inf
    trans x ⊓ y
    apply inf_le_left
    apply inf_le_right
    apply inf_le_right
  · apply le_inf
    apply le_inf
    apply inf_le_left
    trans y ⊓ z
    apply inf_le_right
    apply inf_le_left
    trans y ⊓ z
    repeat apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    apply sup_le
    apply le_sup_left
    trans y ⊔ z
    apply le_sup_left
    apply le_sup_right
    trans y ⊔ z
    repeat apply le_sup_right
  · apply sup_le
    trans x ⊔ y
    repeat apply le_sup_left
    apply sup_le
    trans x ⊔ y
    apply le_sup_right
    apply le_sup_left
    trans y ⊔ z
    apply le_sup_right
    apply sup_le
    trans x ⊔ y
    apply le_sup_right
    apply le_sup_left
    apply le_sup_right


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  apply le_inf
  apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  apply sup_le
  apply le_refl
  apply inf_le_left
  apply le_sup_left
end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, inf_comm (a ⊔ b), absorb1, inf_comm (a ⊔ b), h, ← sup_assoc, inf_comm c, absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, sup_comm (a ⊓ b), absorb2, sup_comm (a ⊓ b), h, ← inf_assoc, sup_comm c, absorb1, sup_comm]

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
#check (sub_mul)

theorem thm1 (h : a ≤ b) : 0 ≤ b - a := by
  trans a - a
  rw [← neg_add_cancel a, add_comm, ← sub_eq_add_neg]
  exact tsub_le_tsub_right h a

theorem thm2 (h: 0 ≤ b - a) : a ≤ b := by
  trans a + b - a
  nth_rewrite 1 [← add_zero a];
  rewrite [add_sub_assoc]
  apply add_le_add_left h a
  rewrite [sub_eq_add_neg, add_assoc, add_comm, add_assoc, add_comm (-a), ← add_assoc, add_neg_cancel_right]
  exact le_refl b

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 <= (b - a) * c := mul_nonneg (thm1 a b h) h'
  apply thm2
  rw [← sub_mul]
  exact h1

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

#check nonneg_of_mul_nonneg_left

example (x y : X) : 0 ≤ dist x y := by
  have h: 0 <= dist x y * 2 := calc
    0 = dist x x := by symm; exact dist_self x
    _ <= dist x y + dist y x := dist_triangle x y x
    _ = dist x y + dist x y := by rw [dist_comm]
    _ = dist x y * 2 := by symm; exact mul_two (dist x y)
  have h1: (0 : ℝ) < 2 := by linarith
  exact nonneg_of_mul_nonneg_left h h1

end
