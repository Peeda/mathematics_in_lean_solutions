import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  cases le_or_gt 0 x
  case inl h =>
    rw [abs_of_nonneg h]
  case inr h =>
    rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  cases le_or_gt 0 x
  case inl h =>
    rw [abs_of_nonneg h]
    linarith
  case inr h =>
    rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  cases le_or_gt 0 (x + y)
  case inl h =>
    rw [abs_of_nonneg h]
    trans |x| + y
    apply add_le_add_right; exact le_abs_self x
    apply add_le_add_left; exact le_abs_self y
  case inr h =>
    rw [abs_of_neg h, neg_add]
    trans |x| + (-y)
    apply add_le_add_right; exact neg_le_abs_self x
    apply add_le_add_left; exact neg_le_abs_self y

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  intro h
  cases le_or_gt 0 y
  case inl h1 =>
    rw [abs_of_nonneg h1] at h
    left; exact h
  case inr h1 =>
    rw [abs_of_neg h1] at h
    right; exact h
  intro h
  cases h
  case inl h1 =>
    linarith [h1, le_abs_self y]
  case inr h1 =>
    linarith [h1, neg_le_abs_self y]

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  rcases (le_or_gt 0 x) with h | h
  rw [abs_of_nonneg h]; intro h1;
  constructor
  linarith
  exact h1;
  rw [abs_of_neg h]; intro h1;
  constructor <;> linarith
  cases le_or_gt 0 x
  case inl h1 =>
    rintro ⟨h2, h3⟩
    rw [abs_of_nonneg h1]; exact h3
  case inr h1 =>
    rintro ⟨h2, h3⟩
    rw [abs_of_neg h1]; linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨a,b,rfl,rfl⟩ <;> linarith [pow_two_nonneg a, pow_two_nonneg b]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1 : (x + 1) * (x - 1) = 0 := by linarith
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h3
  right; linarith
  left; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : ((x + y) * (x - y) = 0) := by linarith
  rcases (eq_zero_or_eq_zero_of_mul_eq_zero this) with h1 | h1
  right; linarith
  left; linarith


section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1 : (x + 1) * (x - 1) = 0 := by
    ring_nf
    exact neg_add_eq_zero.mpr (id (Eq.symm h))
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h3
  right; exact Eq.symm (neg_eq_of_add_eq_zero_left h3)
  left; exact eq_of_sub_eq_zero h3


example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : ((x + y) * (x - y) = 0) := by
    ring_nf; exact Lean.Grind.IntModule.sub_eq_zero_iff.mpr h
  rcases (eq_zero_or_eq_zero_of_mul_eq_zero this) with h1 | h1
  right; exact eq_neg_of_add_eq_zero_left h1
  left; exact eq_of_sub_eq_zero h1

end

example (P : Prop) : ¬¬P → P := by
  intro h
  rcases em P with h | h
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h
  by_cases h' : P
  right; exact h h'
  left; exact h'
  intro h'
  rcases h' with h1 | h1
  contrapose! h1; exact h1.left
  intro h; assumption
