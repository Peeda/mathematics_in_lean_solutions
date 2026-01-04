import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext a b
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have nge_ns := le_trans (le_max_left Ns Nt) nge
  have nge_nt := le_trans (le_max_right Ns Nt) nge
  rw [add_sub_add_comm]
  calc
    |s n - a + (t n - b)| <= |s n - a| + |t n - b| := by apply abs_add
    _ < ε / 2 + ε / 2 := add_lt_add (hs n nge_ns) (ht n nge_nt)
    _ = ε := by linarith

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε epos; dsimp
  have εcpos : 0 < ε / |c| := by exact div_pos epos acpos
  obtain ⟨N, nclose⟩ := cs (ε / |c|) εcpos; use N
  intro n  ngtN
  have : ¬|c| = 0 := by exact abs_ne_zero.mpr h
  calc
    |c * s n - c * a| = |c * (s n - a)| := by congr; ring
    _ = |c| * |s n - a| := by apply abs_mul
    _ < |c| * (ε / |c|) := mul_lt_mul_of_pos_left (nclose n ngtN) acpos
    _ = ε := mul_div_cancel₀ ε this

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, oneclose⟩
  use N, |a| + 1
  intro n ngtN
  calc
    |s n| = |s n - a + a| := by ring_nf
    _ <= |s n - a| + |a| := by apply abs_add
    _ < |a| + 1 := by linarith [oneclose n ngtN]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n nbig
  have sbound := h₀ n (le_of_max_le_left nbig)
  have tbound := h₁ n (le_of_max_le_right nbig)
  rw [sub_zero] at tbound
  calc
    |s n * t n - 0| = |s n| * |t n| := by ring_nf; apply abs_mul
    _ < B * (ε / B) := mul_lt_mul'' (sbound) (tbound) (abs_nonneg s n) (abs_nonneg t n)
    _ = ε := mul_div_cancel₀ ε (ne_of_lt Bpos).symm

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left Na Nb)
  have absb : |s N - b| < ε := hNb N (le_max_right Na Nb)
  have : |a - b| < |a - b| := calc
    |a - b| = |a - s N + -(b - s N)| := by ring_nf
    _ <= |a - s N| + |-(b - s N)| := by apply abs_add
    _ = |s N - a| + |s N - b| := by
      rw [abs_neg, abs_sub_comm (s N), abs_sub_comm b]
    _ < |a - b| / 2 + |a - b| / 2 := add_lt_add absa absb
    _ = |a - b| := by linarith
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
