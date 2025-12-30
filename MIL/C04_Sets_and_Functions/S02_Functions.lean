import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h y ys
    have : f y ∈ f '' s := by use y
    exact h this
  · intro h y yfs
    obtain ⟨x, xs, rfl⟩ := yfs
    exact h xs


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x xinv
  obtain ⟨z, zin, eq⟩ := xinv
  have := h eq; rw [← this]; exact zin

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x xf
  obtain ⟨y, yin, rfl⟩ := xf
  exact yin

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x xin
  obtain ⟨y, fyeq⟩ := h x
  use y
  rw [← fyeq] at xin
  exact ⟨xin, fyeq⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x xin
  obtain ⟨y, yin, rfl⟩ := xin
  replace yin := h yin
  use y

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x xin
  exact h xin

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x xin
  obtain ⟨z, zin, fzeq⟩ := xin
  constructor
  use z
  exact ⟨zin.left, fzeq⟩
  use z
  exact ⟨zin.right, fzeq⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x xin
  obtain ⟨a, ain, aeq⟩ := xin.left
  obtain ⟨b, bin, beq⟩ := xin.right
  have : f a = f b := Eq.trans aeq beq.symm
  replace this := h this
  use a
  constructor; constructor
  exact ain
  rw [this]; exact bin
  exact aeq

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x ⟨xin, xnotin⟩
  obtain ⟨y, yin, yeq⟩ := xin
  use y
  constructor
  constructor
  exact yin
  contrapose! xnotin
  use y
  exact yeq

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x ⟨xin, xnotin⟩
  exact ⟨xin, xnotin⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  · intro ⟨xin, xinv⟩
    obtain ⟨a, ain, aeq⟩ := xin
    use a
    constructor
    constructor; exact ain
    rw [← aeq] at xinv
    exact xinv
    exact aeq
  intro xin
  obtain ⟨y, yin, rfl⟩ := xin
  constructor
  use y
  constructor; exact yin.left; rfl
  exact yin.right

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x xin
  obtain ⟨y, yin, rfl⟩ := xin
  constructor
  use y
  constructor; exact yin.left; rfl
  exact yin.right

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x xin
  show f x ∈ (f '' s ∩ u)
  constructor
  use x; constructor; exact xin.left; rfl
  exact xin.right

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x xin
  rcases xin with h | h
  left
  use x
  right
  exact h

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x; constructor
  · intro xin
    obtain ⟨a, h⟩ := xin
    simp at h
    obtain ⟨h, eq⟩ := h
    obtain ⟨i, ain⟩ := h
    simp
    use i; use a
  · intro xin
    simp; simp at xin
    obtain ⟨h, h1⟩ := xin
    obtain ⟨a, ain, aeq⟩ := h1
    use a; constructor
    use h; exact aeq


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro x xin
  obtain ⟨y, yin, rfl⟩ := xin
  simp; intro i
  use y; constructor
  simp at yin
  exact yin i; rfl

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x xin
  simp at xin; simp
  obtain ⟨y, yin, yeq⟩ := xin i
  use y; constructor
  intro i
  obtain ⟨y0, yin0, yeq0⟩ := xin i
  have := Eq.trans yeq yeq0.symm
  replace this := injf this; rw [← this] at yin0
  exact yin0; exact yeq

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x; simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x; simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
