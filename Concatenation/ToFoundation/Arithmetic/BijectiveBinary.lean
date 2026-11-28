module

public import Foundation.FirstOrder.Arithmetic.Exponential.Log
public import Mathlib.Tactic.Ring

/-!
# Bijective binary numerals

A number `y` is the bijective binary numeral, a string over the digits `1` and `2`, of length
$\log_2 (y + 1)$; the concatenation of numerals, and induction along the numerals.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V]

section ISigma0

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {a p q u x y z w : V}

lemma Pow2.eq_of_le_of_lt (hp : Pow2 p) (hq : Pow2 q) (hpa : p ≤ a) (hap : a < 2 * p)
    (hqa : q ≤ a) (haq : a < 2 * q) : p = q :=
  le_antisymm ((Pow2.le_iff_lt_two hp hq).mpr <| lt_of_le_of_lt hpa haq)
    ((Pow2.le_iff_lt_two hq hp).mpr <| lt_of_le_of_lt hqa hap)

/-- The power of two of the length of the bijective binary numeral `y`. -/
noncomputable def lengthPow2 (y : V) : V := bexp (y + 1) (log (y + 1))

private lemma exponential_lengthPow2 (y : V) : Exponential (log (y + 1)) (lengthPow2 y) :=
  exp_bexp_of_lt <| by simp [length_of_pos (zero_le.trans_lt <| lt_add_one y)]

lemma pow2_lengthPow2 (y : V) : Pow2 (lengthPow2 y) := (exponential_lengthPow2 y).range_pow2

lemma lengthPow2_pos (y : V) : 0 < lengthPow2 y := (pow2_lengthPow2 y).pos

lemma lengthPow2_le (y : V) : lengthPow2 y ≤ y + 1 := by
  obtain ⟨p, hp, H, -⟩ := log_pos (zero_le.trans_lt <| lt_add_one y)
  exact (exponential_lengthPow2 y).uniq H ▸ hp

lemma lt_two_mul_lengthPow2 (y : V) : y + 1 < 2 * lengthPow2 y := by
  obtain ⟨p, -, H, h⟩ := log_pos (zero_le.trans_lt <| lt_add_one y)
  exact (exponential_lengthPow2 y).uniq H ▸ h

lemma lengthPow2_eq_of (hp : Pow2 p) (h₁ : p ≤ y + 1) (h₂ : y + 1 < 2 * p) : lengthPow2 y = p :=
  Pow2.eq_of_le_of_lt (pow2_lengthPow2 y) hp (lengthPow2_le y) (lt_two_mul_lengthPow2 y) h₁ h₂

@[simp]
lemma lengthPow2_zero : lengthPow2 (0 : V) = 1 := lengthPow2_eq_of pow2_one (by simp) (by simp)

@[simp]
lemma lengthPow2_one : lengthPow2 (1 : V) = 2 :=
  lengthPow2_eq_of pow2_two (by simp [one_add_one_eq_two]) (by
    simp [one_add_one_eq_two, two_mul_two_eq_four, Exponential.two_lt_four])

@[simp]
lemma lengthPow2_two : lengthPow2 (2 : V) = 2 :=
  lengthPow2_eq_of pow2_two (by simp) <| by
    simp [two_add_one_eq_three, two_mul_two_eq_four, Exponential.three_lt_four]

/-- The concatenation `x * lengthPow2 y + y` of the bijective binary numerals `x` and `y`. -/
noncomputable def binaryAppend (x y : V) : V := x * lengthPow2 y + y

lemma binaryAppend_graph :
    z = binaryAppend x y ↔ ∃ p ≤ y + 1, (Pow2 p ∧ p ≤ y + 1 ∧ y + 1 < 2 * p) ∧ z = x * p + y :=
  ⟨by
    rintro rfl
    exact ⟨lengthPow2 y, lengthPow2_le y,
      ⟨pow2_lengthPow2 y, lengthPow2_le y, lt_two_mul_lengthPow2 y⟩, rfl⟩, by
    rintro ⟨p, -, ⟨hp, h₁, h₂⟩, rfl⟩
    rw [binaryAppend, lengthPow2_eq_of hp h₁ h₂]⟩

/-- `z` is the concatenation of the bijective binary numerals `x` and `y`. -/
def binaryAppendDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma
  “z x y. ∃ p <⁺ y + 1, (!pow2Def p ∧ p ≤ y + 1 ∧ y + 1 < 2 * p) ∧ z = x * p + y”

instance binaryAppend_defined : 𝚺ᴬ₀-Function₂[V] binaryAppend via binaryAppendDef :=
  .mk fun v ↦ by simp [binaryAppendDef, binaryAppend_graph]

instance binaryAppend_definable : 𝚺ᴬ₀-Function₂[V] binaryAppend :=
  binaryAppend_defined.to_definable

lemma binaryAppend_le (x y : V) : binaryAppend x y ≤ x * (y + 1) + y := by
  simpa [binaryAppend] using mul_le_mul_left (a := x) (lengthPow2_le y)

instance : Bounded₂ (binaryAppend : V → V → V) :=
  ⟨‘x y. x * (y + 1) + y’, fun _ ↦ by simp [binaryAppend_le]⟩

@[simp]
lemma zero_binaryAppend (y : V) : binaryAppend 0 y = y := by simp [binaryAppend]

@[simp]
lemma binaryAppend_zero (x : V) : binaryAppend x 0 = x := by simp [binaryAppend]

lemma binaryAppend_one (x : V) : binaryAppend x 1 = 2 * x + 1 := by
  simp [binaryAppend, mul_comm]

lemma binaryAppend_two (x : V) : binaryAppend x 2 = 2 * x + 2 := by
  simp [binaryAppend, mul_comm]

lemma le_binaryAppend_left (x y : V) : x ≤ binaryAppend x y :=
  le_trans (le_mul_of_pos_right <| lengthPow2_pos y) le_self_add

lemma le_binaryAppend_right (x y : V) : y ≤ binaryAppend x y := le_add_self

lemma lengthPow2_binaryAppend (x y : V) :
    lengthPow2 (binaryAppend x y) = lengthPow2 x * lengthPow2 y := by
  apply lengthPow2_eq_of ((pow2_lengthPow2 x).mul (pow2_lengthPow2 y))
  · calc
      lengthPow2 x * lengthPow2 y ≤ (x + 1) * lengthPow2 y := mul_le_mul_right (lengthPow2_le x)
      _ = x * lengthPow2 y + lengthPow2 y := by ring
      _ ≤ x * lengthPow2 y + (y + 1) := by gcongr; exact lengthPow2_le y
      _ = binaryAppend x y + 1 := by simp [binaryAppend, add_assoc]
  · have hx : x + 2 ≤ 2 * lengthPow2 x := by
      simpa [add_assoc, one_add_one_eq_two] using (lt_iff_succ_le.mp <| lt_two_mul_lengthPow2 x)
    calc
      binaryAppend x y + 1 = x * lengthPow2 y + (y + 1) := by simp [binaryAppend, add_assoc]
      _ < x * lengthPow2 y + 2 * lengthPow2 y := by gcongr; exact lt_two_mul_lengthPow2 y
      _ = (x + 2) * lengthPow2 y := by ring
      _ ≤ 2 * lengthPow2 x * lengthPow2 y := mul_le_mul_right hx
      _ = 2 * (lengthPow2 x * lengthPow2 y) := by ring

lemma binaryAppend_assoc (x y z : V) :
    binaryAppend (binaryAppend x y) z = binaryAppend x (binaryAppend y z) := by
  conv_rhs => rw [binaryAppend, lengthPow2_binaryAppend]
  simp only [binaryAppend]
  ring

lemma eq_zero_or_eq_zero_of_binaryAppend_eq_one (h : binaryAppend x y = 1) : x = 0 ∨ y = 0 := by
  by_contra! hxy
  have : 2 ≤ binaryAppend x y := calc
    2 = 1 * 1 + 1 := by simp [one_add_one_eq_two]
    _ ≤ x * lengthPow2 y + y := add_le_add
      (mul_le_mul' (pos_iff_one_le.mp <| pos_iff_ne_zero.mpr hxy.1)
        (pos_iff_one_le.mp <| lengthPow2_pos y))
      (pos_iff_one_le.mp <| pos_iff_ne_zero.mpr hxy.2)
  simp [h] at this

lemma eq_zero_or_eq_zero_of_binaryAppend_eq_two (h : binaryAppend x y = 2) : x = 0 ∨ y = 0 := by
  by_contra! hxy
  have hy : 1 ≤ y := pos_iff_one_le.mp <| pos_iff_ne_zero.mpr hxy.2
  have hp : 2 ≤ lengthPow2 y := (pow2_lengthPow2 y).two_le fun h ↦ by
    have := lt_two_mul_lengthPow2 y
    simp only [h, mul_one] at this
    have : y + 1 ≤ 1 := lt_succ_iff_le.mp <| by simpa [one_add_one_eq_two] using this
    simp_all
  have : 3 ≤ binaryAppend x y := calc
    3 = 1 * 2 + 1 := by simp [two_add_one_eq_three]
    _ ≤ x * lengthPow2 y + y :=
      add_le_add (mul_le_mul' (pos_iff_one_le.mp <| pos_iff_ne_zero.mpr hxy.1) hp) hy
  simp [h, ← two_add_one_eq_three] at this

private lemma binaryAppend_editor_of_le (hle : lengthPow2 w ≤ lengthPow2 y)
    (h : binaryAppend x y = binaryAppend z w) :
    ∃ u, binaryAppend x u = z ∧ y = binaryAppend u w := by
  obtain ⟨r, hr⟩ := Pow2.dvd_of_le (pow2_lengthPow2 w) (pow2_lengthPow2 y) hle
  have hxz : x * r ≤ z := by
    by_contra! hlt
    have h₁ : (z + 1) * lengthPow2 w ≤ x * lengthPow2 y := by
      rw [hr, mul_comm (lengthPow2 w) r, ← mul_assoc]
      exact mul_le_mul_right <| lt_iff_succ_le.mp hlt
    have h₂ : z * lengthPow2 w + lengthPow2 w + y ≤ z * lengthPow2 w + w := by
      calc
        z * lengthPow2 w + lengthPow2 w + y = (z + 1) * lengthPow2 w + y := by ring
        _ ≤ x * lengthPow2 y + y := by gcongr
        _ = z * lengthPow2 w + w := h
    have h₃ : lengthPow2 w + y ≤ w := by
      simpa [add_assoc] using h₂
    have h₄ : y + 1 < lengthPow2 w := by
      have := lt_two_mul_lengthPow2 w
      rw [two_mul] at this
      have : lengthPow2 w + y + 1 < lengthPow2 w + lengthPow2 w :=
        lt_of_le_of_lt (add_le_add_left h₃ 1) this
      simpa [add_assoc] using this
    exact absurd (lt_of_lt_of_le h₄ <| le_trans hle (lengthPow2_le y)) (lt_irrefl _)
  obtain ⟨u, rfl⟩ := exists_add_of_le hxz
  have hy : y = binaryAppend u w := by
    have : x * lengthPow2 y + y = x * lengthPow2 y + (u * lengthPow2 w + w) := by
      calc
        x * lengthPow2 y + y = (x * r + u) * lengthPow2 w + w := h
        _ = x * lengthPow2 y + (u * lengthPow2 w + w) := by rw [hr]; ring
    exact add_left_cancel this
  refine ⟨u, ?_, hy⟩
  have hu : lengthPow2 u = r := by
    have : lengthPow2 u * lengthPow2 w = r * lengthPow2 w := by
      rw [← lengthPow2_binaryAppend, ← hy, hr, mul_comm]
    exact mul_right_cancel₀ (lengthPow2_pos w).ne' this
  simp [binaryAppend, hu]

/-- The editor axiom for the concatenation of bijective binary numerals. -/
lemma binaryAppend_editor (h : binaryAppend x y = binaryAppend z w) :
    ∃ u, (binaryAppend x u = z ∧ y = binaryAppend u w) ∨
      (x = binaryAppend z u ∧ binaryAppend u y = w) := by
  rcases le_total (lengthPow2 w) (lengthPow2 y) with hle | hle
  · obtain ⟨u, hu⟩ := binaryAppend_editor_of_le hle h
    exact ⟨u, .inl hu⟩
  · obtain ⟨u, h₁, h₂⟩ := binaryAppend_editor_of_le hle h.symm
    exact ⟨u, .inr ⟨h₁.symm, h₂.symm⟩⟩

/-- Induction along the bijective binary numerals. -/
lemma InductionOnHierarchy.binary_induction (Γ : SigmaPiDelta) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ 𝚺 s]
    {P : V → Prop} (hP : Γᴬ_[s].DefinablePred P) (zero : P 0)
    (succ : ∀ x, P x → P (2 * x + 1) ∧ P (2 * x + 2)) : ∀ x, P x := by
  apply InductionOnHierarchy.order_induction_sigma Γ s hP
  intro x IH
  obtain ⟨y, rfl | rfl⟩ := even_or_odd x
  · rcases eq_zero_or_pos y with rfl | hy
    · simpa using zero
    · obtain ⟨z, rfl⟩ := eq_succ_of_pos hy
      have : 2 * (z + 1) = 2 * z + 2 := by ring
      exact this ▸ (succ z <| IH z <| by
        rw [this]; exact lt_of_le_of_lt (le_mul_of_pos_left two_pos) (by simp)).2
  · exact (succ y <| IH y <| lt_of_le_of_lt (le_mul_of_pos_left two_pos) (by simp)).1

end ISigma0

end FFL.FirstOrder.Arithmetic
