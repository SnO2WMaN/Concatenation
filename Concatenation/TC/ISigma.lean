module

public import Concatenation.TC.Empty
public import Concatenation.ToFoundation.Arithmetic.BijectiveBinary

/-!
# $\mathsf{I}\Sigma_n$ interprets $\Sigma_n\text{-}\mathsf{TCI}$

A number is read as its bijective binary numeral, a string over the digits `1` and `2`: the empty
string is `0`, the letters are `1` and `2`, and the concatenation is `binaryAppend`. A substring is
not greater than the string, so a quantifier bounded by the substring relation becomes one bounded
by `≤`, the translation of a $\Sigma_n$ formula defines a $\Sigma_n$ relation, and notation
induction becomes induction along the numerals.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation Arithmetic Bounding.HierarchySymbol
open scoped FFL.FirstOrder.Arithmetic

section eval

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {W : Type*}
  [ConcatenationEmptyStructure W] (c : V ≃ W) (empty : c 0 = ∅) (zero : c 1 = 0) (one : c 2 = 1)
  (append : ∀ x y, c (binaryAppend x y) = c x ++ c y)

include append in
private lemma isSubstring_iff_binaryAppend {x y : V} : IsSubstring (c x) (c y) ↔ x = y ∨
    (∃ k ≤ y, binaryAppend k x = y) ∨ (∃ l ≤ y, binaryAppend x l = y) ∨
    (∃ k ≤ y, ∃ l ≤ y, binaryAppend (binaryAppend k x) l = y) ∨
    ∃ k ≤ y, ∃ l ≤ y, binaryAppend k (binaryAppend x l) = y := by
  constructor
  · rintro (h | ⟨k, h⟩ | ⟨l, h⟩ | ⟨k, l, h⟩ | ⟨k, l, h⟩)
    · exact .inl <| c.injective h
    · obtain ⟨k, rfl⟩ := c.surjective k
      obtain rfl := c.injective <| h.trans (append k x).symm
      exact .inr <| .inl ⟨k, le_binaryAppend_left _ _, rfl⟩
    · obtain ⟨l, rfl⟩ := c.surjective l
      obtain rfl := c.injective <| h.trans (append x l).symm
      exact .inr <| .inr <| .inl ⟨l, le_binaryAppend_right _ _, rfl⟩
    · obtain ⟨k, rfl⟩ := c.surjective k
      obtain ⟨l, rfl⟩ := c.surjective l
      rw [← append, ← append] at h
      obtain rfl := c.injective h
      exact .inr <| .inr <| .inr <| .inl ⟨k,
        (le_binaryAppend_left _ _).trans (le_binaryAppend_left _ _), l,
        le_binaryAppend_right _ _, rfl⟩
    · obtain ⟨k, rfl⟩ := c.surjective k
      obtain ⟨l, rfl⟩ := c.surjective l
      rw [← append, ← append] at h
      obtain rfl := c.injective h
      exact .inr <| .inr <| .inr <| .inr ⟨k, le_binaryAppend_left _ _, l,
        (le_binaryAppend_right _ _).trans (le_binaryAppend_right _ _), rfl⟩
  · rintro (rfl | ⟨k, -, rfl⟩ | ⟨l, -, rfl⟩ | ⟨k, -, l, -, rfl⟩ | ⟨k, -, l, -, rfl⟩)
    · exact .inl rfl
    · exact .inr <| .inl ⟨c k, append k x⟩
    · exact .inr <| .inr <| .inl ⟨c l, append x l⟩
    · exact .inr <| .inr <| .inr <| .inl ⟨c k, c l, by rw [append, append]⟩
    · exact .inr <| .inr <| .inr <| .inr ⟨c k, c l, by rw [append, append]⟩

include append in
private lemma definable_isSubstring :
    𝚺ᴬ₀.Definable fun v : Fin 2 → V ↦ IsSubstring (c (v 0)) (c (v 1)) := by
  simp only [isSubstring_iff_binaryAppend c append]
  definability

include empty zero one append in
private lemma definableBoundedFunction_val {k : ℕ} (ε : ℕ → W) (t : Semiterm ℒ⌢ₑ ℕ k) :
    DefinableBoundedFunction fun v : Fin k → V ↦ c.symm (t.val (fun i ↦ c (v i)) ε) := by
  induction t with
  | bvar i => simp
  | fvar x => simp
  | func f w ih =>
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · exact (DefinableBoundedFunction.const 1).of_iff fun v ↦ by
        change 1 = c.symm 0
        simp [← zero]
    · exact (DefinableBoundedFunction.const 2).of_iff fun v ↦ by
        change 2 = c.symm 1
        simp [← one]
    · exact (DefinableBoundedFunction.comp₂ (F := binaryAppend) (ih 0) (ih 1)).of_iff fun v ↦ by
        apply c.injective
        rw [append]
        simp only [Equiv.apply_symm_apply]
        rfl
    · exact (DefinableBoundedFunction.const 0).of_iff fun v ↦ by
        change 0 = c.symm ∅
        simp [← empty]

include append in
private lemma le_of_isSubstring {x y : V} (h : IsSubstring (c x) (c y)) : x ≤ y := by
  rcases (isSubstring_iff_binaryAppend c append).mp h with
    rfl | ⟨k, -, rfl⟩ | ⟨l, -, rfl⟩ | ⟨k, -, l, -, rfl⟩ | ⟨k, -, l, -, rfl⟩
  · rfl
  · exact le_binaryAppend_right _ _
  · exact le_binaryAppend_left _ _
  · exact (le_binaryAppend_right _ _).trans (le_binaryAppend_left _ _)
  · exact (le_binaryAppend_left _ _).trans (le_binaryAppend_right _ _)

include empty zero one append in
private lemma definable_eval_ball {k : ℕ} (ε : ℕ → W) {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]}
    {R : Semiformula.Operator ℒ⌢ₑ 2} (hR : R ∈ substringBounding ℒ⌢ₑ)
    {t : Semiterm ℒ⌢ₑ ℕ (k + 1)} (ht : t.Positive) {φ : Semiformula ℒ⌢ₑ ℕ (k + 1)}
    (h : ℌ.Definable fun v : Fin (k + 1) → V ↦ φ.Eval (fun i ↦ c (v i)) ε) :
    ℌ.Definable fun v : Fin k → V ↦ (∀¹[R.operator ![#0, t]] φ).Eval (fun i ↦ c (v i)) ε := by
  obtain rfl := mem_substringBounding_iff.mp hR
  obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
  have hB := definableBoundedFunction_val c empty zero one append ε t
  have hS : ℌ.Definable fun w : Fin (k + 1) → V ↦
      ¬IsSubstring (c (w 0)) (c (c.symm (t.val (fun i ↦ c (w i.succ)) ε))) :=
    (((definable_isSubstring c append).arithmetic_bounded_substitution
      (f := ![fun w ↦ w 0, fun w ↦ c.symm (t.val (fun i ↦ c (w i.succ)) ε)]) (by
        intro i
        cases i using Fin.cases with
        | zero => simp
        | succ i => simpa using hB.retraction Fin.succ)).notSigma.of_zero).of_iff fun w ↦ by simp
  have hw (w : Fin (k + 1) → V) : (w 0 :> fun j ↦ w j.succ) = w := Matrix.cons_head_tail w
  refine (Definable.arithmetic_ball_ble (P := fun v x ↦
      ¬IsSubstring (c x) (c (c.symm (t.val (fun i ↦ c (v i)) ε))) ∨
        φ.Eval (fun i ↦ c ((x :> v) i)) ε) hB
    ((hS.or h).of_iff fun w ↦ by rw [hw])).of_iff fun v ↦ ?_
  have hc (x : V) : (fun i ↦ c ((x :> v) i)) = (c x :> fun i ↦ c (v i)) := by
    funext i
    cases i using Fin.cases <;> simp
  simp only [hc, Semiformula.eval_ball, Semiformula.eval_operator, Matrix.comp₂,
    Semiterm.val_bvar, Matrix.cons_val_zero, Semiterm.val_bShift, Equiv.apply_symm_apply,
    substringOperator, Semiformula.Operator.val, Defined.eval_iff]
  constructor
  · intro H x _
    by_cases hs : IsSubstring (c x) (t.val (fun i ↦ c (v i)) ε)
    · exact .inr <| H _ hs
    · exact .inl hs
  · intro H x hx
    have hle := le_of_isSubstring c append (x := c.symm x)
      (y := c.symm (t.val (fun i ↦ c (v i)) ε)) (by simpa using hx)
    exact (by simpa using H (c.symm x) hle : _ ∨ _).resolve_left (not_not_intro hx)

include empty zero one append in
private lemma definable_eval_bexs {k : ℕ} (ε : ℕ → W) {ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ]}
    {R : Semiformula.Operator ℒ⌢ₑ 2} (hR : R ∈ substringBounding ℒ⌢ₑ)
    {t : Semiterm ℒ⌢ₑ ℕ (k + 1)} (ht : t.Positive) {φ : Semiformula ℒ⌢ₑ ℕ (k + 1)}
    (h : ℌ.Definable fun v : Fin (k + 1) → V ↦ φ.Eval (fun i ↦ c (v i)) ε) :
    ℌ.Definable fun v : Fin k → V ↦ (∃¹[R.operator ![#0, t]] φ).Eval (fun i ↦ c (v i)) ε := by
  obtain rfl := mem_substringBounding_iff.mp hR
  obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
  have hB := definableBoundedFunction_val c empty zero one append ε t
  have hS : ℌ.Definable fun w : Fin (k + 1) → V ↦
      IsSubstring (c (w 0)) (c (c.symm (t.val (fun i ↦ c (w i.succ)) ε))) :=
    (((definable_isSubstring c append).arithmetic_bounded_substitution
      (f := ![fun w ↦ w 0, fun w ↦ c.symm (t.val (fun i ↦ c (w i.succ)) ε)]) (by
        intro i
        cases i using Fin.cases with
        | zero => simp
        | succ i => simpa using hB.retraction Fin.succ)).of_zero).of_iff fun w ↦ by simp
  have hw (w : Fin (k + 1) → V) : (w 0 :> fun j ↦ w j.succ) = w := Matrix.cons_head_tail w
  refine (Definable.arithmetic_bexs_ble (P := fun v x ↦
      IsSubstring (c x) (c (c.symm (t.val (fun i ↦ c (v i)) ε))) ∧
        φ.Eval (fun i ↦ c ((x :> v) i)) ε) hB
    ((hS.and h).of_iff fun w ↦ by rw [hw])).of_iff fun v ↦ ?_
  have hc (x : V) : (fun i ↦ c ((x :> v) i)) = (c x :> fun i ↦ c (v i)) := by
    funext i
    cases i using Fin.cases <;> simp
  simp only [hc, Semiformula.eval_bexs, Semiformula.eval_operator, Matrix.comp₂,
    Semiterm.val_bvar, Matrix.cons_val_zero, Semiterm.val_bShift, Equiv.apply_symm_apply,
    substringOperator, Semiformula.Operator.val, Defined.eval_iff]
  constructor
  · rintro ⟨x, hx, H⟩
    refine ⟨c.symm x, le_of_isSubstring c append (by simpa using hx), ?_⟩
    simpa using And.intro hx H
  · rintro ⟨x, -, hx, H⟩
    exact ⟨c x, hx, H⟩

include empty zero one append in
private lemma definable_eval_of_closure (ε : ℕ → W) (ℌ : Bounding.HierarchySymbol ℬ[<, ℒₒᵣ])
    {k : ℕ} {φ : Semiformula ℒ⌢ₑ ℕ k} (hφ : (substringBounding ℒ⌢ₑ).Closure φ) :
    ℌ.Definable fun v : Fin k → V ↦ φ.Eval (fun i ↦ c (v i)) ε := by
  induction hφ with
  | verum => simp
  | falsum => simp
  | rel r w =>
    rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    have h₀ := definableBoundedFunction_val c empty zero one append ε (w 0)
    have h₁ := definableBoundedFunction_val c empty zero one append ε (w 1)
    exact (Definable.arithmetic_bounded_comp₂ (R := Eq) h₀ h₁).of_iff fun v ↦
      c.symm.apply_eq_iff_eq.symm
  | nrel r w =>
    rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    have h₀ := definableBoundedFunction_val c empty zero one append ε (w 0)
    have h₁ := definableBoundedFunction_val c empty zero one append ε (w 1)
    exact (Definable.arithmetic_bounded_comp₂ (ℌ := 𝚺ᴬ₀) (R := Eq) h₀ h₁).notSigma.of_zero.of_iff
      fun v ↦ not_congr c.symm.apply_eq_iff_eq.symm
  | and _ _ ihφ ihψ => exact (ihφ.and ihψ).of_iff fun v ↦ by simp
  | or _ _ ihφ ihψ => exact (ihφ.or ihψ).of_iff fun v ↦ by simp
  | ball hR ht _ ih => exact definable_eval_ball c empty zero one append ε hR ht ih
  | bexs hR ht _ ih => exact definable_eval_bexs c empty zero one append ε hR ht ih

include empty zero one append in
private lemma definable_eval (ε : ℕ → W) {Γ : Polarity} {s k : ℕ} {φ : Semiformula ℒ⌢ₑ ℕ k}
    (hφ : (substringBounding ℒ⌢ₑ).Hierarchy Γ s φ) :
    Γᴬ_[s].Definable fun v : Fin k → V ↦ φ.Eval (fun i ↦ c (v i)) ε := by
  have hc {k : ℕ} (v : Fin k → V) (x : V) :
      (fun i ↦ c ((x :> v) i)) = (c x :> fun i ↦ c (v i)) := by
    funext i
    cases i using Fin.cases <;> simp
  have hw {k : ℕ} (w : Fin (k + 1) → V) : (w 0 :> fun j ↦ w j.succ) = w := Matrix.cons_head_tail w
  have hexs {m k : ℕ} {ψ : Semiformula ℒ⌢ₑ ℕ (k + 1)}
      (h : 𝚺ᴬ_[m + 1].Definable fun v : Fin (k + 1) → V ↦ ψ.Eval (fun i ↦ c (v i)) ε) :
      𝚺ᴬ_[m + 1].Definable fun v : Fin k → V ↦ (∃¹ ψ).Eval (fun i ↦ c (v i)) ε :=
    (Definable.exs (P := fun v x ↦ ψ.Eval (fun i ↦ c ((x :> v) i)) ε)
      (h.of_iff fun w ↦ by rw [hw])).of_iff fun v ↦ by
        simp only [Semiformula.eval_ex, hc]
        exact ⟨fun ⟨x, hx⟩ ↦ ⟨c.symm x, by simpa using hx⟩, fun ⟨x, hx⟩ ↦ ⟨c x, hx⟩⟩
  have hall {m k : ℕ} {ψ : Semiformula ℒ⌢ₑ ℕ (k + 1)}
      (h : 𝚷ᴬ_[m + 1].Definable fun v : Fin (k + 1) → V ↦ ψ.Eval (fun i ↦ c (v i)) ε) :
      𝚷ᴬ_[m + 1].Definable fun v : Fin k → V ↦ (∀¹ ψ).Eval (fun i ↦ c (v i)) ε :=
    (Definable.all (P := fun v x ↦ ψ.Eval (fun i ↦ c ((x :> v) i)) ε)
      (h.of_iff fun w ↦ by rw [hw])).of_iff fun v ↦ by
        simp only [Semiformula.eval_all, hc]
        exact ⟨fun hx x ↦ hx (c x), fun hx x ↦ by simpa using hx (c.symm x)⟩
  induction hφ with
  | bounded Γ s n h => exact definable_eval_of_closure c empty zero one append ε _ h
  | and _ _ ihφ ihψ => exact (ihφ.and ihψ).of_iff fun v ↦ by simp
  | or _ _ ihφ ihψ => exact (ihφ.or ihψ).of_iff fun v ↦ by simp
  | ball hR ht _ ih => exact definable_eval_ball c empty zero one append ε hR ht ih
  | bexs hR ht _ ih => exact definable_eval_bexs c empty zero one append ε hR ht ih
  | exs _ ih => exact hexs ih
  | all _ ih => exact hall ih
  | sigma _ ih => exact hexs <| ih.of_lt <| by simp
  | pi _ ih => exact hall <| ih.of_lt <| by simp
  | dummy_sigma _ ih => exact (hall ih).of_lt <| by simp
  | dummy_pi _ ih => exact (hexs ih).of_lt <| by simp

include empty zero one append in
private lemma eval_notationInduction (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ 𝚺 s] {φ : Semiformula ℒ⌢ₑ ℕ 1}
    (hφ : (substringBounding ℒ⌢ₑ).Hierarchy 𝚺 s φ) (ε : ℕ → W) :
    Semiformula.Evalf ε (notationInduction φ) := by
  suffices φ.Eval ![∅] ε → (∀ x, φ.Eval ![x] ε → φ.Eval ![x ++ 0] ε ∧ φ.Eval ![x ++ 1] ε) →
      ∀ x, φ.Eval ![x] ε by
    simpa [notationInduction, Semiformula.eval_substs]
  intro hε hsucc x
  have hP : 𝚺ᴬ_[s].DefinablePred fun a : V ↦ φ.Eval ![c a] ε :=
    (definable_eval c empty zero one append ε hφ).of_iff fun v ↦ by
      rw [Matrix.fun_eq_vec_one (fun i ↦ c (v i))]
  have := InductionOnHierarchy.binary_induction 𝚺 s hP (by simpa [empty] using hε) fun a ha ↦ by
    have h := hsucc (c a) ha
    rw [← zero, ← one, ← append, ← append, binaryAppend_one, binaryAppend_two] at h
    exact h
  simpa using this (c.symm x)

include empty zero one append in
private lemma models_TCISigma (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ 𝚺 s] : W↓[ℒ⌢ₑ] ⊧* TCISigma s := by
  have : Nonempty W := ⟨∅⟩
  have hc : ∀ x : W, ∃ a, c a = x := c.surjective
  constructor
  intro σ hσ
  cases hσ with
  | notationInduction φ hφ =>
    simpa [models_iff, Semiformula.eval_univCl] using
      fun ε ↦ eval_notationInduction c empty zero one append s hφ.hierarchy ε
  | tcEmpty σ hσ =>
    cases hσ with
    | equal _ hφ => exact models_theory_iff.mp inferInstance _ hφ
    | emptyConcat =>
      suffices ∀ x : W, ∅ ++ x = x by simpa [models_iff]
      intro x
      obtain ⟨a, rfl⟩ := hc x
      rw [← empty, ← append, zero_binaryAppend]
    | concatEmpty =>
      suffices ∀ x : W, x ++ ∅ = x by simpa [models_iff]
      intro x
      obtain ⟨a, rfl⟩ := hc x
      rw [← empty, ← append, binaryAppend_zero]
    | concatAssoc =>
      suffices ∀ x y z : W, x ++ y ++ z = x ++ (y ++ z) by simpa [models_iff]
      intro x y z
      obtain ⟨a, rfl⟩ := hc x
      obtain ⟨b, rfl⟩ := hc y
      obtain ⟨d, rfl⟩ := hc z
      simp only [← append, binaryAppend_assoc]
    | editor =>
      suffices ∀ x y z w : W, x ++ y = z ++ w →
          ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) by simpa [models_iff]
      intro x y z w h
      obtain ⟨a, rfl⟩ := hc x
      obtain ⟨b, rfl⟩ := hc y
      obtain ⟨d, rfl⟩ := hc z
      obtain ⟨e, rfl⟩ := hc w
      simp only [← append, c.apply_eq_iff_eq] at h ⊢
      obtain ⟨u, hu⟩ := binaryAppend_editor h
      exact ⟨c u, by simpa only [← append, c.apply_eq_iff_eq] using hu⟩
    | zeroNeEmpty =>
      suffices (0 : W) ≠ ∅ by simpa [models_iff]
      simp [← zero, ← empty]
    | oneNeEmpty =>
      suffices (1 : W) ≠ ∅ by simpa [models_iff]
      simp [← one, ← empty]
    | zeroNeOne =>
      suffices (0 : W) ≠ 1 by simpa [models_iff]
      simp only [← zero, ← one, ne_eq, c.apply_eq_iff_eq]
      exact ne_of_lt one_lt_two
    | zeroAtom =>
      suffices ∀ x y : W, x ++ y = 0 → x = ∅ ∨ y = ∅ by simpa [models_iff]
      intro x y h
      obtain ⟨a, rfl⟩ := hc x
      obtain ⟨b, rfl⟩ := hc y
      simp only [← append, ← zero, ← empty, c.apply_eq_iff_eq] at h ⊢
      exact eq_zero_or_eq_zero_of_binaryAppend_eq_one h
    | oneAtom =>
      suffices ∀ x y : W, x ++ y = 1 → x = ∅ ∨ y = ∅ by simpa [models_iff]
      intro x y h
      obtain ⟨a, rfl⟩ := hc x
      obtain ⟨b, rfl⟩ := hc y
      simp only [← append, ← one, ← empty, c.apply_eq_iff_eq] at h ⊢
      exact eq_zero_or_eq_zero_of_binaryAppend_eq_two h

end eval

variable (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] [𝗜𝚺₀ ⪯ T]

/--
The translation of the language of concatenation with the empty string into arithmetic by the
bijective binary numerals: the empty string is `0`, the letters are `1` and `2`, and the
concatenation is `binaryAppend`.
- [HH14, Question 3]
-/
noncomputable def binaryTranslation : DirectTranslation T ℒ⌢ₑ where
  domain := ⟨⊤⟩
  rel
    | Sum.inl Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Sum.inl Language.Concatenation.Func.zero => ⟨“z. z = 1”⟩
    | Sum.inl Language.Concatenation.Func.one => ⟨“z. z = 2”⟩
    | Sum.inl Language.Concatenation.Func.concat => ⟨binaryAppendDef.val⟩
    | Sum.inr (Language.Constant.Func.const _) => ⟨“z. z = 0”⟩
  domain_nonempty := Arithmetic.complete.{0} _ _ fun V _ _ ↦
    (models_domainNonempty_iff _).mpr <| by simp [Semiformula.Operator.val]
  func_defined f := Arithmetic.complete.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := ModelsTheory.of_provably_subtheory V 𝗜𝚺₀ T inferInstance
    intro e _
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    all_goals simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
  preserve_eq := Arithmetic.complete.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

namespace binaryTranslation

variable {T} {V : Type} [ORingStructure V]

@[simp]
lemma dom (x : V) : (binaryTranslation T).Dom x := by
  simp [DirectTranslation.dom_iff, binaryTranslation, Semiformula.Operator.val]

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]

variable (V T) in
/-- The letters, the concatenation and the empty string of the bijective binary numerals. -/
noncomputable abbrev concatenationEmptyStructure :
    ConcatenationEmptyStructure ((binaryTranslation T).Model V) where
  zero := ⟨1, dom 1⟩
  one := ⟨2, dom 2⟩
  append x y := ⟨binaryAppend x y, dom _⟩
  emptyCollection := ⟨0, dom 0⟩

variable (V T) in
/-- The numbers as the elements of the model of `binaryTranslation`. -/
def equiv : V ≃ (binaryTranslation T).Model V where
  toFun x := ⟨x, dom x⟩
  invFun := Model.val
  left_inv _ := rfl
  right_inv _ := rfl

/--
The structure of the model of `binaryTranslation` is the one of the bijective binary numerals.
-/
lemma struc_eq [V↓[ℒₒᵣ] ⊧* T] :
    Model.struc (binaryTranslation T) V = @standardModelEmpty _ (concatenationEmptyStructure T V) :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      rcases f with (_ | _ | _) | ⟨⟨⟩⟩ <;>
        simp [binaryTranslation, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq] <;>
        rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext <| Model.eq_iff v)

end binaryTranslation

local instance (n : ℕ) : 𝗜𝚺₀ ⪯ 𝗜𝚺 n := ISigma_weakerThan_of_le n.zero_le

/--
The bijective binary numerals of a model of $\mathsf{I}\Sigma_n$ form a model of
$\Sigma_n\text{-}\mathsf{TCI}$.
- [HH14, Question 3]
-/
instance {V : Type} [ORingStructure V] (n : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝚺n] :
    ((binaryTranslation (𝗜𝚺 n)).Model V)↓[ℒ⌢ₑ] ⊧* TCISigma n := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := mod_ISigma_of_le n.zero_le
  rw [binaryTranslation.struc_eq]
  let := binaryTranslation.concatenationEmptyStructure (𝗜𝚺 n) V
  exact models_TCISigma (binaryTranslation.equiv (𝗜𝚺 n) V) rfl rfl rfl (fun _ _ ↦ rfl) n

/--
$\mathsf{I}\Sigma_n$ interprets $\Sigma_n\text{-}\mathsf{TCI}$ by the bijective binary numerals.
- [HH14, Question 3]
- [Gan09, Lemma 4]
-/
noncomputable instance binaryInterpretation (n : ℕ) : 𝗜𝚺 n ⊳ TCISigma n where
  trln := binaryTranslation (𝗜𝚺 n)
  interpret_theory _ hφ := Arithmetic.complete.{0} _ _ fun _ _ _ ↦
    DirectTranslation.models_translate_of_mem hφ

end FFL.FirstOrder.Concatenation
