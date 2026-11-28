module

public import Concatenation.TC.Empty
public import Concatenation.ToFoundation.PrenexDefinable
public import Concatenation.ToMathlib.VecCons

/-!
# Notation induction

Substrings and tallies in $\mathsf{TC}$ with the empty string, and induction and collection on
the tallies in the models of $\Sigma_n\text{-}\mathsf{TCI}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open Bounding

section TCEmpty

variable {V : Type*} [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] {c d k l u v w x y z : V}

namespace TCEmpty

lemma isSubstring_iff : IsSubstring x y ↔ ∃ u v, y = u ++ x ++ v := by
  constructor
  · rintro (rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩)
    · exact ⟨∅, ∅, by simp⟩
    · exact ⟨u, ∅, by simp⟩
    · exact ⟨∅, v, by simp⟩
    · exact ⟨u, v, rfl⟩
    · exact ⟨u, v, by simp [TCEmpty.append_assoc]⟩
  · rintro ⟨u, v, rfl⟩
    exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨u, v, rfl⟩

lemma isSubstring_append_append_of (h : IsSubstring x y) (u v : V) :
    IsSubstring x (u ++ y ++ v) := by
  obtain ⟨k, l, rfl⟩ := isSubstring_iff.mp h
  exact isSubstring_iff.mpr ⟨u ++ k, l ++ v, by simp [TCEmpty.append_assoc]⟩

lemma isSubstring_append_left_of (h : IsSubstring x y) (u : V) : IsSubstring x (u ++ y) := by
  simpa using isSubstring_append_append_of h u ∅

lemma isSubstring_append_right_of (h : IsSubstring x y) (v : V) : IsSubstring x (y ++ v) := by
  simpa using isSubstring_append_append_of h ∅ v

lemma isSubstring_trans (hxy : IsSubstring x y) (hyz : IsSubstring y z) : IsSubstring x z := by
  obtain ⟨k, l, rfl⟩ := isSubstring_iff.mp hyz
  exact isSubstring_append_append_of hxy k l

@[simp]
lemma empty_isSubstring (x : V) : IsSubstring ∅ x := isSubstring_iff.mpr ⟨∅, x, by simp⟩

@[simp]
lemma isSubstring_empty_iff : IsSubstring x ∅ ↔ x = ∅ := by
  constructor
  · intro h
    obtain ⟨k, l, h⟩ := isSubstring_iff.mp h
    exact (eq_empty_of_append_eq_empty (eq_empty_of_append_eq_empty h.symm).1).2
  · rintro rfl
    simp

lemma eq_of_isSubstring_isAtom (hc : IsAtom c) (h : IsSubstring x c) : x = ∅ ∨ x = c := by
  obtain ⟨k, l, h⟩ := isSubstring_iff.mp h
  rcases eq_empty_of_append_isAtom (h ▸ hc) with h' | rfl
  · obtain ⟨rfl, rfl⟩ := eq_empty_of_append_eq_empty h'
    simp
  · simp only [append_empty] at h
    rcases eq_empty_of_append_isAtom (h ▸ hc) with rfl | rfl
    · simp only [empty_append] at h
      exact Or.inr h.symm
    · simp

lemma eq_and_eq_of_append_isAtom (hc : IsAtom c) (hd : IsAtom d) (h : x ++ c = y ++ d) :
    x = y ∧ c = d := by
  obtain ⟨w, ⟨rfl, h'⟩ | ⟨rfl, h'⟩⟩ := editor h
  · rcases eq_empty_of_append_isAtom (h' ▸ hc) with rfl | h''
    · simp_all
    · exact absurd h'' (isAtom_ne_empty hd)
  · rcases eq_empty_of_append_isAtom (h' ▸ hd) with rfl | h''
    · simp_all
    · exact absurd h'' (isAtom_ne_empty hc)

lemma isSubstring_or_isSubstring_of_isAtom (hc : IsAtom c) (h : IsSubstring c (x ++ y)) :
    IsSubstring c x ∨ IsSubstring c y := by
  obtain ⟨k, l, h⟩ := isSubstring_iff.mp h
  obtain ⟨w, ⟨h₁, rfl⟩ | ⟨rfl, -⟩⟩ := editor h
  · obtain ⟨u, ⟨-, rfl⟩ | ⟨rfl, hu⟩⟩ := editor h₁
    · exact Or.inr <| isSubstring_iff.mpr ⟨u, l, rfl⟩
    · rcases eq_empty_of_append_isAtom (hu ▸ hc) with rfl | rfl
      · exact Or.inr <| isSubstring_iff.mpr ⟨∅, l, by simp_all⟩
      · exact Or.inl <| isSubstring_iff.mpr ⟨k, ∅, by simp_all⟩
  · exact Or.inl <| isSubstring_iff.mpr ⟨k, w, rfl⟩

@[simp]
lemma isTally_empty : IsTally c (∅ : V) := fun _ hy h ↦
  absurd (isSubstring_empty_iff.mp h) (isAtom_ne_empty hy)

lemma isTally_one : IsTally (1 : V) 1 := fun y hy h ↦ by
  rcases eq_of_isSubstring_isAtom isAtom_one h with rfl | rfl
  · exact absurd rfl (isAtom_ne_empty hy)
  · rfl

lemma isTally_of_isSubstring (hx : IsTally c x) (h : IsSubstring y x) : IsTally c y :=
  fun z hz hzy ↦ hx z hz (isSubstring_trans hzy h)

lemma isTally_append (hx : IsTally c x) (hy : IsTally c y) : IsTally c (x ++ y) := fun z hz h ↦
  (isSubstring_or_isSubstring_of_isAtom hz h).elim (hx z hz) (hy z hz)

lemma isTally_append_iff : IsTally c (x ++ y) ↔ IsTally c x ∧ IsTally c y :=
  ⟨fun h ↦ ⟨isTally_of_isSubstring h (isSubstring_append_left x y),
    isTally_of_isSubstring h (isSubstring_append_right x y)⟩, fun h ↦ isTally_append h.1 h.2⟩

lemma not_isTally_one_append_zero (x : V) : ¬IsTally 1 (x ++ 0) := fun h ↦
  TCEmpty.zero_ne_one <| h 0 isAtom_zero (isSubstring_append_right x 0)

lemma isTally_one_iff : IsTally 1 x ↔ ∀ y, IsSubstring y x → y ≠ 0 := by
  constructor
  · rintro h y hy rfl
    exact TCEmpty.zero_ne_one <| h 0 isAtom_zero hy
  · rintro h _ (rfl | rfl) hy
    · exact absurd rfl (h 0 hy)
    · rfl

end TCEmpty

end TCEmpty

section definitions

local notation "ℬₛ" => substringBounding ℒ⌢ₑ

variable {V : Type*} [ConcatenationEmptyStructure V]

@[simp]
lemma val_substringOperator_empty {v : Fin 2 → V} :
    (substringOperator ℒ⌢ₑ).val v ↔ IsSubstring (v 0) (v 1) := by
  simp [substringOperator, Semiformula.Operator.val]

/-- `x` is a `1`-tally: no substring of `x` is the letter `0`. -/
def isTallyOneDef : 𝚺-[ℬₛ, 0].Semisentence 1 :=
  .mkSigma “x. ∀¹[%(substringOperator _) #0 x] #0 ≠ !!(op(0).const)”

instance isTally_one_defined [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] :
    𝚺-[ℬₛ, 0]-Predicate[V] (IsTally 1) via isTallyOneDef :=
  .mk fun v ↦ by simp [isTallyOneDef, TCEmpty.isTally_one_iff]

instance isTally_one_definable [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] : 𝚺-[ℬₛ, 0]-Predicate[V] (IsTally 1) :=
  isTally_one_defined.to_definable

/-- `x` is a proper prefix of `y`: `y` is `x` followed by a nonempty string. -/
def IsProperPrefix (x y : V) : Prop := ∃ z, z ≠ ∅ ∧ y = x ++ z

/-- `x` is a proper prefix of `y`. -/
def isProperPrefixDef : 𝚺-[ℬₛ, 0].Semisentence 2 :=
  .mkSigma “x y. ∃¹[%(substringOperator _) #0 y] (#0 ≠ ⋆ ∧ y = x ⌢ #0)”

instance isProperPrefix_defined :
    𝚺-[ℬₛ, 0]-Relation[V] IsProperPrefix via isProperPrefixDef :=
  .mk fun v ↦ by
    suffices (∃ z, IsSubstring z (v 1) ∧ z ≠ ∅ ∧ v 1 = v 0 ++ z) ↔ ∃ z, z ≠ ∅ ∧ v 1 = v 0 ++ z by
      simpa [isProperPrefixDef, IsProperPrefix]
    exact ⟨fun ⟨z, _, h⟩ ↦ ⟨z, h⟩, fun ⟨z, h₁, h₂⟩ ↦ ⟨z, h₂ ▸ isSubstring_append_right _ _, h₁, h₂⟩⟩

instance isProperPrefix_definable : 𝚺-[ℬₛ, 0]-Relation[V] IsProperPrefix :=
  isProperPrefix_defined.to_definable

end definitions

section closure

local notation "ℬₛ" => substringBounding ℒ⌢ₑ

variable {V : Type*} [ConcatenationEmptyStructure V] {k : ℕ}

lemma definable_eq_term (t u : Semiterm ℒ⌢ₑ V k) :
    𝚺-[ℬₛ, 0].Definable fun v ↦ t.val v id = u.val v id :=
  (HierarchySymbol.DefinableRel.eq.retractiont ![t, u]).of_iff fun v ↦ by simp

lemma bexs_substring {P : (Fin k → V) → V → Prop}
    (hP : 𝚺-[ℬₛ, 0].Definable fun w ↦ P (w ·.succ) (w 0)) (t : Semiterm ℒ⌢ₑ V k) :
    𝚺-[ℬₛ, 0].Definable fun v ↦ ∃ x, IsSubstring x (t.val v id) ∧ P v x :=
  (HierarchySymbol.Definable.bexs (R := substringOperator ℒ⌢ₑ) rfl hP t).of_iff fun v ↦ by simp

lemma ball_substring {P : (Fin k → V) → V → Prop}
    (hP : 𝚺-[ℬₛ, 0].Definable fun w ↦ P (w ·.succ) (w 0)) (t : Semiterm ℒ⌢ₑ V k) :
    𝚺-[ℬₛ, 0].Definable fun v ↦ ∀ x, IsSubstring x (t.val v id) → P v x :=
  (HierarchySymbol.Definable.ball (R := substringOperator ℒ⌢ₑ) rfl hP t).of_iff fun v ↦ by simp

lemma definable_isSubstring_term (t u : Semiterm ℒ⌢ₑ V k) :
    𝚺-[ℬₛ, 0].Definable fun v ↦ IsSubstring (t.val v id) (u.val v id) :=
  (bexs_substring (P := fun v x ↦ x = t.val v id)
    ((definable_eq_term #0 (Rew.bShift t)).of_iff fun w ↦ by simp [Semiterm.val_bShift'])
    u).of_iff fun v ↦ by simp

/--
The relations with a prenex $\Sigma_1$ definition with parameters are closed under unbounded
existential quantification.
-/
lemma PrenexDefinable.exs_Sigma1 {Q : (Fin (k + 1) → V) → Prop}
    (hQ : PrenexDefinable ℬₛ 𝚺 1 Q) : PrenexDefinable ℬₛ 𝚺 1 fun v ↦ ∃ x, Q (x :> v) := by
  have : Nonempty V := ⟨∅⟩
  obtain ⟨R, hR, H⟩ := PrenexDefinable.sigma_succ_iff.mp hQ
  have hR := PrenexDefinable.zero_iff.mp hR
  have hD : 𝚺-[ℬₛ, 0].Definable fun w : Fin (k + 1) → V ↦
      ∃ x, IsSubstring x (w 0) ∧ ∃ y, IsSubstring y (w 0) ∧ R (y :> x :> fun i ↦ w i.succ) := by
    apply bexs_substring _ #0
    apply bexs_substring _ #1
    refine (hR.retraction (0 :> 1 :> fun l ↦ l.succ.succ.succ)).of_iff fun w ↦ iff_of_eq ?_
    congr 1
    funext i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun l ↦ ?_) j) i <;> simp
  refine PrenexDefinable.sigma_succ_iff.mpr ⟨_, PrenexDefinable.zero_iff.mpr hD, fun v ↦ ?_⟩
  simp only [H]
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨x ++ y, x, isSubstring_append_left x y, y, by simp, by simpa using h⟩
  · rintro ⟨z, x, -, y, -, h⟩
    exact ⟨x, y, by simpa using h⟩

lemma PrenexDefinable.and_Sigma1 {P Q : (Fin k → V) → Prop} (hP : PrenexDefinable ℬₛ 𝚺 1 P)
    (hQ : PrenexDefinable ℬₛ 𝚺 1 Q) : PrenexDefinable ℬₛ 𝚺 1 fun v ↦ P v ∧ Q v := by
  have : Nonempty V := ⟨∅⟩
  obtain ⟨R, hR, H⟩ := PrenexDefinable.sigma_succ_iff.mp hP
  have hQ' : PrenexDefinable ℬₛ 𝚺 1 fun w : Fin (k + 1) → V ↦ R w ∧ Q (fun i ↦ w i.succ) :=
    (hQ.retraction Fin.succ).and_delta0 (PrenexDefinable.zero_iff.mp hR) |>.of_iff
      fun w ↦ and_comm
  exact (PrenexDefinable.exs_Sigma1 hQ').of_iff fun v ↦ by simp [H]

lemma PrenexDefinable.or_Sigma1 {P Q : (Fin k → V) → Prop} (hP : PrenexDefinable ℬₛ 𝚺 1 P)
    (hQ : PrenexDefinable ℬₛ 𝚺 1 Q) : PrenexDefinable ℬₛ 𝚺 1 fun v ↦ P v ∨ Q v := by
  have : Nonempty V := ⟨∅⟩
  obtain ⟨R, hR, H⟩ := PrenexDefinable.sigma_succ_iff.mp hP
  obtain ⟨S, hS, H'⟩ := PrenexDefinable.sigma_succ_iff.mp hQ
  exact PrenexDefinable.sigma_succ_iff.mpr ⟨fun w ↦ R w ∨ S w,
    PrenexDefinable.zero_iff.mpr <| (PrenexDefinable.zero_iff.mp hR).or
      (PrenexDefinable.zero_iff.mp hS), fun v ↦ by simp [H, H', exists_or]⟩

lemma PrenexDefinable.all_Pi1 {Q : (Fin (k + 1) → V) → Prop}
    (hQ : PrenexDefinable ℬₛ 𝚷 1 Q) : PrenexDefinable ℬₛ 𝚷 1 fun v ↦ ∀ x, Q (x :> v) :=
  (PrenexDefinable.exs_Sigma1 hQ.not).not.of_iff fun v ↦ by simp

end closure

section notationInduction

local notation "ℬₛ" => substringBounding ℒ⌢ₑ

variable {V : Type*} [ConcatenationEmptyStructure V] {s : ℕ}

lemma TCISigma.models_TCEmpty (s : ℕ) [V↓[ℒ⌢ₑ] ⊧* TCISigma s] : V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ :=
  models_of_ss (U := TCISigma s) inferInstance IsTCISigmaAxiom.tcEmpty

instance [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] : V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ := TCISigma.models_TCEmpty 1

/--
The models of $\Sigma_{s'}\text{-}\mathsf{TCI}$ are models of $\Sigma_s\text{-}\mathsf{TCI}$ for
`s ≤ s'`.
-/
lemma TCISigma.models_of_le {s' : ℕ} [V↓[ℒ⌢ₑ] ⊧* TCISigma s'] (hs : s ≤ s') :
    V↓[ℒ⌢ₑ] ⊧* TCISigma s := by
  have : V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ := TCISigma.models_TCEmpty s'
  have : Nonempty V := ⟨∅⟩
  apply models_theory_iff.mpr
  intro σ hσ
  rcases hσ with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact models_theory_iff.mp inferInstance _ hφ
  · obtain ⟨ψ, hψ, H⟩ := hφ.exists_eval_iff_of_le hs
    have h : ∀ f : ℕ → V, ψ.Eval ![∅] f →
        (∀ x, ψ.Eval ![x] f → ψ.Eval ![x ++ 0] f ∧ ψ.Eval ![x ++ 1] f) → ∀ x, ψ.Eval ![x] f := by
      simpa [models_iff, notationInduction, Semiformula.eval_substs] using
        Theory.models (T := TCISigma s') V (IsTCISigmaAxiom.notationInduction ψ hψ)
    suffices ∀ f : ℕ → V, φ.Eval ![∅] f →
        (∀ x, φ.Eval ![x] f → φ.Eval ![x ++ 0] f ∧ φ.Eval ![x ++ 1] f) → ∀ x, φ.Eval ![x] f by
      simpa [models_iff, notationInduction, Semiformula.eval_substs] using this
    intro f h₀ h₁ x
    have H' (y : V) := H V ![y] f
    exact (H' x).mpr <| h f ((H' ∅).mp h₀) (fun y hy ↦ by
      simpa only [H'] using h₁ y ((H' y).mpr hy)) x

/--
Notation induction for a predicate defined by a prenex $\Sigma_s$ formula with parameters.
- [HH14, Question 3]
-/
@[elab_as_elim]
lemma TCISigma.notation_induction [V↓[ℒ⌢ₑ] ⊧* TCISigma s] {P : V → Prop}
    (hP : PrenexDefinable ℬₛ 𝚺 s fun v : Fin 1 → V ↦ P (v 0)) (empty : P ∅)
    (append : ∀ x, P x → P (x ++ 0) ∧ P (x ++ 1)) : ∀ x, P x := by
  intro x
  have : Nonempty V := ⟨∅⟩
  obtain ⟨e, φ, hφ, H⟩ := hP.exists_eval_iff
  have h : ∀ f : ℕ → V, φ.Eval ![∅] f →
      (∀ x, φ.Eval ![x] f → φ.Eval ![x ++ 0] f ∧ φ.Eval ![x ++ 1] f) → ∀ x, φ.Eval ![x] f := by
    simpa [models_iff, notationInduction, Semiformula.eval_substs] using
      Theory.models (T := TCISigma s) V (IsTCISigmaAxiom.notationInduction φ hφ)
  have H' (y : V) : P y ↔ φ.Eval ![y] e := by simpa using H ![y]
  simp only [H'] at empty append ⊢
  exact h e empty append x

section

variable [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] {c u v w x y z : V}

@[elab_as_elim]
lemma TCISigma.delta0_induction {P : V → Prop} (hP : 𝚺-[ℬₛ, 0].DefinablePred P) (empty : P ∅)
    (append : ∀ x, P x → P (x ++ 0) ∧ P (x ++ 1)) : ∀ x, P x :=
  have : Nonempty V := ⟨∅⟩
  TCISigma.notation_induction (s := 1) (.of_delta0 hP) empty append

namespace TCISigma

lemma eq_empty_or_eq_append_isAtom (x : V) : x = ∅ ∨ ∃ u c, IsAtom c ∧ x = u ++ c := by
  have : ∀ x : V, x = ∅ ∨ ∃ u, IsSubstring u x ∧ (x = u ++ 0 ∨ x = u ++ 1) := by
    apply delta0_induction
    · exact .mkPolarity (ℬ := ℬₛ) (Γ := 𝚺) (m := 0) “x. x = ⋆ ∨ ∃¹[%(substringOperator _) #0 x]
        (x = #0 ⌢ !!(op(0).const) ∨ x = #0 ⌢ !!(op(1).const))” (by simp) (fun v ↦ by simp)
    · simp
    · exact fun x _ ↦ ⟨.inr ⟨x, by simp⟩, .inr ⟨x, by simp⟩⟩
  rcases this x with h | ⟨u, -, h | h⟩
  · exact .inl h
  · exact .inr ⟨u, 0, by simp, h⟩
  · exact .inr ⟨u, 1, by simp, h⟩

lemma eq_empty_or_eq_isAtom_append (x : V) : x = ∅ ∨ ∃ c u, IsAtom c ∧ x = c ++ u := by
  have : ∀ x : V, x = ∅ ∨ ∃ u, IsSubstring u x ∧ (x = 0 ++ u ∨ x = 1 ++ u) := by
    apply delta0_induction
    · exact .mkPolarity (ℬ := ℬₛ) (Γ := 𝚺) (m := 0) “x. x = ⋆ ∨ ∃¹[%(substringOperator _) #0 x]
        (x = !!(op(0).const) ⌢ #0 ∨ x = !!(op(1).const) ⌢ #0)” (by simp) (fun v ↦ by simp)
    · simp
    · have H (c : V) (hc : IsAtom c) : ∀ x : V,
          (x = ∅ ∨ ∃ u, IsSubstring u x ∧ (x = 0 ++ u ∨ x = 1 ++ u)) →
          ∃ u, IsSubstring u (x ++ c) ∧ (x ++ c = 0 ++ u ∨ x ++ c = 1 ++ u) := by
        rintro x (rfl | ⟨u, -, rfl | rfl⟩)
        · rcases hc with rfl | rfl <;> exact ⟨∅, by simp⟩
        · exact ⟨u ++ c, by simp [TCEmpty.append_assoc]⟩
        · exact ⟨u ++ c, by simp [TCEmpty.append_assoc]⟩
      exact fun x ih ↦ ⟨.inr (H 0 (by simp) x ih), .inr (H 1 (by simp) x ih)⟩
  rcases this x with h | ⟨u, -, h | h⟩
  · exact .inl h
  · exact .inr ⟨0, u, by simp, h⟩
  · exact .inr ⟨1, u, by simp, h⟩

lemma append_right_cancel (h : x ++ z = y ++ z) : x = y := by
  revert h
  revert z
  apply delta0_induction (P := fun z ↦ x ++ z = y ++ z → x = y) _ (by simp)
  · intro z ih
    constructor <;> intro h <;> apply ih <;>
      [exact (TCEmpty.eq_and_eq_of_append_isAtom isAtom_zero isAtom_zero <| by
        simpa [TCEmpty.append_assoc] using h).1;
      exact (TCEmpty.eq_and_eq_of_append_isAtom isAtom_one isAtom_one <| by
        simpa [TCEmpty.append_assoc] using h).1]
  · exact .mkPolarity (ℬ := ℬₛ) (Γ := 𝚺) (m := 0) “z. &x ⌢ z = &y ⌢ z → &x = &y” (by simp)
      (fun v ↦ by simp)

lemma eq_empty_of_append_eq_self (h : x ++ w = x) : w = ∅ := by
  have : ∀ x : V, ∀ w, IsSubstring w x → x ++ w = x → w = ∅ := by
    apply delta0_induction
    · exact .mkPolarity (ℬ := ℬₛ) (Γ := 𝚺) (m := 0)
        “x. ∀¹[%(substringOperator _) #0 x] (x ⌢ #0 = x → #0 = ⋆)”
        (by simp) (fun v ↦ by simp)
    · simp
    · have H : ∀ x c : V, IsAtom c → (∀ w, IsSubstring w x → x ++ w = x → w = ∅) →
          ∀ w, IsSubstring w (x ++ c) → x ++ c ++ w = x ++ c → w = ∅ := by
        intro x c hc ih w _ h
        by_contra hw
        rcases eq_empty_or_eq_append_isAtom w with rfl | ⟨w', d, hd, rfl⟩
        · exact hw rfl
        obtain ⟨h₁, -⟩ :=
            TCEmpty.eq_and_eq_of_append_isAtom (x := x ++ c ++ w') (y := x) hd hc <| by
          simpa [TCEmpty.append_assoc] using h
        have h₂ : x ++ (c ++ w') = x := by simpa [TCEmpty.append_assoc] using h₁
        have h₃ := ih _ (h₂ ▸ isSubstring_append_right x (c ++ w')) h₂
        exact TCEmpty.isAtom_ne_empty hc (TCEmpty.eq_empty_of_append_eq_empty h₃).1
      exact fun x ih ↦ ⟨H x 0 isAtom_zero ih, H x 1 isAtom_one ih⟩
  exact this x w (h ▸ isSubstring_append_right x w) h

lemma one_append_eq_append_one (hx : IsTally 1 x) : 1 ++ x = x ++ 1 := by
  revert x
  apply delta0_induction (P := fun x ↦ IsTally 1 x → 1 ++ x = x ++ 1)
  · exact .mkPolarity (ℬ := ℬₛ) (Γ := 𝚺) (m := 0)
      “x. !(Rewriting.emb isTallyOneDef.val) x → !!(op(1).const) ⌢ x = x ⌢ !!(op(1).const)”
      (by simp) (fun v ↦ by simp)
  · simp
  · intro x ih
    refine ⟨fun h ↦ absurd h (TCEmpty.not_isTally_one_append_zero x), fun h ↦ ?_⟩
    rw [← TCEmpty.append_assoc, ih (TCEmpty.isTally_append_iff.mp h).1]

lemma append_comm (hx : IsTally 1 x) (hy : IsTally 1 y) : x ++ y = y ++ x := by
  revert y
  apply delta0_induction (P := fun y ↦ IsTally 1 y → x ++ y = y ++ x)
  · exact .mkPolarity (ℬ := ℬₛ) (Γ := 𝚺) (m := 0)
      “y. !(Rewriting.emb isTallyOneDef.val) y → &x ⌢ y = y ⌢ &x” (by simp) (fun v ↦ by simp)
  · simp
  · intro y ih
    refine ⟨fun h ↦ absurd h (TCEmpty.not_isTally_one_append_zero y), fun h ↦ ?_⟩
    rw [← TCEmpty.append_assoc, ih (TCEmpty.isTally_append_iff.mp h).1, TCEmpty.append_assoc,
      ← one_append_eq_append_one hx, TCEmpty.append_assoc]

lemma eq_append_one_of_ne_empty (hx : IsTally 1 x) (h : x ≠ ∅) :
    ∃ x', IsTally 1 x' ∧ x = x' ++ 1 := by
  rcases eq_empty_or_eq_append_isAtom x with rfl | ⟨u, c, hc, rfl⟩
  · exact absurd rfl h
  · obtain ⟨hu, hc'⟩ := TCEmpty.isTally_append_iff.mp hx
    obtain rfl : c = 1 := hc' c hc (IsSubstring.refl c)
    exact ⟨u, hu, rfl⟩

lemma exists_append_eq_or_exists_append_eq (hx : IsTally 1 x) (hy : IsTally 1 y) :
    (∃ z, x ++ z = y) ∨ ∃ z, y ++ z = x := by
  have : ∀ y : V, IsTally 1 y →
      (∃ z, IsSubstring z y ∧ x ++ z = y) ∨ ∃ z, IsSubstring z x ∧ y ++ z = x := by
    apply delta0_induction
    · exact .mkPolarity (ℬ := ℬₛ) (Γ := 𝚺) (m := 0)
        “y. !(Rewriting.emb isTallyOneDef.val) y →
          (∃¹[%(substringOperator _) #0 y] &x ⌢ #0 = y) ∨
          (∃¹[%(substringOperator _) #0 &x] y ⌢ #0 = &x)” (by simp) (fun v ↦ by simp)
    · exact fun _ ↦ .inr ⟨x, IsSubstring.refl x, by simp⟩
    · intro y ih
      refine ⟨fun h ↦ absurd h (TCEmpty.not_isTally_one_append_zero y), fun h ↦ ?_⟩
      have hy := (TCEmpty.isTally_append_iff.mp h).1
      rcases ih hy with ⟨z, -, rfl⟩ | ⟨z, hz, rfl⟩
      · exact .inl ⟨z ++ 1, by simp [TCEmpty.append_assoc], by simp [TCEmpty.append_assoc]⟩
      · by_cases hz' : z = ∅
        · subst hz'
          exact .inl ⟨1, by simp, by simp⟩
        · obtain ⟨z', -, rfl⟩ := eq_append_one_of_ne_empty
            (TCEmpty.isTally_of_isSubstring hx hz) hz'
          refine .inr ⟨z', TCEmpty.isSubstring_append_left_of (by simp) y, ?_⟩
          rw [TCEmpty.append_assoc, one_append_eq_append_one
            (TCEmpty.isTally_of_isSubstring hx (TCEmpty.isSubstring_trans (by simp) hz))]
  rcases this y hy with ⟨z, -, h⟩ | ⟨z, -, h⟩
  exacts [.inl ⟨z, h⟩, .inr ⟨z, h⟩]

lemma exists_append_eq_of_isSubstring (hy : IsTally 1 y) (h : IsSubstring u y) :
    IsTally 1 u ∧ ∃ l, IsTally 1 l ∧ u ++ l = y := by
  obtain ⟨k, l, rfl⟩ := TCEmpty.isSubstring_iff.mp h
  obtain ⟨hku, hl⟩ := TCEmpty.isTally_append_iff.mp hy
  obtain ⟨hk, hu⟩ := TCEmpty.isTally_append_iff.mp hku
  refine ⟨hu, k ++ l, TCEmpty.isTally_append hk hl, ?_⟩
  rw [← TCEmpty.append_assoc, append_comm hu hk]

lemma isSubstring_and_ne_iff (hy : IsTally 1 y) :
    IsSubstring u y ∧ u ≠ y ↔ IsTally 1 u ∧ IsProperPrefix u y := by
  constructor
  · rintro ⟨h, hne⟩
    obtain ⟨hu, l, -, rfl⟩ := exists_append_eq_of_isSubstring hy h
    refine ⟨hu, l, fun hl ↦ hne ?_, rfl⟩
    simp [hl]
  · rintro ⟨-, z, hz, rfl⟩
    exact ⟨by simp, fun h ↦ hz (eq_empty_of_append_eq_self h.symm)⟩

lemma isSubstring_append_one_cases (hy : IsTally 1 (y ++ 1)) (h : IsSubstring u (y ++ 1)) :
    IsSubstring u y ∨ u = y ++ 1 := by
  obtain ⟨-, l, hl, h⟩ := exists_append_eq_of_isSubstring hy h
  by_cases hl' : l = ∅
  · subst hl'
    exact .inr (by simpa using h)
  · obtain ⟨l', -, rfl⟩ := eq_append_one_of_ne_empty hl hl'
    have : u ++ l' = y := (TCEmpty.eq_and_eq_of_append_isAtom isAtom_one isAtom_one <| by
      simpa [TCEmpty.append_assoc] using h).1
    exact .inl (this ▸ isSubstring_append_left u l')

lemma append_eq_self_iff (hx : IsTally 1 x) (hw : IsTally 1 w) : w ++ x = x ↔ w = ∅ :=
  ⟨fun h ↦ eq_empty_of_append_eq_self (by rwa [append_comm hx hw]), by rintro rfl; simp⟩

end TCISigma

end

namespace TCISigma

/-- Induction on the tallies for a predicate with a prenex $\Sigma_s$ definition. -/
lemma tally_induction [V↓[ℒ⌢ₑ] ⊧* TCISigma s] {P : V → Prop}
    (hP : PrenexDefinable ℬₛ 𝚺 s fun v : Fin 1 → V ↦ P (v 0)) (zero : P ∅)
    (succ : ∀ x, IsTally 1 x → P x → P (x ++ 1)) : ∀ x, IsTally 1 x → P x := by
  have : V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ := TCISigma.models_TCEmpty s
  have : Nonempty V := ⟨∅⟩
  have key : ∀ x, P x ∨ ¬IsTally 1 x := by
    refine notation_induction (s := s) (P := fun x ↦ P x ∨ ¬IsTally 1 x) ?_ ?_ ?_
    · exact hP.or_delta0 isTally_one_definable.not_zero
    · exact .inl zero
    · intro x ih
      refine ⟨.inr (TCEmpty.not_isTally_one_append_zero x), ?_⟩
      by_cases h : IsTally 1 (x ++ 1)
      · have hx := (TCEmpty.isTally_append_iff.mp h).1
        exact .inl (succ x hx (ih.resolve_right (not_not.mpr hx)))
      · exact .inr h
  exact fun x hx ↦ (key x).resolve_right (not_not.mpr hx)

variable [V↓[ℒ⌢ₑ] ⊧* TCISigma 1]

/--
Induction on the tallies for a predicate with a prenex $\Pi_1$ definition.
-/
lemma tally_induction_Pi1 {P : V → Prop}
    (hP : PrenexDefinable ℬₛ 𝚷 1 fun v : Fin 1 → V ↦ P (v 0)) (zero : P ∅)
    (succ : ∀ x, IsTally 1 x → P x → P (x ++ 1)) : ∀ x, IsTally 1 x → P x := by
  have : Nonempty V := ⟨∅⟩
  intro c hc
  by_contra hPc
  have H : ∀ d, IsTally 1 d → ¬IsSubstring d c ∨ ∃ e, IsSubstring e c ∧ e ++ d = c ∧ ¬P e := by
    apply tally_induction (s := 1)
      (P := fun d ↦ ¬IsSubstring d c ∨ ∃ e, IsSubstring e c ∧ e ++ d = c ∧ ¬P e)
    · refine ((PrenexDefinable.exs_Sigma1 <| (hP.not.retraction ![0]).and_delta0 <|
        (definable_isSubstring_term #0 &c).and (definable_eq_term ‘#0 ⌢ #1’ &c)).or_delta0
        (definable_isSubstring_term #0 &c).not_zero).of_iff fun v ↦ by
          simp [or_comm, and_comm, and_assoc]
    · exact .inr ⟨c, IsSubstring.refl c, by simp, hPc⟩
    · intro d hd ih
      refine or_iff_not_imp_left.mpr fun hdc ↦ ?_
      have hdc := not_not.mp hdc
      obtain ⟨e, hec, rfl, he⟩ := (ih.resolve_left <| not_not.mpr <|
        TCEmpty.isSubstring_trans (isSubstring_append_left d 1) hdc)
      have heT := TCEmpty.isTally_of_isSubstring hc hec
      by_cases he' : e = ∅
      · subst he'
        obtain ⟨-, l, -, hl⟩ := exists_append_eq_of_isSubstring hc hdc
        have : 1 ++ l = ∅ := eq_empty_of_append_eq_self (x := d) <| by
          simpa [TCEmpty.append_assoc] using hl
        exact absurd (TCEmpty.eq_empty_of_append_eq_empty this).1 TCEmpty.one_ne_empty
      · obtain ⟨e', he'T, rfl⟩ := eq_append_one_of_ne_empty heT he'
        refine ⟨e', TCEmpty.isSubstring_trans (by simp) hec, ?_,
          fun h ↦ he (succ e' he'T h)⟩
        rw [← one_append_eq_append_one hd, ← TCEmpty.append_assoc]
  obtain ⟨e, -, he, hPe⟩ := (H c hc).resolve_left (not_not.mpr (IsSubstring.refl c))
  obtain rfl := (append_eq_self_iff hc (TCEmpty.isTally_of_isSubstring hc (he ▸
    isSubstring_append_left e c))).mp he
  exact hPe zero

/--
Collection for a $\Delta_0$ relation over the substrings of a tally.
-/
lemma collection {θ : V → V → Prop}
    (hθ : 𝚺-[ℬₛ, 0].Definable fun v : Fin 2 → V ↦ θ (v 0) (v 1)) {b : V} (hb : IsTally 1 b)
    (h : ∀ y, IsSubstring y b → ∃ w, θ y w) :
    ∃ W, ∀ y, IsSubstring y b → ∃ w, IsSubstring w W ∧ θ y w := by
  have : Nonempty V := ⟨∅⟩
  have H : ∀ u, IsTally 1 u → (∃ W, ∀ y, IsSubstring y u → ∃ w, IsSubstring w W ∧ θ y w) ∨
      ¬IsSubstring u b := by
    apply tally_induction (s := 1) (P := fun u ↦
      (∃ W, ∀ y, IsSubstring y u → ∃ w, IsSubstring w W ∧ θ y w) ∨ ¬IsSubstring u b)
    · have hD : 𝚺-[ℬₛ, 0].Definable fun w : Fin 2 → V ↦
          ∀ y, IsSubstring y (w 1) → ∃ x, IsSubstring x (w 0) ∧ θ y x := by
        apply ball_substring _ #1
        apply bexs_substring _ #1
        exact (hθ.retraction ![1, 0]).of_iff fun v ↦ by simp
      exact (PrenexDefinable.sigma_succ_iff.mpr ⟨_, PrenexDefinable.zero_iff.mpr hD,
        fun v ↦ Iff.rfl⟩).or_delta0 (definable_isSubstring_term #0 &b).not_zero |>.of_iff
          fun v ↦ by simp
    · obtain ⟨w₀, hw₀⟩ := h ∅ (by simp)
      exact .inl ⟨w₀, fun y hy ↦ ⟨w₀, IsSubstring.refl w₀, by simpa using
        (TCEmpty.isSubstring_empty_iff.mp hy) ▸ hw₀⟩⟩
    · intro u hu ih
      refine or_iff_not_imp_right.mpr fun hub ↦ ?_
      have hub := not_not.mp hub
      obtain ⟨W, hW⟩ := ih.resolve_right <| not_not.mpr <|
        TCEmpty.isSubstring_trans (isSubstring_append_left u 1) hub
      obtain ⟨w₁, hw₁⟩ := h _ hub
      refine ⟨W ++ w₁, fun y hy ↦ ?_⟩
      rcases isSubstring_append_one_cases (TCEmpty.isTally_of_isSubstring hb hub) hy with
        hy | rfl
      · obtain ⟨w, hw, hθw⟩ := hW y hy
        exact ⟨w, TCEmpty.isSubstring_append_right_of hw w₁, hθw⟩
      · exact ⟨w₁, isSubstring_append_right W w₁, hw₁⟩
  exact (H b hb).resolve_right (not_not.mpr (IsSubstring.refl b))

/--
A $\Sigma_1$ relation universally quantified over the substrings of a tally is $\Sigma_1$ on the
tallies.
-/
lemma exists_prenexDefinable_ball {k : ℕ} {P : (Fin (k + 2) → V) → Prop}
    (hP : PrenexDefinable ℬₛ 𝚺 1 P) :
    ∃ Q : (Fin (k + 1) → V) → Prop, PrenexDefinable ℬₛ 𝚺 1 Q ∧
      ∀ u, IsTally 1 (u 0) → (Q u ↔ ∀ x, IsSubstring x (u 0) → P (x :> u)) := by
  have : Nonempty V := ⟨∅⟩
  obtain ⟨D, hD, H⟩ := PrenexDefinable.sigma_succ_iff.mp hP
  have hD := PrenexDefinable.zero_iff.mp hD
  have hM : 𝚺-[ℬₛ, 0].Definable fun z : Fin (k + 2) → V ↦
      ∀ x, IsSubstring x (z 1) → ∃ w, IsSubstring w (z 0) ∧ D (w :> x :> fun i ↦ z i.succ) := by
    apply ball_substring _ #1
    apply bexs_substring _ #1
    exact (hD.retraction (0 :> 1 :> fun i ↦ i.succ.succ.succ)).of_iff fun z ↦ by
      simp [Matrix.fun_vecCons_apply]
  refine ⟨_, PrenexDefinable.sigma_succ_iff.mpr ⟨_, PrenexDefinable.zero_iff.mpr hM,
    fun u ↦ Iff.rfl⟩, fun u hu ↦ ⟨?_, fun h ↦ ?_⟩⟩
  · rintro ⟨W, hW⟩ x hx
    obtain ⟨w, -, hw⟩ := hW x (by simpa using hx)
    exact (H _).mpr ⟨w, by simpa using hw⟩
  · obtain ⟨W, hW⟩ := collection (θ := fun x w ↦ D (w :> x :> u))
      ((hD.retractiont (#1 :> #0 :> fun i ↦ &(u i))).of_iff fun v ↦ by
        simp [Matrix.fun_vecCons_apply]) hu fun x hx ↦ (H _).mp (h x hx)
    exact ⟨W, fun x hx ↦ by simpa using hW x (by simpa using hx)⟩

end TCISigma

end notationInduction

end FFL.FirstOrder.Concatenation
