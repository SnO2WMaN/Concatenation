module

public import Concatenation.TC.Interpretability
public import Concatenation.ToFoundation.Arithmetic.Q
public import Concatenation.ToFoundation.Interpretability.DefinitionalEquivalence
public import Foundation.FirstOrder.Arithmetic.Schemata
import Concatenation.OpenProblem

/-!
# $\mathsf{TC}$ with and without the empty string

The two theories are mutually interpretable, hence both essentially undecidable, and even
definitionally equivalent, by a definable bijection between all strings and the nonempty strings.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation

section nonempty

variable {V : Type} [ConcatenationEmptyStructure V] {x : V}

/-- `x` is not the empty string. -/
def isNonempty : Semisentence ℒ⌢ₑ 1 := “x. x ≠ ⋆”

instance isNonempty_defined : ℒ⌢ₑ-predicate[V] (· ≠ ∅) via isNonempty :=
  ⟨fun v ↦ by simp [isNonempty]⟩

instance isNonempty_definable : ℒ⌢ₑ-predicate[V] (· ≠ ∅) := isNonempty_defined.to_definable

/--
In the models of `T`, the letters are not empty, and the nonempty strings are closed under
concatenation.
-/
class NonemptyClosed (T : Theory ℒ⌢ₑ) : Prop where
  zero_ne_empty (V : Type) [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* T] : (0 : V) ≠ ∅
  one_ne_empty (V : Type) [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* T] : (1 : V) ≠ ∅
  append_ne_empty (V : Type) [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* T] {x y : V}
    (hx : x ≠ ∅) : x ++ y ≠ ∅

instance : NonemptyClosed 𝗧𝗖ₑ where
  zero_ne_empty _ := TCEmpty.zero_ne_empty
  one_ne_empty _ := TCEmpty.one_ne_empty
  append_ne_empty _ _ _ _ _ hx h := hx (TCEmpty.eq_empty_of_append_eq_empty h).1

variable (T : Theory ℒ⌢ₑ) [𝗘𝗤 ℒ⌢ₑ ⪯ T] [NonemptyClosed T]

/--
The translation of the language without the empty string into a theory with the empty string,
relativized to the nonempty strings.
- [Vis09, Appendix A]
- [HH14, Theorem 3]
-/
def nonemptyTranslation : DirectTranslation T ℒ⌢ where
  domain := ⟨isNonempty⟩
  rel
    | Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Language.Concatenation.Func.zero => ⟨“z. z = !!(op(0).const)”⟩
    | Language.Concatenation.Func.one => ⟨“z. z = !!(op(1).const)”⟩
    | Language.Concatenation.Func.concat => ⟨“z x y. z = x ⌢ y”⟩
  domain_nonempty := completeEmpty.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simpa [Semiformula.Operator.val] using NonemptyClosed.zero_ne_empty T V
  func_defined f := completeEmpty.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : e i ≠ ∅ := by simpa [Semiformula.Operator.val] using he i
    cases f
    · suffices ∃! y : V, y ≠ ∅ ∧ y = 0 by simpa [Semiformula.Operator.val]
      use 0
      simpa using NonemptyClosed.zero_ne_empty T V
    · suffices ∃! y : V, y ≠ ∅ ∧ y = 1 by simpa [Semiformula.Operator.val]
      use 1
      simpa using NonemptyClosed.one_ne_empty T V
    · suffices ∃! y : V, y ≠ ∅ ∧ y = e 0 ++ e 1 by simpa [Semiformula.Operator.val]
      use e 0 ++ e 1
      simpa using NonemptyClosed.append_ne_empty (T := T) V (he 0)
  preserve_eq := completeEmpty.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace nonemptyTranslation

variable {T}

@[simp]
lemma dom_iff : (nonemptyTranslation T).Dom x ↔ x ≠ ∅ := by
  simp [DirectTranslation.dom_iff, nonemptyTranslation, Semiformula.Operator.val]

variable [V↓[ℒ⌢ₑ] ⊧* T]

variable (V T) in
/-- The letters and the concatenation of `V` restricted to the nonempty strings. -/
abbrev concatenationStructure : ConcatenationStructure ((nonemptyTranslation T).Model V) where
  zero := ⟨0, dom_iff.mpr <| NonemptyClosed.zero_ne_empty T V⟩
  one := ⟨1, dom_iff.mpr <| NonemptyClosed.one_ne_empty T V⟩
  append x y := ⟨x ++ y, dom_iff.mpr <|
    NonemptyClosed.append_ne_empty (T := T) V <| dom_iff.mp x.dom⟩

/--
The structure of the model of `nonemptyTranslation` is the standard one of the letters and the
concatenation restricted to the nonempty strings.
-/
lemma struc_eq :
    Model.struc (nonemptyTranslation T) V = @standardModel _ (concatenationStructure V T) :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      cases f <;> simp [nonemptyTranslation, Semiformula.Operator.val] <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

section

attribute [local instance] concatenationStructure

variable {x y : V} {hx : (nonemptyTranslation T).Dom x} {hy : (nonemptyTranslation T).Dom y}

@[simp]
lemma zero_eq_mk : (0 : (nonemptyTranslation T).Model V) =
    ⟨0, dom_iff.mpr <| NonemptyClosed.zero_ne_empty T V⟩ := rfl

@[simp]
lemma one_eq_mk : (1 : (nonemptyTranslation T).Model V) =
    ⟨1, dom_iff.mpr <| NonemptyClosed.one_ne_empty T V⟩ := rfl

@[simp]
lemma mk_append_mk : (⟨x, hx⟩ ++ ⟨y, hy⟩ : (nonemptyTranslation T).Model V) =
    ⟨x ++ y, dom_iff.mpr <| NonemptyClosed.append_ne_empty (T := T) V <| dom_iff.mp hx⟩ := rfl

end

end nonemptyTranslation

/--
The nonempty strings of a model of $\mathsf{TC}$ with the empty string form a model of
$\mathsf{TC}$.
- [Vis09, Appendix A]
-/
instance [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] : ((nonemptyTranslation 𝗧𝗖ₑ).Model V)↓[ℒ⌢] ⊧* 𝗧𝗖 := by
  rw [nonemptyTranslation.struc_eq]
  let := nonemptyTranslation.concatenationStructure V 𝗧𝗖ₑ
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case editor =>
    suffices ∀ x y z w : V, x ++ y = z ++ w → (x = z ∧ y = w) ∨
        ∃ u, u ≠ ∅ ∧ ((x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w)) by
      simpa [models_iff, Model.forall_iff, Model.exists_iff] using
        fun x _ y _ z _ w _ ↦ this x y z w
    intro x y z w h
    obtain ⟨u, hu⟩ := TCEmpty.editor h
    rcases eq_or_ne u ∅ with rfl | hu'
    · exact .inl <| by simpa using hu
    · exact .inr ⟨u, hu', hu⟩
  case zeroNeConcat =>
    simpa [models_iff, Model.forall_iff] using fun (x : V) (hx : x ≠ ∅) (y : V) (hy : y ≠ ∅)
      (h : 0 = x ++ y) ↦ (TCEmpty.eq_empty_of_append_isAtom <| by simp [← h]).elim hx hy
  case oneNeConcat =>
    simpa [models_iff, Model.forall_iff] using fun (x : V) (hx : x ≠ ∅) (y : V) (hy : y ≠ ∅)
      (h : 1 = x ++ y) ↦ (TCEmpty.eq_empty_of_append_isAtom <| by simp [← h]).elim hx hy
  all_goals simp [models_iff, Model.forall_iff, TCEmpty.append_assoc]

/--
$\mathsf{TC}$ with the empty string interprets $\mathsf{TC}$ on the nonempty strings.
- [Vis09, Appendix A]
- [HH14, Theorem 3]
-/
instance : 𝗧𝗖ₑ ⊳ 𝗧𝗖 where
  trln := nonemptyTranslation 𝗧𝗖ₑ
  interpret_theory _ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    DirectTranslation.models_translate_of_mem hφ

end nonempty

section option

open ConcatenationStructure ConcatenationEmptyStructure

variable {V : Type*} [ConcatenationStructure V] {x y : V}

/-- The strings of `V` together with an empty string. -/
instance : ConcatenationEmptyStructure (Option V) where
  zero := some 0
  one := some 1
  append := Option.merge (· ++ ·)
  emptyCollection := none

lemma Option.zero_eq_some : (0 : Option V) = some 0 := rfl

lemma Option.one_eq_some : (1 : Option V) = some 1 := rfl

lemma Option.empty_eq_none : (∅ : Option V) = none := rfl

@[simp]
lemma Option.none_append (x : Option V) : none ++ x = x := by cases x <;> rfl

@[simp]
lemma Option.append_none (x : Option V) : x ++ none = x := by cases x <;> rfl

@[simp]
lemma Option.some_append_some (x y : V) : (some x ++ some y : Option V) = some (x ++ y) := rfl

/-- The editor axiom passes to the strings of `V` together with an empty string. -/
lemma Option.editor {x y z w : Option V}
    (H : ∀ x y z w : V, x ++ y = z ++ w →
      (x = z ∧ y = w) ∨ ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w))
    (h : x ++ y = z ++ w) : ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) := by
  rcases x with _ | x <;> rcases z with _ | z
  · use none
    simpa using h
  · use some z
    exact Or.inl ⟨by simp, by simpa using h⟩
  · use some x
    exact Or.inr ⟨by simp, by simpa using h⟩
  rcases y with _ | y <;> rcases w with _ | w
  · use none
    simpa using h
  · use some w
    exact Or.inr ⟨by simpa using h, by simp⟩
  · use some y
    exact Or.inl ⟨by simpa using h, by simp⟩
  · rcases H _ _ _ _ (Option.some.inj h) with ⟨rfl, rfl⟩ | ⟨u, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
      [use none; use some u; use some u] <;> simp

lemma Option.ofList_cons (b : Bool) (l : List Bool) :
    (ofList (b :: l) : Option V) = some (ofFreeSemigroup ⟨b, l⟩) := by
  suffices ∀ (l : List Bool) (x : V),
      l.foldl (fun m b ↦ m ++ if b then 1 else 0) (some x) =
        some (l.foldl (fun m b ↦ m ++ if b then 1 else 0) x) by
    rw [ofFreeSemigroup, FreeSemigroup.stringValue, ← this]
    cases b <;> rfl
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    intro x
    rw [List.foldl_cons, List.foldl_cons, ← ih]
    cases b <;> rfl

@[simp]
lemma Option.not_isSubstring_none : ¬IsSubstring (some x) (none : Option V) := by
  rintro (h | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩ | ⟨u, v, h⟩)
  · simp at h
  · cases u <;> simp at h
  · cases v <;> simp at h
  all_goals cases u <;> cases v <;> simp at h

lemma Option.isSubstring_of_some (h : IsSubstring (some x) (some y)) : IsSubstring x y := by
  rcases h with h | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩ | ⟨u, v, h⟩
  · simp at h
    grind [IsSubstring]
  · cases u <;> simp at h <;> grind [IsSubstring]
  · cases v <;> simp at h <;> grind [IsSubstring]
  all_goals cases u <;> cases v <;> simp at h <;> grind [IsSubstring]

/--
The strings of a model of $\mathsf{TC}$ together with an empty string form a model of $\mathsf{TC}$
with the empty string.
- [Vis09, Appendix A]
-/
instance [V↓[ℒ⌢] ⊧* 𝗧𝗖] : (Option V)↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ := by
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case emptyConcat => simp [models_iff, Option.empty_eq_none]
  case concatEmpty => simp [models_iff, Option.empty_eq_none]
  case concatAssoc =>
    suffices ∀ x y z : Option V, x ++ y ++ z = x ++ (y ++ z) by simpa [models_iff]
    rintro (_ | x) (_ | y) (_ | z) <;> simp [Concatenation.append_assoc]
  case editor =>
    suffices ∀ x y z w : Option V, x ++ y = z ++ w →
        ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) by simpa [models_iff]
    exact fun _ _ _ _ ↦ Option.editor fun _ _ _ _ ↦ Concatenation.editor
  case zeroNeEmpty => simp [models_iff, Option.empty_eq_none, Option.zero_eq_some]
  case oneNeEmpty => simp [models_iff, Option.empty_eq_none, Option.one_eq_some]
  case zeroAtom =>
    suffices ∀ x y : Option V, x ++ y = 0 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    rintro (_ | x) (_ | y) h <;> simp_all [Option.empty_eq_none, Option.zero_eq_some]
  case oneAtom =>
    suffices ∀ x y : Option V, x ++ y = 1 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    rintro (_ | x) (_ | y) h <;> simp_all [Option.empty_eq_none, Option.one_eq_some]
  case zeroNeOne => simp [models_iff, Option.zero_eq_some, Option.one_eq_some]

end option

section code

variable {V : Type} [ConcatenationStructure V] {x y z : V}

/--
`x` is the letter $1$ or begins with it.
- [HH14, Theorem 3]
-/
def IsEmptyCode (x : V) : Prop := 1 ◨ x

/--
`x` is the letter $1$ or begins with it.
- [HH14, Theorem 3]
-/
def isEmptyCode : Semisentence ℒ⌢ 1 := “x. !isPrefix !!(op(1).const) x”

instance isEmptyCode_defined : ℒ⌢-predicate[V] IsEmptyCode via isEmptyCode :=
  ⟨fun v ↦ by simp [isEmptyCode, IsEmptyCode]⟩

instance isEmptyCode_definable : ℒ⌢-predicate[V] IsEmptyCode := isEmptyCode_defined.to_definable

/--
`z` is the code of the concatenation of the strings coded by `x` and `y`.
- [HH14, Theorem 3]
-/
def IsCodeAppend (z x y : V) : Prop :=
  (x = 1 ∧ z = y) ∨ (y = 1 ∧ z = x) ∨ ∃ u v, x = 1 ++ u ∧ y = 1 ++ v ∧ z = 1 ++ (u ++ v)

/--
`z` is the code of the concatenation of the strings coded by `x` and `y`.
- [HH14, Theorem 3]
-/
def isCodeAppend : Semisentence ℒ⌢ 3 :=
  “z x y. (x = !!(op(1).const) ∧ z = y) ∨ (y = !!(op(1).const) ∧ z = x) ∨
    ∃ u v, x = !!(op(1).const) ⌢ u ∧ y = !!(op(1).const) ⌢ v ∧ z = !!(op(1).const) ⌢ (u ⌢ v)”

instance isCodeAppend_defined : ℒ⌢-relation₃[V] IsCodeAppend via isCodeAppend :=
  ⟨fun v ↦ by simp [isCodeAppend, IsCodeAppend]⟩

instance isCodeAppend_definable : ℒ⌢-relation₃[V] IsCodeAppend := isCodeAppend_defined.to_definable

/-- The code of a string or of the empty string: the string itself after the letter $1$. -/
def emptyCode : Option V → V
  | none => 1
  | some x => 1 ++ x

@[simp]
lemma isEmptyCode_emptyCode (x : Option V) : IsEmptyCode (emptyCode x) := by
  cases x <;> simp [IsEmptyCode, emptyCode]

lemma isEmptyCode_iff : IsEmptyCode x ↔ ∃ y, emptyCode y = x := by
  constructor
  · rintro (rfl | ⟨y, rfl⟩)
    · exact ⟨none, rfl⟩
    · exact ⟨some y, rfl⟩
  · rintro ⟨y, rfl⟩
    simp

/--
In the models of `T`, the letter $1$ is not a concatenation, and can be cancelled on the left.
-/
class OneCancellable (T : Theory ℒ⌢) : Prop where
  append_ne_one (V : Type) [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* T] (x y : V) : x ++ y ≠ 1
  one_append_cancel (V : Type) [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* T] {x y : V}
    (h : 1 ++ x = 1 ++ y) : x = y

instance : OneCancellable 𝗧𝗖 where
  append_ne_one _ _ _ := Concatenation.append_ne_one
  one_append_cancel _ _ _ _ _ := isAtom_one.append_left_cancel

variable (T : Theory ℒ⌢) [OneCancellable T]

section

variable [V↓[ℒ⌢] ⊧* T]

include T

lemma emptyCode_injective : Function.Injective (emptyCode (V := V)) := by
  rintro (_ | x) (_ | y) h
  · rfl
  · exact (OneCancellable.append_ne_one T V 1 y h.symm).elim
  · exact (OneCancellable.append_ne_one T V 1 x h).elim
  · exact congrArg some <| OneCancellable.one_append_cancel T V h

lemma isCodeAppend_emptyCode_iff {x y : Option V} :
    IsCodeAppend z (emptyCode x) (emptyCode y) ↔ z = emptyCode (x ++ y) := by
  have h (x y : V) : 1 ++ x = 1 ++ y ↔ x = y :=
    ⟨OneCancellable.one_append_cancel T V, congrArg _⟩
  have h' (x : V) : 1 ≠ 1 ++ x := fun h ↦ OneCancellable.append_ne_one T V 1 x h.symm
  rcases x with _ | x <;> rcases y with _ | y <;>
    simp [IsCodeAppend, emptyCode, h, h', OneCancellable.append_ne_one T V]

end

variable [𝗘𝗤 ℒ⌢ ⪯ T]

/--
The translation of the language with the empty string into `T` that codes a string by the string
itself after the letter $1$, and the empty string by the letter $1$.
- [HH14, Theorem 3]
- [Vis09, Appendix A]
-/
def emptyTranslation : DirectTranslation T ℒ⌢ₑ where
  domain := ⟨isEmptyCode⟩
  rel
    | Sum.inl Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Sum.inl Language.Concatenation.Func.zero => ⟨“z. z = !!(op(1).const) ⌢ !!(op(0).const)”⟩
    | Sum.inl Language.Concatenation.Func.one => ⟨“z. z = !!(op(1).const) ⌢ !!(op(1).const)”⟩
    | Sum.inl Language.Concatenation.Func.concat => ⟨isCodeAppend⟩
    | Sum.inr (Language.Constant.Func.const _) => ⟨“z. z = !!(op(1).const)”⟩
  domain_nonempty := complete.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use emptyCode none
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : IsEmptyCode (e i) := by simpa [Semiformula.Operator.val] using he i
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · suffices ∃! y : V, IsEmptyCode y ∧ y = emptyCode (some 0) by
        simpa [Semiformula.Operator.val]
      use emptyCode (some 0)
      simp
    · suffices ∃! y : V, IsEmptyCode y ∧ y = emptyCode (some 1) by
        simpa [Semiformula.Operator.val]
      use emptyCode (some 1)
      simp
    · suffices ∃! y : V, IsEmptyCode y ∧ IsCodeAppend y (e 0) (e 1) by
        simpa [Semiformula.Operator.val]
      obtain ⟨x, hx⟩ := isEmptyCode_iff.mp (he 0)
      obtain ⟨y, hy⟩ := isEmptyCode_iff.mp (he 1)
      simp only [← hx, ← hy, isCodeAppend_emptyCode_iff T]
      use emptyCode (x ++ y)
      simp
    · suffices ∃! y : V, IsEmptyCode y ∧ y = emptyCode none by
        simpa [Semiformula.Operator.val]
      use emptyCode none
      simp
  preserve_eq := complete.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace emptyTranslation

variable {T}

@[simp]
lemma dom_iff : (emptyTranslation T).Dom x ↔ IsEmptyCode x := by
  simp [DirectTranslation.dom_iff, emptyTranslation, Semiformula.Operator.val]

variable [V↓[ℒ⌢] ⊧* T]

/-- The bijection of the strings of `V` and the empty string with their codes. -/
noncomputable def equiv : Option V ≃ (emptyTranslation T).Model V :=
  Equiv.ofBijective (fun x ↦ ⟨emptyCode x, by simp⟩) <| by
    constructor
    · exact fun x y h ↦ emptyCode_injective T <| congrArg Model.val h
    · intro x
      obtain ⟨y, hy⟩ := isEmptyCode_iff.mp <| dom_iff.mp x.dom
      exact ⟨y, Model.ext hy⟩

@[simp]
lemma val_equiv (x : Option V) : (equiv (T := T) x : V) = emptyCode x := rfl

lemma struc_eq :
    Model.struc (emptyTranslation T) V = Tarski.Structure.ofEquiv (equiv (T := T)) := by
  apply Tarski.Structure.ext
  · funext k f v
    symm
    apply Model.func_iff.mpr
    obtain ⟨v, rfl⟩ : ∃ w, v = equiv ∘ w := ⟨equiv.symm ∘ v, by simp [← Function.comp_assoc]⟩
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · simp [emptyTranslation, Semiformula.Operator.val]
      rfl
    · simp [emptyTranslation, Semiformula.Operator.val]
      rfl
    · simp only [emptyTranslation, Semiformula.Operator.val, Function.comp_apply]
      simp only [Defined.eval_iff]
      exact (isCodeAppend_emptyCode_iff T).mpr <| by
        change emptyCode (equiv.symm (equiv (v 0)) ++ equiv.symm (equiv (v 1))) = _
        simp
    · simp [emptyTranslation, Semiformula.Operator.val]
      rfl
  · funext k r v
    rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    exact propext <| (Model.eq_iff v).trans equiv.symm.apply_eq_iff_eq.symm

/--
The codes of the strings and of the empty string satisfy what the strings together with an empty
string satisfy.
-/
lemma models_of_option {U : Theory ℒ⌢ₑ} (h : (Option V)↓[ℒ⌢ₑ] ⊧* U) :
    ((emptyTranslation T).Model V)↓[ℒ⌢ₑ] ⊧* U := by
  have : Option V ≡ₑ[ℒ⌢ₑ] (emptyTranslation T).Model V := by
    rw [struc_eq]
    exact Tarski.Structure.ElementaryEquiv.ofEquiv equiv
  exact (Tarski.Structure.ElementaryEquiv.modelsTheory (M₁ := Option V)).mp h

end emptyTranslation

/--
The codes of the strings of a model of $\mathsf{TC}$ and of the empty string form a model of
$\mathsf{TC}$ with the empty string.
- [HH14, Theorem 3]
-/
instance [V↓[ℒ⌢] ⊧* 𝗧𝗖] : ((emptyTranslation 𝗧𝗖).Model V)↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ :=
  emptyTranslation.models_of_option inferInstance

/--
$\mathsf{TC}$ interprets $\mathsf{TC}$ with the empty string.
- [HH14, Theorem 3]
- [Vis09, Appendix A]
-/
instance : 𝗧𝗖 ⊳ 𝗧𝗖ₑ where
  trln := emptyTranslation 𝗧𝗖
  interpret_theory _ hφ := complete.{0} _ _ fun _ _ _ ↦ DirectTranslation.models_translate_of_mem hφ

/--
$\mathsf{TC}$ and $\mathsf{TC}$ with the empty string are mutually interpretable.
- [Vis09, Appendix A]
-/
instance : 𝗧𝗖 ⋈ 𝗧𝗖ₑ := ⟨inferInstance, inferInstance⟩

instance : Entailment.Consistent 𝗧𝗖ₑ := DirectInterpretation.consistent (inferInstance : 𝗧𝗖 ⊳ 𝗧𝗖ₑ)

/--
$\mathsf{TC}$ with the empty string is essentially undecidable.
- [Hor11, §2]
-/
instance : Entailment.EssentiallyUndecidable 𝗧𝗖ₑ fun _ ↦ True :=
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗧𝗖ₑ ⊳ 𝗧𝗖)

end code

section empty

variable {V : Type*} [ConcatenationEmptyStructure V] {x y z : V}

/-- Every nonempty suffix of `x` begins with the letter $0$. -/
def NonemptySuffixesBeginWithZero (x : V) : Prop := ∀ u v, x = u ++ v → v = ∅ ∨ ∃ w, v = 0 ++ w

/-- Every nonempty suffix of `x` begins with the letter $0$. -/
def nonemptySuffixesBeginWithZero : Semisentence ℒ⌢ₑ 1 :=
  “x. ∀ u v, x = u ⌢ v → v = ⋆ ∨ ∃ w, v = !!(op(0).const) ⌢ w”

instance nonemptySuffixesBeginWithZero_defined :
    ℒ⌢ₑ-predicate[V] NonemptySuffixesBeginWithZero via nonemptySuffixesBeginWithZero :=
  ⟨fun v ↦ by simp [nonemptySuffixesBeginWithZero, NonemptySuffixesBeginWithZero]⟩

instance nonemptySuffixesBeginWithZero_definable :
    ℒ⌢ₑ-predicate[V] NonemptySuffixesBeginWithZero :=
  nonemptySuffixesBeginWithZero_defined.to_definable

open Classical in
/--
The string `0 ++ x` if every nonempty suffix of `x` begins with the letter $0$, and `x` otherwise.
-/
noncomputable def shift (x : V) : V := if NonemptySuffixesBeginWithZero x then 0 ++ x else x

/-- `y` is `shift x`. -/
def isShift : Semisentence ℒ⌢ₑ 2 :=
  “y x. (!nonemptySuffixesBeginWithZero x ∧ y = !!(op(0).const) ⌢ x) ∨
    (¬!nonemptySuffixesBeginWithZero x ∧ y = x)”

instance shift_defined : ℒ⌢ₑ-function₁[V] shift via isShift := .mk fun v ↦ by
  by_cases h : NonemptySuffixesBeginWithZero (v 1) <;> simp [isShift, shift, h]

instance shift_definable : ℒ⌢ₑ-function₁[V] shift := shift_defined.to_definable

section map

variable {W : Type*} [ConcatenationEmptyStructure W] (g : V ≃ W) (zero : g 0 = 0)
    (append : ∀ x y, g (x ++ y) = g x ++ g y) (empty : g ∅ = ∅)

include zero append empty

lemma nonemptySuffixesBeginWithZero_map_iff :
    NonemptySuffixesBeginWithZero (g x) ↔ NonemptySuffixesBeginWithZero x := by
  simp [NonemptySuffixesBeginWithZero, g.surjective.forall, g.surjective.exists, ← zero,
    ← append, ← empty]

lemma shift_map (x : V) : shift (g x) = g (shift x) := by
  by_cases h : NonemptySuffixesBeginWithZero x <;>
    simp [shift, nonemptySuffixesBeginWithZero_map_iff g zero append empty, h, zero, append]

end map

section TCEmpty

variable [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ]

namespace TCEmpty

lemma zero_append_cancel (h : 0 ++ x = 0 ++ y) : x = y := by
  obtain ⟨u, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := editor h
  · simpa [eq_empty_of_append_eq_left isAtom_zero h₁] using h₂
  · simpa [eq_empty_of_append_eq_left isAtom_zero h₁.symm] using h₂

end TCEmpty

lemma nonemptySuffixesBeginWithZero_empty : NonemptySuffixesBeginWithZero (∅ : V) :=
  fun _ _ h ↦ Or.inl (TCEmpty.eq_empty_of_append_eq_empty h.symm).2

lemma nonemptySuffixesBeginWithZero_zero_append_iff :
    NonemptySuffixesBeginWithZero (0 ++ x) ↔ NonemptySuffixesBeginWithZero x := by
  constructor
  · exact fun h u v hx ↦ h (0 ++ u) v <| by rw [hx, TCEmpty.append_assoc]
  · intro h u v hx
    obtain ⟨w, ⟨-, hw⟩ | ⟨hw, rfl⟩⟩ := TCEmpty.editor hx
    · exact h w v hw
    · rcases TCEmpty.eq_empty_of_append_isAtom (hw ▸ isAtom_zero) with rfl | rfl
      · right
        use x
        simp [show w = 0 by simpa using hw.symm]
      · simpa using h ∅ x (by simp)

lemma shift_injective : Function.Injective (shift (V := V)) := by
  intro x y h
  by_cases hx : NonemptySuffixesBeginWithZero x <;>
    by_cases hy : NonemptySuffixesBeginWithZero y <;>
    simp only [shift, hx, hy, ite_true, ite_false] at h
  · exact TCEmpty.zero_append_cancel h
  · exact (hy <| h ▸ nonemptySuffixesBeginWithZero_zero_append_iff.mpr hx).elim
  · exact (hx <| h ▸ nonemptySuffixesBeginWithZero_zero_append_iff.mpr hy).elim
  · exact h

/-- The strings `shift x` are the nonempty strings. -/
lemma exists_shift_eq_iff : (∃ x, shift x = y) ↔ y ≠ ∅ := by
  constructor
  · rintro ⟨x, rfl⟩ h
    by_cases hx : NonemptySuffixesBeginWithZero x <;>
      simp only [shift, hx, ite_true, ite_false] at h
    · exact TCEmpty.zero_ne_empty (TCEmpty.eq_empty_of_append_eq_empty h).1
    · exact hx <| h ▸ nonemptySuffixesBeginWithZero_empty
  · intro hy
    by_cases h : NonemptySuffixesBeginWithZero y
    · obtain ⟨x, rfl⟩ := (h ∅ y (by simp)).resolve_left hy
      use x
      simp [shift, nonemptySuffixesBeginWithZero_zero_append_iff.mp h]
    · use y
      simp [shift, h]

@[simp]
lemma shift_ne_empty (x : V) : shift x ≠ ∅ := exists_shift_eq_iff.mp ⟨x, rfl⟩

lemma existsUnique_eq_shift (hy : y ≠ ∅) : ∃! x, y = shift x := by
  obtain ⟨x, rfl⟩ := exists_shift_eq_iff.mpr hy
  use x
  simp [shift_injective.eq_iff, eq_comm]

end TCEmpty

end empty

section shiftTranslation

variable {V : Type} [ConcatenationEmptyStructure V]

/--
The unrelativized translation of $\mathsf{TC}$ into $\mathsf{TC}$ with the empty string that reads
a string `x` as the nonempty string `shift x`.
-/
def shiftTranslation : DirectTranslation 𝗧𝗖ₑ ℒ⌢ where
  domain := ⟨⊤⟩
  rel
    | Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Language.Concatenation.Func.zero => ⟨“z. !isShift !!(op(0).const) z”⟩
    | Language.Concatenation.Func.one => ⟨“z. !isShift !!(op(1).const) z”⟩
    | Language.Concatenation.Func.concat =>
      ⟨“z x y. ∃ u v, !isShift u x ∧ !isShift v y ∧ !isShift (u ⌢ v) z”⟩
  domain_nonempty := completeEmpty.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    simp [Semiformula.Operator.val]
  func_defined f := completeEmpty.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    cases f
    · simpa [Semiformula.Operator.val] using existsUnique_eq_shift (V := V) TCEmpty.zero_ne_empty
    · simpa [Semiformula.Operator.val] using existsUnique_eq_shift (V := V) TCEmpty.one_ne_empty
    · simpa [Semiformula.Operator.val] using existsUnique_eq_shift
        (y := shift (e 0) ++ shift (e 1)) fun h ↦
          shift_ne_empty _ (TCEmpty.eq_empty_of_append_eq_empty h).1
  preserve_eq := completeEmpty.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace shiftTranslation

@[simp]
lemma dom {V : Type*} [Tarski.Structure ℒ⌢ₑ V] (x : V) : shiftTranslation.Dom x := by
  simp [DirectTranslation.dom_iff, shiftTranslation, Semiformula.Operator.val]

lemma func_zero_val_iff {e : Fin 1 → V} :
    (shiftTranslation.func Language.Concatenation.Func.zero).val e ↔ 0 = shift (e 0) := by
  simp [shiftTranslation, Semiformula.Operator.val]

lemma func_one_val_iff {e : Fin 1 → V} :
    (shiftTranslation.func Language.Concatenation.Func.one).val e ↔ 1 = shift (e 0) := by
  simp [shiftTranslation, Semiformula.Operator.val]

lemma func_concat_val_iff {e : Fin 3 → V} :
    (shiftTranslation.func Language.Concatenation.Func.concat).val e ↔
      shift (e 1) ++ shift (e 2) = shift (e 0) := by
  simp [shiftTranslation, Semiformula.Operator.val]

variable [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ]

/-- The bijection of the strings of `V` with the nonempty ones. -/
noncomputable def equiv : shiftTranslation.Model V ≃ (nonemptyTranslation 𝗧𝗖ₑ).Model V :=
  Equiv.ofBijective (fun x ↦ ⟨shift (x : V), by simp⟩) <| by
    constructor
    · exact fun x y h ↦ Model.ext <| shift_injective <| congrArg Model.val h
    · intro y
      obtain ⟨x, hx⟩ := exists_shift_eq_iff.mpr <| nonemptyTranslation.dom_iff.mp y.dom
      exact ⟨⟨x, dom x⟩, Model.ext hx⟩

@[simp]
lemma val_equiv (x : shiftTranslation.Model V) : (equiv x : V) = shift (x : V) := rfl

lemma shift_equiv_symm (y : (nonemptyTranslation 𝗧𝗖ₑ).Model V) :
    shift ((equiv.symm y : _) : V) = y := by
  rw [← val_equiv, Equiv.apply_symm_apply]

/-- The letters and the concatenation of the nonempty strings transported to all strings. -/
noncomputable abbrev concatenationStructure : ConcatenationStructure (shiftTranslation.Model V) :=
  let := nonemptyTranslation.concatenationStructure V 𝗧𝗖ₑ
  .ofEquiv equiv

lemma struc_eq :
    Model.struc shiftTranslation V = @standardModel _ concatenationStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      let := nonemptyTranslation.concatenationStructure V 𝗧𝗖ₑ
      symm
      apply Model.func_iff.mpr
      cases f
      · exact func_zero_val_iff.mpr (shift_equiv_symm 0).symm
      · exact func_one_val_iff.mpr (shift_equiv_symm 1).symm
      · exact func_concat_val_iff.mpr (shift_equiv_symm (equiv (v 0) ++ equiv (v 1))).symm)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

end shiftTranslation

/--
The strings of a model of $\mathsf{TC}$ with the empty string, read as its nonempty strings, form a
model of $\mathsf{TC}$.
-/
instance [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] : (shiftTranslation.Model V)↓[ℒ⌢] ⊧* 𝗧𝗖 := by
  have : (nonemptyTranslation 𝗧𝗖ₑ).Model V ≡ₑ[ℒ⌢] shiftTranslation.Model V := by
    rw [shiftTranslation.struc_eq,
      @standardModel_ofEquiv _ (nonemptyTranslation.concatenationStructure V 𝗧𝗖ₑ),
      ← nonemptyTranslation.struc_eq]
    exact Tarski.Structure.ElementaryEquiv.ofEquiv _
  exact (Tarski.Structure.ElementaryEquiv.modelsTheory
    (M₁ := (nonemptyTranslation 𝗧𝗖ₑ).Model V)).mp inferInstance

end shiftTranslation

section option

variable {V : Type*} [ConcatenationStructure V] {x y z : V}

/-- Every suffix of `x` begins with the letter $0$. -/
def SuffixesBeginWithZero (x : V) : Prop := ∀ y, x ◧ y → 0 ◨ y

/-- Every suffix of `x` begins with the letter $0$. -/
def suffixesBeginWithZero : Semisentence ℒ⌢ 1 :=
  “x. ∀ y, !isSuffix y x → !isPrefix !!(op(0).const) y”

instance suffixesBeginWithZero_defined :
    ℒ⌢-predicate[V] SuffixesBeginWithZero via suffixesBeginWithZero :=
  ⟨fun v ↦ by simp [suffixesBeginWithZero, SuffixesBeginWithZero]⟩

instance suffixesBeginWithZero_definable : ℒ⌢-predicate[V] SuffixesBeginWithZero :=
  suffixesBeginWithZero_defined.to_definable

lemma nonemptySuffixesBeginWithZero_some_iff :
    NonemptySuffixesBeginWithZero (some x) ↔ SuffixesBeginWithZero x := by
  have h (y : V) : (∃ w : Option V, some y = 0 ++ w) ↔ 0 ◨ y := by
    simp [Option.exists, Option.zero_eq_some, IsPrefix, eq_comm (a := y)]
  simp only [NonemptySuffixesBeginWithZero, SuffixesBeginWithZero, Option.forall, h,
    Option.empty_eq_none]
  simpa [IsSuffix, or_imp, forall_and] using fun _ ↦ forall_comm

open Classical in
/--
The letter $0$ for the empty string; for a string `x`, the string `0 ++ x` if every suffix of `x`
begins with the letter $0$, and `x` otherwise.
-/
noncomputable def shiftOption : Option V → V
  | none => 0
  | some x => if SuffixesBeginWithZero x then 0 ++ x else x

/-- `y` is `shiftOption (some x)`. -/
def isShiftSome : Semisentence ℒ⌢ 2 :=
  “y x. (!suffixesBeginWithZero x ∧ y = !!(op(0).const) ⌢ x) ∨
    (¬!suffixesBeginWithZero x ∧ y = x)”

instance shiftOption_some_defined :
    ℒ⌢-function₁[V] (fun x ↦ shiftOption (some x)) via isShiftSome := .mk fun v ↦ by
  by_cases h : SuffixesBeginWithZero (v 1) <;> simp [isShiftSome, shiftOption, h]

instance shiftOption_some_definable : ℒ⌢-function₁[V] (fun x ↦ shiftOption (some x)) :=
  shiftOption_some_defined.to_definable

/--
`z` corresponds under `shiftOption` to the concatenation of the strings corresponding to `x`
and `y`.
-/
def IsShiftAppend (z x y : V) : Prop :=
  (x = 0 ∧ z = y) ∨ (y = 0 ∧ z = x) ∨
    ∃ u v, x = shiftOption (some u) ∧ y = shiftOption (some v) ∧ z = shiftOption (some (u ++ v))

/--
`z` corresponds under `shiftOption` to the concatenation of the strings corresponding to `x`
and `y`.
-/
def isShiftAppend : Semisentence ℒ⌢ 3 :=
  “z x y. (x = !!(op(0).const) ∧ z = y) ∨ (y = !!(op(0).const) ∧ z = x) ∨
    ∃ u v, !isShiftSome x u ∧ !isShiftSome y v ∧ !isShiftSome z (u ⌢ v)”

instance isShiftAppend_defined : ℒ⌢-relation₃[V] IsShiftAppend via isShiftAppend :=
  ⟨fun v ↦ by simp [isShiftAppend, IsShiftAppend]⟩

instance isShiftAppend_definable : ℒ⌢-relation₃[V] IsShiftAppend :=
  isShiftAppend_defined.to_definable

variable [V↓[ℒ⌢] ⊧* 𝗧𝗖]

lemma some_shiftOption (x : Option V) : some (shiftOption x) = shift x := by
  rcases x with _ | x
  · rw [← Option.empty_eq_none, shift, ite_eq_left nonemptySuffixesBeginWithZero_empty]
    simp [Option.empty_eq_none, Option.zero_eq_some, shiftOption]
  · by_cases h : SuffixesBeginWithZero x <;>
      simp [shift, shiftOption, nonemptySuffixesBeginWithZero_some_iff, h, Option.zero_eq_some]

/-- The bijection of the strings of `V` and the empty string with the strings of `V`. -/
noncomputable def shiftOptionEquiv : Option V ≃ V :=
  Equiv.ofBijective shiftOption <| by
    constructor
    · intro x y h
      apply shift_injective
      rw [← some_shiftOption, h, some_shiftOption]
    · intro y
      obtain ⟨x, hx⟩ := exists_shift_eq_iff (y := some y).mpr <| by simp [Option.empty_eq_none]
      use x
      rwa [← some_shiftOption, Option.some_inj] at hx

@[simp]
lemma shiftOptionEquiv_apply (x : Option V) : shiftOptionEquiv x = shiftOption x := rfl

lemma shiftOption_inj {x y : Option V} : shiftOption x = shiftOption y ↔ x = y :=
  shiftOptionEquiv.apply_eq_iff_eq

lemma isShiftAppend_shiftOption_iff {x y : Option V} :
    IsShiftAppend z (shiftOption x) (shiftOption y) ↔ z = shiftOption (x ++ y) := by
  rcases x with _ | x <;> rcases y with _ | y <;>
    simp [IsShiftAppend, shiftOption_inj, show (0 : V) = shiftOption none from rfl]

end option

section emptyShiftTranslation

variable {V : Type} [ConcatenationStructure V]

/--
The unrelativized translation of $\mathsf{TC}$ with the empty string into $\mathsf{TC}$ that reads
the string `shiftOption x` as the string `x` or the empty string.
-/
def emptyShiftTranslation : DirectTranslation 𝗧𝗖 ℒ⌢ₑ where
  domain := ⟨⊤⟩
  rel
    | Sum.inl Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Sum.inl Language.Concatenation.Func.zero => ⟨“z. !isShiftSome z !!(op(0).const)”⟩
    | Sum.inl Language.Concatenation.Func.one => ⟨“z. !isShiftSome z !!(op(1).const)”⟩
    | Sum.inl Language.Concatenation.Func.concat => ⟨isShiftAppend⟩
    | Sum.inr (Language.Constant.Func.const _) => ⟨“z. z = !!(op(0).const)”⟩
  domain_nonempty := complete.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · simp [Semiformula.Operator.val]
    · simp [Semiformula.Operator.val]
    · obtain ⟨x, y, rfl⟩ : ∃ x y, e = ![x, y] := ⟨_, _, Matrix.fun_eq_vec_two _⟩
      obtain ⟨x, rfl⟩ := shiftOptionEquiv.surjective x
      obtain ⟨y, rfl⟩ := shiftOptionEquiv.surjective y
      simp [Semiformula.Operator.val, isShiftAppend_shiftOption_iff]
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
  preserve_eq := complete.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace emptyShiftTranslation

@[simp]
lemma dom {V : Type*} [Tarski.Structure ℒ⌢ V] (x : V) : emptyShiftTranslation.Dom x := by
  simp [DirectTranslation.dom_iff, emptyShiftTranslation, Semiformula.Operator.val]

lemma func_zero_val_iff {e : Fin 1 → V} :
    (emptyShiftTranslation.func (Sum.inl Language.Concatenation.Func.zero)).val e ↔
      e 0 = shiftOption (some 0) := by
  simp [emptyShiftTranslation, Semiformula.Operator.val]

lemma func_one_val_iff {e : Fin 1 → V} :
    (emptyShiftTranslation.func (Sum.inl Language.Concatenation.Func.one)).val e ↔
      e 0 = shiftOption (some 1) := by
  simp [emptyShiftTranslation, Semiformula.Operator.val]

lemma func_empty_val_iff {e : Fin 1 → V} :
    (emptyShiftTranslation.func (Sum.inr <| Language.Constant.Func.const ⟨⟩)).val e ↔ e 0 = 0 := by
  simp [emptyShiftTranslation, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

variable [V↓[ℒ⌢] ⊧* 𝗧𝗖]

/-- The bijection of the strings of `V` and the empty string with the strings of `V`. -/
noncomputable def equiv : Option V ≃ emptyShiftTranslation.Model V :=
  shiftOptionEquiv.trans
    { toFun x := ⟨x, dom x⟩
      invFun x := x }

@[simp]
lemma val_equiv (x : Option V) : (equiv x : V) = shiftOption x := rfl

/--
The letters, the concatenation and the empty string of `Option V` transported to the strings of `V`.
-/
noncomputable abbrev concatenationEmptyStructure :
    ConcatenationEmptyStructure (emptyShiftTranslation.Model V) := .ofEquiv equiv.symm

lemma struc_eq :
    Model.struc emptyShiftTranslation V = @standardModelEmpty _ concatenationEmptyStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      obtain ⟨v, rfl⟩ : ∃ w, v = equiv ∘ w := ⟨equiv.symm ∘ v, by simp [← Function.comp_assoc]⟩
      rcases f with (_ | _ | _) | ⟨⟨⟩⟩
      · exact func_zero_val_iff.mpr rfl
      · exact func_one_val_iff.mpr rfl
      · have h : equiv.symm (equiv (v 0)) ++ equiv.symm (equiv (v 1)) = v 0 ++ v 1 := by simp
        exact (Defined.eval_iff (φ := isShiftAppend) _).mpr <| isShiftAppend_shiftOption_iff.mpr <|
          congrArg shiftOption h
      · exact func_empty_val_iff.mpr rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext <| Model.eq_iff v)

end emptyShiftTranslation

/--
The strings of a model of $\mathsf{TC}$, read as its strings and the empty string, form a model of
$\mathsf{TC}$ with the empty string.
-/
instance [V↓[ℒ⌢] ⊧* 𝗧𝗖] : (emptyShiftTranslation.Model V)↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ := by
  have : Option V ≡ₑ[ℒ⌢ₑ] emptyShiftTranslation.Model V := by
    rw [emptyShiftTranslation.struc_eq, standardModelEmpty_ofEquiv]
    exact Tarski.Structure.ElementaryEquiv.ofEquiv _
  exact (Tarski.Structure.ElementaryEquiv.modelsTheory (M₁ := Option V)).mp inferInstance

end emptyShiftTranslation

/--
The interpretation of $\mathsf{TC}$ in $\mathsf{TC}$ with the empty string by `shiftTranslation`.
-/
abbrev shiftInterpretation : 𝗧𝗖ₑ ⊳ 𝗧𝗖 where
  trln := shiftTranslation
  interpret_theory _ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    DirectTranslation.models_translate_of_mem hφ

/--
The interpretation of $\mathsf{TC}$ with the empty string in $\mathsf{TC}$ by
`emptyShiftTranslation`.
-/
abbrev emptyShiftInterpretation : 𝗧𝗖 ⊳ 𝗧𝗖ₑ where
  trln := emptyShiftTranslation
  interpret_theory _ hφ := complete.{0} _ _ fun _ _ _ ↦ DirectTranslation.models_translate_of_mem hφ

section

variable {V : Type} [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* 𝗧𝗖]

lemma emptyShiftTranslation.shift_eq (x : emptyShiftTranslation.Model V) :
    @shift _ concatenationEmptyStructure x = equiv (some (x : V)) := by
  let := concatenationEmptyStructure (V := V)
  obtain ⟨x, rfl⟩ := equiv.surjective x
  rw [shift_map equiv (rfl : equiv (0 : Option V) = 0) (fun x y ↦ ?_) (rfl : equiv ∅ = ∅),
    ← some_shiftOption, val_equiv]
  change _ = equiv (equiv.symm (equiv x) ++ equiv.symm (equiv y))
  simp

end

section

variable {V : Type} [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ]

namespace shiftTranslation

/--
The bijection of the strings of the model of `shiftTranslation` and the empty string with the
strings of `V`.
-/
noncomputable def optionEquiv : Option (shiftTranslation.Model V) ≃ V :=
  Equiv.ofBijective (fun x ↦ x.elim ∅ fun x ↦ shift (x : V)) <| by
    constructor
    · rintro (_ | x) (_ | y) h
      · rfl
      · exact (shift_ne_empty _ h.symm).elim
      · exact (shift_ne_empty _ h).elim
      · exact congrArg some <| Model.ext <| shift_injective h
    · intro y
      rcases Classical.em (y = ∅) with rfl | h
      · exact ⟨none, rfl⟩
      · obtain ⟨x, hx⟩ := exists_shift_eq_iff.mpr h
        exact ⟨some ⟨x, dom x⟩, hx⟩

lemma optionEquiv_zero :
    let := concatenationStructure (V := V)
    optionEquiv (0 : Option (shiftTranslation.Model V)) = 0 :=
  shift_equiv_symm (nonemptyTranslation.concatenationStructure V 𝗧𝗖ₑ).toZero.zero

lemma optionEquiv_one :
    let := concatenationStructure (V := V)
    optionEquiv (1 : Option (shiftTranslation.Model V)) = 1 :=
  shift_equiv_symm (nonemptyTranslation.concatenationStructure V 𝗧𝗖ₑ).toOne.one

lemma optionEquiv_append (x y : Option (shiftTranslation.Model V)) :
    let := concatenationStructure (V := V)
    optionEquiv (x ++ y) = optionEquiv x ++ optionEquiv y := by
  rcases x with _ | x <;> rcases y with _ | y
  · exact (TCEmpty.empty_append _).symm
  · exact (TCEmpty.empty_append _).symm
  · exact (TCEmpty.append_empty _).symm
  · exact shift_equiv_symm <|
      (nonemptyTranslation.concatenationStructure V 𝗧𝗖ₑ).toAppend.append (equiv x) (equiv y)

lemma val_shiftOption_eq (x : Option (shiftTranslation.Model V)) :
    ((@shiftOption _ concatenationStructure x : shiftTranslation.Model V) : V) =
      optionEquiv x := by
  let := concatenationStructure (V := V)
  apply shift_injective
  have : (shiftTranslation.Model V)↓[ℒ⌢] ⊧* 𝗧𝗖 := by
    rw [← struc_eq]
    infer_instance
  rw [shift_map optionEquiv optionEquiv_zero optionEquiv_append rfl, ← some_shiftOption]
  rfl

end shiftTranslation

end

lemma emptyShiftTranslation.func_val_iff {V : Type} [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* 𝗧𝗖]
    {k} (f : (ℒ⌢).Func k) (e : Fin (k + 1) → emptyShiftTranslation.Model V) :
    (shiftTranslation.func f).val e ↔
      ((DirectTranslation.id 𝗧𝗖).func f).val fun i ↦ (e i : V) := by
  rw [id_func_val_iff, struc_eq]
  let := concatenationEmptyStructure (V := V)
  have h {x : V} {y z : emptyShiftTranslation.Model V} (hz : z = equiv (some x)) :
      z = shift y ↔ (y : V) = x := by
    simp [hz, shift_eq, eq_comm]
  cases f
  · exact shiftTranslation.func_zero_val_iff.trans <| h rfl
  · exact shiftTranslation.func_one_val_iff.trans <| h rfl
  · apply shiftTranslation.func_concat_val_iff.trans <| h _
    rw [shift_eq, shift_eq]
    have h (x y : V) :
        equiv.symm (equiv (some x)) ++ equiv.symm (equiv (some y)) = some (x ++ y) := by simp
    exact congrArg equiv <| h (e 1) (e 2)

lemma shiftTranslation.func_val_iff {V : Type} [ConcatenationEmptyStructure V]
    [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] {k} (f : (ℒ⌢ₑ).Func k) (e : Fin (k + 1) → shiftTranslation.Model V) :
    (emptyShiftTranslation.func f).val e ↔
      ((DirectTranslation.id 𝗧𝗖ₑ).func f).val fun i ↦ (e i : V) := by
  rw [id_func_val_iff]
  have : (shiftTranslation.Model V)↓[ℒ⌢] ⊧* 𝗧𝗖 := inferInstance
  rw [struc_eq] at this ⊢
  let := concatenationStructure (V := V)
  have h {x : shiftTranslation.Model V} {y : Option (shiftTranslation.Model V)} {z : V}
      (hz : optionEquiv y = z) : x = shiftOption y ↔ (x : V) = z := by
    rw [← hz, ← val_shiftOption_eq, Model.val_inj_iff]
  rcases f with (_ | _ | _) | ⟨⟨⟩⟩
  · exact emptyShiftTranslation.func_zero_val_iff.trans <| h optionEquiv_zero
  · exact emptyShiftTranslation.func_one_val_iff.trans <| h optionEquiv_one
  · obtain ⟨x, hx⟩ := shiftOptionEquiv.surjective (e 1)
    obtain ⟨y, hy⟩ := shiftOptionEquiv.surjective (e 2)
    apply (Defined.eval_iff (φ := isShiftAppend) _).trans
    rw [← hx, ← hy]
    apply isShiftAppend_shiftOption_iff.trans <| h _
    rw [optionEquiv_append, ← val_shiftOption_eq, ← val_shiftOption_eq]
    exact congrArg₂ (fun a b : shiftTranslation.Model V ↦ (a : V) ++ (b : V)) hx hy
  · exact emptyShiftTranslation.func_empty_val_iff.trans <| h (y := none) rfl

open DirectInterpretation in
/--
$\mathsf{TC}$ and $\mathsf{TC}$ with the empty string are definitionally equivalent.
- [Vis09, Appendix A]
-/
def TC.definitionalEquivalenceEmpty : DefinitionalEquivalence 𝗧𝗖 𝗧𝗖ₑ where
  r := emptyShiftInterpretation
  l := shiftInterpretation
  equivalent_id_left := {
    domain := complete.{0} _ _ fun V _ _ ↦ models_domainIff_iff.mpr fun x ↦ iff_of_true
      ((compDirectTranslation_Dom_iff shiftTranslation emptyShiftInterpretation).mpr
        ⟨⟨⟨x, emptyShiftTranslation.dom x⟩, shiftTranslation.dom _⟩, rfl⟩) (id_Dom x)
    rel R := complete.{0} _ _ fun V _ _ ↦ models_operatorIff_iff.mpr fun e _ ↦ by
      let e' (i) : emptyShiftTranslation.Model V := ⟨e i, emptyShiftTranslation.dom _⟩
      apply (translateOperator_val_iff emptyShiftInterpretation (shiftTranslation.rel R) e').trans
      apply Iff.trans _ id_rel_val_iff.symm
      cases R
      change Semiformula.Evalb e' “x y. x = y” ↔ e 0 = e 1
      simp [e']
    func f := complete.{0} _ _ fun V _ _ ↦ models_operatorIff_iff.mpr fun e _ ↦
      let e' (i) : emptyShiftTranslation.Model V := ⟨e i, emptyShiftTranslation.dom _⟩
      (translateOperator_val_iff emptyShiftInterpretation _ e').trans <|
        emptyShiftTranslation.func_val_iff f e' }
  equivalent_id_right := {
    domain := completeEmpty.{0} _ _ fun V _ _ ↦ models_domainIff_iff.mpr fun x ↦ iff_of_true
      ((compDirectTranslation_Dom_iff emptyShiftTranslation shiftInterpretation).mpr
        ⟨⟨⟨x, shiftTranslation.dom x⟩, emptyShiftTranslation.dom _⟩, rfl⟩) (id_Dom x)
    rel R := completeEmpty.{0} _ _ fun V _ _ ↦ models_operatorIff_iff.mpr fun e _ ↦ by
      let e' (i) : shiftTranslation.Model V := ⟨e i, shiftTranslation.dom _⟩
      apply (translateOperator_val_iff shiftInterpretation (emptyShiftTranslation.rel R) e').trans
      apply Iff.trans _ id_rel_val_iff.symm
      rcases R with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      change Semiformula.Evalb e' “x y. x = y” ↔ e 0 = e 1
      simp [e']
    func f := completeEmpty.{0} _ _ fun V _ _ ↦ models_operatorIff_iff.mpr fun e _ ↦
      let e' (i) : shiftTranslation.Model V := ⟨e i, shiftTranslation.dom _⟩
      (translateOperator_val_iff shiftInterpretation _ e').trans <|
        shiftTranslation.func_val_iff f e' }

section notationInduction

/--
The notation induction axiom for `φ`.
- [HH14, Question 3]
-/
def notationInduction {ξ : Type*} (φ : Semiformula ℒ⌢ₑ ξ 1) : Formula ℒ⌢ₑ ξ :=
  “!φ ⋆ → (∀ x, !φ x → !φ (x ⌢ !!(op(0).const)) ∧ !φ (x ⌢ !!(op(1).const))) → ∀ x, !φ x”

/--
Axioms of the theory $\Sigma_n\text{-}\mathsf{TCI}$.
- [HH14, Question 3]
-/
inductive IsTCISigmaAxiom (n : ℕ) : Sentence ℒ⌢ₑ → Prop
  | tcEmpty : ∀ φ ∈ 𝗧𝗖ₑ, IsTCISigmaAxiom n φ
  | notationInduction (φ : Semiformula ℒ⌢ₑ ℕ 1) : (substringBounding ℒ⌢ₑ).PrenexHierarchy 𝚺 n φ →
      IsTCISigmaAxiom n (notationInduction φ).univCl

/--
The theory $\Sigma_n\text{-}\mathsf{TCI}$: $\mathsf{TC}$ with the empty string and notation
induction for the $\Sigma_n$ formulas.
- [HH14, Question 3]
-/
abbrev TCISigma (n : ℕ) : Theory ℒ⌢ₑ := Set.ofPred (IsTCISigmaAxiom n)

instance (n : ℕ) : 𝗧𝗖ₑ ⪯ TCISigma n := Entailment.WeakerThan.ofSubset IsTCISigmaAxiom.tcEmpty

instance (n : ℕ) : 𝗘𝗤 ℒ⌢ₑ ⪯ TCISigma n :=
  Entailment.WeakerThan.trans (𝓣 := 𝗧𝗖ₑ) inferInstance inferInstance

/--
Are $\Sigma_n\text{-}\mathsf{TCI}$ and $\mathsf{I}\Sigma_n$ mutually interpretable for each $n$?
- [HH14, Question 3]
-/
open_problem TCISigma_mutuallyInterpretable_ISigma := ∀ n : ℕ, Nonempty (TCISigma n ⋈ 𝗜𝚺 n)

/--
$\Sigma_0\text{-}\mathsf{TCI}$ interprets $\mathsf{I}\Sigma_0$.
- [HH14, Question 3]
-/
noncomputable instance TCISigma.interpretationISigma0 : TCISigma 0 ⊳ 𝗜𝚺₀ :=
  Arithmetic.ISigma0.interpretationInQ.comp <| (inferInstance : 𝗧𝗖 ⊳ 𝗤).comp <|
    (inferInstance : 𝗧𝗖ₑ ⊳ 𝗧𝗖).comp <| DirectInterpretation.ofWeakerThan (TCISigma 0) 𝗧𝗖ₑ

end notationInduction

end FFL.FirstOrder.Concatenation
