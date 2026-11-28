module

public import Concatenation.ToFoundation.Concat
public import Concatenation.ToFoundation.Language

/-!
# Language of the theory of concatenation
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Language

namespace Concatenation

inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | concat : Func 2

inductive Rel : ℕ → Type
  | eq : Rel 2

end Concatenation

/--
Language of the theory of concatenation: two letters $0$, $1$, and concatenation.
- [GZ08, §1]
- [Mur22, §1]
-/
@[reducible]
def concatenation : Language where
  Func := Concatenation.Func
  Rel := Concatenation.Rel

@[inherit_doc]
notation "ℒ⌢" => concatenation

namespace Concatenation

instance (k) : DecidableEq (Concatenation.Func k) := fun a b ↦ by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> {exact instDecidableFalse}

instance (k) : DecidableEq (Concatenation.Rel k) := fun a b ↦ by
  rcases a; rcases b; exact .isTrue rfl

instance (k) : Encodable (Concatenation.Func k) where
  encode
    | .zero => 0
    | .one => 1
    | .concat => 0
  decode e :=
    match k, e with
    | 0, 0 => some .zero
    | 0, 1 => some .one
    | 2, 0 => some .concat
    | _, _ => none
  encodek x := by rcases x <;> simp

instance (k) : Encodable (Concatenation.Rel k) where
  encode
    | .eq => 0
  decode e :=
    match k, e with
    | 2, 0 => some .eq
    | _, _ => none
  encodek x := by rcases x; simp

instance : (ℒ⌢).Finite where
  func := ⟨{⟨0, .zero⟩, ⟨0, .one⟩, ⟨2, .concat⟩}, by rintro ⟨_, _ | _ | _⟩ <;> simp⟩
  rel := ⟨{⟨2, .eq⟩}, by rintro ⟨_, _ | _⟩; simp⟩

instance : (ℒ⌢).Zero := ⟨Func.zero⟩

instance : (ℒ⌢).One := ⟨Func.one⟩

instance : (ℒ⌢).Concat := ⟨Func.concat⟩

instance : (ℒ⌢).Eq := ⟨Rel.eq⟩

end Concatenation

/-- The letters `α` and the symbol for concatenation. -/
inductive ConcatenationLettersFunc (α : Type) : ℕ → Type
  | letter (a : α) : ConcatenationLettersFunc α 0
  | concat : ConcatenationLettersFunc α 2

/--
Language of the theory of concatenation with the letters `α`.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
-/
@[reducible]
def concatenationLetters (α : Type) : Language where
  Func := ConcatenationLettersFunc α
  Rel := Concatenation.Rel

@[inherit_doc]
notation "ℒ⌢[" α "]" => concatenationLetters α

namespace ConcatenationLetters

variable {α : Type}

instance [Encodable α] (k) : Encodable (ConcatenationLettersFunc α k) where
  encode
    | .letter a => Encodable.encode a
    | .concat => 0
  decode e :=
    match k, e with
    | 0, e => (Encodable.decode e).map .letter
    | 2, 0 => some .concat
    | _, _ => none
  encodek x := by rcases x <;> simp

instance : (ℒ⌢[α]).Concat := ⟨.concat⟩

instance : (ℒ⌢[α]).Eq := ⟨Concatenation.Rel.eq⟩

end ConcatenationLetters

/-- The single symbol for the prefix relation. -/
inductive PrefixRel : ℕ → Type
  | pref : PrefixRel 2

/-- The language whose only symbol is the prefix relation. -/
@[reducible]
def prefixRel : Language where
  Func := fun _ ↦ Empty
  Rel := PrefixRel

namespace PrefixRel

instance (k) : DecidableEq (PrefixRel k) := fun a b ↦ by
  rcases a; rcases b; exact .isTrue rfl

instance (k) : Encodable (PrefixRel k) where
  encode
    | .pref => 0
  decode e :=
    match k, e with
    | 2, 0 => some .pref
    | _, _ => none
  encodek x := by rcases x; simp

end PrefixRel

/-- The single symbol for the successor of strings. -/
inductive SuccessorFunc : ℕ → Type
  | succ : SuccessorFunc 1

/--
Language of the theory of concatenation with the successor of strings.
- [Dam17, §1]
- [Dam17a, §1]
-/
abbrev concatenationSuccessor : Language := ℒ⌢.add <| Language.ofFunc SuccessorFunc

@[inherit_doc]
notation "ℒ⌢ₛ" => concatenationSuccessor

/--
Language of the theory of concatenation with the empty string, written `⋆` in formulas.
- [HH14, §2]
-/
abbrev concatenationEmpty : Language := ℒ⌢.add unit.{0}

@[inherit_doc]
notation "ℒ⌢ₑ" => concatenationEmpty

/--
Language of the theory of concatenation with the prefix relation.
- [Mur22, §2]
-/
abbrev concatenationPrefix : Language := ℒ⌢.add prefixRel

@[inherit_doc]
notation "ℒ⌢⊑" => concatenationPrefix

instance : (ℒ⌢⊑).Prefix := ⟨Sum.inr PrefixRel.pref⟩

/--
Language of the theory of concatenation with the empty string and a bounding relation.
- [KM21, §1.4]
-/
abbrev concatenationEmptyPrefix : Language := ℒ⌢ₑ.add prefixRel

@[inherit_doc]
notation "ℒ⌢ₑ⊑" => concatenationEmptyPrefix

instance : (ℒ⌢ₑ⊑).Prefix := ⟨Sum.inr PrefixRel.pref⟩

section

variable (k : ℕ)

instance : (ℒ⌢ₑ).Finite where
  func :=
    have : DecidableEq ((k : ℕ) × (ℒ⌢ₑ).Func k) := inferInstance
    { elems := {⟨0, Sum.inl Concatenation.Func.zero⟩, ⟨0, Sum.inl Concatenation.Func.one⟩,
        ⟨2, Sum.inl Concatenation.Func.concat⟩, ⟨0, Sum.inr <| Constant.Func.const ⟨⟩⟩}
      complete := by rintro ⟨_, (_ | _ | _) | ⟨⟨⟩⟩⟩ <;> simp }
  rel :=
    { elems := {⟨2, Sum.inl Concatenation.Rel.eq⟩}
      complete := by rintro ⟨_, (_ | _) | ⟨⟨⟩⟩⟩; simp }

end

end Language

abbrev ConcatenationTheory := Theory ℒ⌢

abbrev ConcatenationSentence := Sentence ℒ⌢

variable {ξ : Type*} {n : ℕ} [ToString ξ]

def Semiterm.toStringConcatenation : Semiterm ℒ⌢ ξ n → String
  | #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x => "a_{" ++ toString x ++ "}"
  | func Language.Zero.zero _ => "0"
  | func Language.One.one _ => "1"
  | func Language.Concat.concat v =>
    s!"({(v 0).toStringConcatenation} ⌢ {(v 1).toStringConcatenation})"

instance : Repr (Semiterm ℒ⌢ ξ n) := ⟨fun t _ ↦ t.toStringConcatenation⟩

instance : ToString (Semiterm ℒ⌢ ξ n) := ⟨fun t ↦ t.toStringConcatenation⟩

end FFL.FirstOrder
