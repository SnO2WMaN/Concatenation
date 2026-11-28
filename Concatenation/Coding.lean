module

public import Concatenation.Biteral
public import Concatenation.ToFoundation.Coding
public import Concatenation.ToMathlib.Encodable
public import Foundation.FirstOrder.Incompleteness.Church

/-!
# Coding of the language of concatenation

The symbols of `ℒ⌢` are primitive-recursively coded and $\Delta_0$-definable in arithmetic, so
that Foundation's computability arguments on formulas apply to `ℒ⌢`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

namespace Language.Concatenation

instance : (ℒ⌢).Primcodable where
  func := by
    have h : Primrec fun p : ℕ × ℕ ↦
        if (p.1 = 0 ∧ p.2 < 2) ∨ (p.1 = 2 ∧ p.2 = 0) then p.2 + 1 else 0 := by
      primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    match k, e with
    |     0,     0 => rfl
    |     0,     1 => rfl
    |     0, _ + 2 => simp [Encodable.decode]
    |     1,     _ => simp [Encodable.decode]
    |     2,     0 => rfl
    |     2, _ + 1 => simp [Encodable.decode]
    | _ + 3,     _ => simp [Encodable.decode]
  rel := by
    have h : Primrec fun p : ℕ × ℕ ↦ if p.1 = 2 ∧ p.2 = 0 then 1 else 0 := by primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    match k, e with
    |     0,     _ => simp [Encodable.decode]
    |     1,     _ => simp [Encodable.decode]
    |     2,     0 => rfl
    |     2, _ + 1 => simp [Encodable.decode]
    | _ + 3,     _ => simp [Encodable.decode]

lemma mem_range_encode_func_iff {k f : ℕ} :
    f ∈ Set.range (Encodable.encode : (ℒ⌢).Func k → ℕ) ↔ (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨
    (k = 2 ∧ f = 0) := by
  constructor
  · rintro ⟨f, rfl⟩
    rcases f <;> simp <;> rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · use Func.zero; rfl
    · use Func.one; rfl
    · use Func.concat; rfl

lemma mem_range_encode_rel_iff {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : (ℒ⌢).Rel k → ℕ) ↔ k = 2 ∧ r = 0 := by
  constructor
  · rintro ⟨r, rfl⟩
    rcases r; simp; rfl
  · rintro ⟨rfl, rfl⟩
    use Rel.eq; rfl

instance : (ℒ⌢).LORDefinable where
  func := .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0)”
  rel := .mkSigma “k r. k = 2 ∧ r = 0”
  func_iff {k c} := by simpa [models_iff] using! mem_range_encode_func_iff
  rel_iff {k c} := by simpa [models_iff] using! mem_range_encode_rel_iff

end Language.Concatenation

namespace Language.ConcatenationLetters

instance {α : Type} [Primcodable α] : (ℒ⌢[α]).Primcodable where
  func := by
    have h : Primrec fun p : ℕ × ℕ ↦
        if p.1 = 0 then Encodable.encode (Encodable.decode p.2 : Option α)
        else if p.1 = 2 ∧ p.2 = 0 then 1 else 0 :=
      Primrec.ite (by primrec) (Primrec.encode.comp <| Primrec.decode.comp Primrec.snd)
        (by primrec)
    apply h.of_eq
    rintro ⟨k, e⟩
    match k, e with
    |     0,     e =>
      rcases h : (Encodable.decode e : Option α) with _ | a <;> simp [Encodable.decode, h]
      rfl
    |     1,     _ => simp [Encodable.decode]
    |     2,     0 => rfl
    |     2, _ + 1 => simp [Encodable.decode]
    | _ + 3,     _ => simp [Encodable.decode]
  rel := Language.Primcodable.rel (L := ℒ⌢)

lemma mem_range_encode_func_iff {n k f : ℕ} :
    f ∈ Set.range (Encodable.encode : (ℒ⌢[Fin n]).Func k → ℕ) ↔
      (k = 0 ∧ f < n) ∨ (k = 2 ∧ f = 0) := by
  constructor
  · rintro ⟨f, rfl⟩
    rcases f with a | _
    · exact .inl ⟨rfl, a.isLt⟩
    · exact .inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, rfl⟩)
    · use .letter ⟨f, h⟩; rfl
    · use .concat; rfl

instance {n : ℕ} : (ℒ⌢[Fin n]).LORDefinable where
  func := .mkSigma “k f. (k = 0 ∧ f < ↑n) ∨ (k = 2 ∧ f = 0)”
  rel := .mkSigma “k r. k = 2 ∧ r = 0”
  func_iff {k c} := by simpa [models_iff] using! mem_range_encode_func_iff
  rel_iff {k c} := by simpa [models_iff] using! Concatenation.mem_range_encode_rel_iff

end Language.ConcatenationLetters

namespace Language.PrefixRel

instance : prefixRel.Encodable where
  func _ := inferInstanceAs (Encodable Empty)
  rel _ := inferInstance

instance : prefixRel.Primcodable where
  func := by
    apply (Primrec.const 0 : Primrec fun _ : ℕ × ℕ ↦ 0).of_eq
    rintro ⟨k, e⟩
    simp [Encodable.decode]
  rel := by
    have h : Primrec fun p : ℕ × ℕ ↦ if p.1 = 2 ∧ p.2 = 0 then 1 else 0 := by primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    match k, e with
    |     0,     _ => rfl
    |     1,     _ => rfl
    |     2,     0 => rfl
    |     2, _ + 1 => simp [Encodable.decode]
    | _ + 3,     _ => simp [Encodable.decode]

end Language.PrefixRel

namespace Language

lemma concatenationEmpty.decode_func_two_mul (k m : ℕ) :
    (Encodable.decode (2 * m) : Option ((ℒ⌢ₑ).Func k)) =
      (Encodable.decode m : Option ((ℒ⌢).Func k)).map Sum.inl :=
  Encodable.decode_sum_two_mul (β := Constant.Func PUnit k) m

lemma concatenationEmpty.decode_func_two_mul_add_one (k m : ℕ) :
    (Encodable.decode (2 * m + 1) : Option ((ℒ⌢ₑ).Func k)) =
      (Encodable.decode m : Option (Constant.Func PUnit k)).map Sum.inr :=
  Encodable.decode_sum_two_mul_add_one (β := Constant.Func PUnit k) m

lemma concatenationEmpty.decode_rel_two_mul (k m : ℕ) :
    (Encodable.decode (2 * m) : Option ((ℒ⌢ₑ).Rel k)) =
      (Encodable.decode m : Option ((ℒ⌢).Rel k)).map Sum.inl :=
  Encodable.decode_sum_two_mul (β := PEmpty) m

lemma concatenationEmpty.decode_rel_two_mul_add_one (k m : ℕ) :
    (Encodable.decode (2 * m + 1) : Option ((ℒ⌢ₑ).Rel k)) = none :=
  Encodable.decode_sum_two_mul_add_one (β := PEmpty) m

open concatenationEmpty in
instance : (ℒ⌢ₑ).Primcodable where
  func := by
    have h : Primrec fun p : ℕ × ℕ ↦
        if (p.1 = 0 ∧ p.2 < 3) ∨ (p.1 = 2 ∧ p.2 = 0) then p.2 + 1 else 0 := by
      primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' e
    · simp only [decode_func_two_mul]
      match k, m with
      |     0,     0 => rfl
      |     0,     1 => rfl
      |     0, m + 2 => simp [Encodable.decode]; rfl
      |     1,     _ => simp [Encodable.decode]; rfl
      |     2,     0 => rfl
      |     2, _ + 1 => simp [Encodable.decode]; rfl
      | _ + 3,     _ => simp [Encodable.decode]; rfl
    · simp only [decode_func_two_mul_add_one]
      match k, m with
      |     0,     0 => rfl
      |     0, m + 1 => simp [Encodable.decode]; rfl
      | _ + 1,     _ => simp [Encodable.decode]; rfl
  rel := by
    have h : Primrec fun p : ℕ × ℕ ↦ if p.1 = 2 ∧ p.2 = 0 then 1 else 0 := by primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' e
    · simp only [decode_rel_two_mul]
      match k, m with
      |     0,     _ => simp [Encodable.decode]; rfl
      |     1,     _ => simp [Encodable.decode]; rfl
      |     2,     0 => rfl
      |     2, _ + 1 => simp [Encodable.decode]; rfl
      | _ + 3,     _ => simp [Encodable.decode]; rfl
    · simp [decode_rel_two_mul_add_one]

lemma concatenationEmpty.mem_range_encode_func_iff {k f : ℕ} :
    f ∈ Set.range (Encodable.encode : (ℒ⌢ₑ).Func k → ℕ) ↔ (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨
    (k = 0 ∧ f = 2) ∨ (k = 2 ∧ f = 0) := by
  constructor
  · rintro ⟨(_ | _ | _) | ⟨⟨⟩⟩, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩
    · exact Or.inr <| Or.inr <| Or.inr ⟨rfl, rfl⟩
    · exact Or.inr <| Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · use Sum.inl Concatenation.Func.zero; rfl
    · use Sum.inr <| Constant.Func.const ⟨⟩; rfl
    · use Sum.inl Concatenation.Func.one; rfl
    · use Sum.inl Concatenation.Func.concat; rfl

lemma concatenationEmpty.mem_range_encode_rel_iff {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : (ℒ⌢ₑ).Rel k → ℕ) ↔ k = 2 ∧ r = 0 := by
  constructor
  · rintro ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    use Sum.inl Concatenation.Rel.eq; rfl

instance : (ℒ⌢ₑ).LORDefinable where
  func := .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 0 ∧ f = 2) ∨ (k = 2 ∧ f = 0)”
  rel := .mkSigma “k r. k = 2 ∧ r = 0”
  func_iff {k c} := by
    simpa [models_iff] using! concatenationEmpty.mem_range_encode_func_iff
  rel_iff {k c} := by simpa [models_iff] using! concatenationEmpty.mem_range_encode_rel_iff

end Language

namespace Concatenation

/--
The closed term naming `n`: the letter $0$ for $n = 0$, the string of $n$ letters $1$ otherwise.
- [Gan09, §1, Definition 2]
-/
def numeralTerm : ℕ → ClosedSemiterm ℒ⌢ 0
  | 0 => ‘!!(op(0).const)’
  | 1 => ‘!!(op(1).const)’
  | n + 2 => ‘!!(numeralTerm (n + 1)) ⌢ !!(op(1).const)’

@[simp]
lemma numeralTerm_zero : numeralTerm 0 = ‘!!(op(0).const)’ := rfl

@[simp]
lemma numeralTerm_one : numeralTerm 1 = ‘!!(op(1).const)’ := rfl

@[simp]
lemma numeralTerm_add_two (n : ℕ) :
    numeralTerm (n + 2) = ‘!!(numeralTerm (n + 1)) ⌢ !!(op(1).const)’ := rfl

end Concatenation

end FFL.FirstOrder
