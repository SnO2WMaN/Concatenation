module

public import Concatenation.Coding
public import Concatenation.ToFoundation.Decidability
public import Concatenation.WTC.Basic
import Concatenation.OpenProblem

/-!
# An open problem on $\mathsf{WTC}$ with restricted schemata
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Concatenation

/--
Axioms of $\mathsf{WTC}$ where the schemata are restricted to the strings in `K`.
- [HH14, Definition 5]
-/
inductive IsWTCOnAxiom (K : Set (FreeSemigroup Bool)) : Sentence ℒ⌢ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢, IsWTCOnAxiom K φ
  | concatAssoc {u : FreeSemigroup Bool} : u ∈ K → IsWTCOnAxiom K
      “∀ x y z, !isSubstring ((x ⌢ y) ⌢ z) !!(biteral u) ∨
      !isSubstring (x ⌢ (y ⌢ z)) !!(biteral u) → (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | editor {u : FreeSemigroup Bool} : u ∈ K → IsWTCOnAxiom K
      “∀ x y s t, x ⌢ y = s ⌢ t ∧ !isSubstring (x ⌢ y) !!(biteral u) →
      (x = s ∧ y = t) ∨ ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”
  | concatNeZero : IsWTCOnAxiom K “∀ x y, x ⌢ y ≠ !!(op(0).const)”
  | concatNeOne : IsWTCOnAxiom K “∀ x y, x ⌢ y ≠ !!(op(1).const)”
  | zeroNeOne : IsWTCOnAxiom K “!!(op(0).const) ≠ !!(op(1).const)”

/--
$\mathsf{WTC}$ where the schemata are restricted to the strings in `K`.
- [HH14, Definition 5]
-/
abbrev WTCOn (K : Set (FreeSemigroup Bool)) : Theory ℒ⌢ := Set.ofPred (IsWTCOnAxiom K)

/--
For which sets of strings that contain the letters and are closed under substrings is the
restriction of $\mathsf{WTC}$, as axiomatized in the cited definition, to the instances of its
schemata for the strings in the set essentially undecidable?
- [HH14, Definition 5]
-/
open_problem essentiallyUndecidable_WTCOn (K : Set (FreeSemigroup Bool))
    (_ : ∀ b, FreeSemigroup.of b ∈ K) (_ : ∀ x y, x * y ∈ K → x ∈ K ∧ y ∈ K) :=
  (WTCOn K).EssentiallyUndecidable

end Concatenation

end FFL.FirstOrder
