module

public import Concatenation.Coding
public import Concatenation.Language
public import Concatenation.ToFoundation.AddCoding
public import Concatenation.ToFoundation.Decidability
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy
import Concatenation.OpenProblem

/-!
# Open problems on concatenation with bounded quantifiers

The structures $\mathfrak{B}$ and $\mathfrak{F}$ of the binary strings, with the empty one, whose
bounding relation is that of substrings and the comparison of lengths, and the one with the equality
of lengths.
-/

@[expose] public section

open scoped FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

/--
A purely existential formula.
- [KM21, §1.4]
-/
inductive Semiformula.Existential {L : Language} {ξ : Type*} :
    {n : ℕ} → Semiformula L ξ n → Prop
  | of_open {n : ℕ} {φ : Semiformula L ξ n} : φ.Open → Existential φ
  | and {n : ℕ} {φ ψ : Semiformula L ξ n} : Existential φ → Existential ψ → Existential (φ ⋏ ψ)
  | or {n : ℕ} {φ ψ : Semiformula L ξ n} : Existential φ → Existential ψ → Existential (φ ⋎ ψ)
  | exs {n : ℕ} {φ : Semiformula L ξ (n + 1)} : Existential φ → Existential (∃¹ φ)

namespace Concatenation

/--
The structure of the binary strings with concatenation, where `R` interprets the bounding relation.
- [KM21, §1.5]
-/
def bitStructure (R : List Bool → List Bool → Prop) : Tarski.Struc ℒ⌢ₑ⊑ where
  Dom := List Bool
  nonempty := inferInstance
  struc :=
    { func := fun _ f v ↦ match f with
        | .inl (.inl .zero) => [false]
        | .inl (.inl .one) => [true]
        | .inl (.inl .concat) => v 0 ++ v 1
        | .inl (.inr _) => []
      rel := fun _ r v ↦ match r with
        | .inl (.inl .eq) => v 0 = v 1
        | .inr .pref => R (v 0) (v 1) }

/--
The structure $\mathfrak{B}$, whose bounding relation is that of substrings.
- [KM21, §1.5]
-/
abbrev bitStructureInfix : Tarski.Struc ℒ⌢ₑ⊑ := bitStructure fun x y ↦ x <:+: y

/--
The structure $\mathfrak{F}$, whose bounding relation is the comparison of lengths.
- [KM21, §1.5]
-/
abbrev bitStructureLength : Tarski.Struc ℒ⌢ₑ⊑ := bitStructure fun x y ↦ x.length ≤ y.length

/--
Is the fragment $\exists^{\mathfrak{B}}$ of the purely existential sentences true in $\mathfrak{B}$
decidable?
- [KM21, Problem 1]
- [Mur23, Problem 55]
-/
open_problem existential_infix_decidable :=
  ComputablePred fun σ : Sentence ℒ⌢ₑ⊑ ↦ σ.Existential ∧ bitStructureInfix ⊧ σ

/--
Is the fragment $\exists^{\mathfrak{F}}$ of the purely existential sentences true in $\mathfrak{F}$
decidable?
- [KM21, Problem 2]
- [Mur23, Problem 56]
-/
open_problem existential_length_decidable :=
  ComputablePred fun σ : Sentence ℒ⌢ₑ⊑ ↦ σ.Existential ∧ bitStructureLength ⊧ σ

/--
The structure of the binary strings whose bounding relation is the equality of lengths.
- [Mur21, §5.2]
-/
abbrev bitStructureEqLength : Tarski.Struc ℒ⌢ₑ⊑ := bitStructure fun x y ↦ x.length = y.length

/--
Is the truth of the existential sentences on the binary strings with concatenation and the equality
of lengths, that is, the satisfiability of word equations with length constraints, decidable?
- [Mur21, §5.2]
- [DGHMN18, §1]
- [Cio24, §2]
- [Mur23, §1.1]
-/
open_problem existential_eqLength_decidable :=
  ComputablePred fun σ : Sentence ℒ⌢ₑ⊑ ↦ σ.Existential ∧ bitStructureEqLength ⊧ σ

/--
The $\Sigma$ formulas: universal quantifiers are bounded.
- [KM21, §1.4]
-/
abbrev IsSigma {ξ : Type*} {n : ℕ} (φ : Semiformula ℒ⌢ₑ⊑ ξ n) : Prop :=
  Bounding.Hierarchy ⟨{Semiformula.Operator.Prefix.pref}⟩ 𝚺 1 φ

/--
Is there no finite set of purely universal sentences true in $\mathfrak{F}$ which is
$\Sigma$-complete with respect to $\mathfrak{F}$?
- [KM21, Conjecture 1]
- [Mur23, Conjecture 42]
-/
open_problem no_finite_open_sigmaComplete_length :=
  ¬∃ T : Theory ℒ⌢ₑ⊑, T.Finite ∧
    (∀ σ ∈ T, ∃ (n : ℕ) (φ : Semisentence ℒ⌢ₑ⊑ n), φ.Open ∧ σ = ∀¹* φ) ∧
    bitStructureLength ⊧* T ∧
    ∀ σ : Sentence ℒ⌢ₑ⊑, IsSigma σ → bitStructureLength ⊧ σ → 𝗘𝗤 ℒ⌢ₑ⊑ ∪ T ⊢ σ

end Concatenation

end FFL.FirstOrder
