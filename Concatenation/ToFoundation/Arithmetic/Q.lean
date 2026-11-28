module

public import Foundation.FirstOrder.Arithmetic.R0.Undecidability
public import Concatenation.ToFoundation.Interpretability.LocallyFinitelySatisfiable
public import Concatenation.ToMathlib.Infinite
public import Foundation.FirstOrder.Arithmetic.Q.Basic
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Robinson's arithmetic $\mathsf{Q}$

$\mathsf{Q}$ is finitely axiomatizable, has no finite models, and is essentially undecidable. The
interpretation of $\mathsf{I}\Sigma_0$ in $\mathsf{Q}$ is assumed as an axiom.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

namespace RobinsonQ

lemma finite : (𝗤 : ArithmeticTheory).Finite := by
  apply ((Theory.Eq.finite (L := ℒₒᵣ)).union
    (Set.toFinite {_, _, _, _, _, _, _, _})).subset fun σ hσ ↦ by
    cases hσ with
    | equal _ h => exact .inl h
    | succNeZero => exact .inr <| .inl rfl
    | succInj => exact .inr <| .inr <| .inl rfl
    | zeroOrSucc => exact .inr <| .inr <| .inr <| .inl rfl
    | addZero => exact .inr <| .inr <| .inr <| .inr <| .inl rfl
    | addSucc => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
    | mulZero => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
    | mulSucc => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
    | ltDef => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr rfl

lemma finiteAxiomatizable : FiniteAxiomatizable 𝗤 := .of_finite finite

lemma infinite_of_models (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗤] : Infinite V :=
  .of_injective_of_forall_ne (f := (· + (1 : V))) (fun _ _ ↦ succ_inj) Arithmetic.succ_ne_zero

/--
$\mathsf{Q}$ has no finite models.
- [Hor11, §3, Proposition 3.2]
-/
theorem not_hasFiniteModel : ¬(𝗤 : ArithmeticTheory).HasFiniteModel := by
  intro h
  obtain ⟨V, _, hfin, _, _, hV⟩ := h.exists_eq
  obtain ⟨W, _, _, _, s, _, hW⟩ : ∃ (W : Type) (_ : Nonempty W) (_ : Finite W)
      (_ : ORingStructure W) (_ : Tarski.Structure ℒₒᵣ W) (_ : Tarski.Structure.ORing ℒₒᵣ W),
      W↓[ℒₒᵣ] ⊧* 𝗤 :=
    let e := Tarski.Structure.Model.equiv ℒₒᵣ V
    let s : Tarski.Structure ℒₒᵣ (Tarski.Structure.Model ℒₒᵣ V) := Tarski.Structure.ofEquiv e
    ⟨Tarski.Structure.Model ℒₒᵣ V, inferInstance, .of_equiv V e, inferInstance, s,
      inferInstance,
      (Tarski.Structure.Model.elementaryEquiv ℒₒᵣ V).modelsTheory.mp hV⟩
  rcases standardModel_unique W s
  exact not_finite_iff_infinite.mpr (infinite_of_models W) inferInstance

end RobinsonQ

/--
$\mathsf{Q}$ is essentially undecidable.
- [Sve08, §2]
-/
instance : Entailment.EssentiallyUndecidable (𝗤 : ArithmeticTheory) fun _ ↦ True :=
  Entailment.EssentiallyUndecidable.of_weakerThan 𝗥₀ 𝗤

/--
$\mathsf{Q}$ interprets $\mathsf{I}\Sigma_0$.
- [HP98, Theorem V.5.7]
-/
axiom ISigma0.interpretationInQ : 𝗤 ⊳ 𝗜𝚺₀

end FFL.FirstOrder.Arithmetic
