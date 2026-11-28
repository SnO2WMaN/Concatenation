module

public import Concatenation.ToFoundation.BoundingHierarchy
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv

/-!
# The models of $\mathsf{PA}$

A structure is a model of $\mathsf{PA}$ as soon as it is a model of every $\mathsf{I}\Sigma_s$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

lemma models_Peano_of_models_ISigma {V : Type*} [ORingStructure V]
    (h : ∀ s, V↓[ℒₒᵣ] ⊧* 𝗜𝚺s) : V↓[ℒₒᵣ] ⊧* 𝗣𝗔 := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := h 0
  refine Semantics.ModelsSet.union_iff.mpr ⟨mod_paMinus_of_ISigma (s := 0), ?_⟩
  apply Semantics.modelsSet_iff.mpr
  rintro _ ⟨φ, -, rfl⟩
  obtain ⟨s, hφ⟩ := Bounding.Hierarchy.exists_level ℬ[<, ℒₒᵣ] 𝚺 φ
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := h s
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ s := inferInstance
  exact Semantics.modelsSet_iff.mp this (Or.inr ⟨φ, hφ, rfl⟩)

end FFL.FirstOrder.Arithmetic
