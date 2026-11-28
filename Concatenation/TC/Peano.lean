module

public import Concatenation.TC.ISigma
public import Concatenation.TC.TallyArithmetic
public import Concatenation.ToFoundation.Arithmetic.Peano

/-!
# $\mathsf{TCI}$ and $\mathsf{PA}$ are mutually interpretable

The translation by the bijective binary numerals that interprets $\Sigma_n\text{-}\mathsf{TCI}$ in
$\mathsf{I}\Sigma_n$ does not depend on `n`, and every formula lies in some level of the bounded
hierarchy, so the same translation interprets $\mathsf{TCI}$ in $\mathsf{PA}$. Likewise the
translation by the tallies that interprets $\mathsf{I}\Sigma_{n+1}$ in
$\Sigma_{n+1}\text{-}\mathsf{TCI}$ does not depend on `n`, so it interprets $\mathsf{PA}$ in
$\mathsf{TCI}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/--
The bijective binary numerals of a model of $\mathsf{PA}$ form a model of $\mathsf{TCI}$.
- [Gan09, §1]
-/
instance {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    ((binaryTranslation 𝗣𝗔).Model V)↓[ℒ⌢ₑ] ⊧* 𝗧𝗖𝗜 := by
  rw [binaryTranslation.struc_eq]
  let := binaryTranslation.concatenationEmptyStructure 𝗣𝗔 V
  have append (x y : V) : binaryTranslation.equiv 𝗣𝗔 V (binaryAppend x y) =
      binaryTranslation.equiv 𝗣𝗔 V x ++ binaryTranslation.equiv 𝗣𝗔 V y := rfl
  constructor
  intro σ hσ
  cases hσ with
  | tcEmpty _ hσ =>
    exact (models_TCISigma (binaryTranslation.equiv 𝗣𝗔 V) rfl rfl rfl append 0).models_set
      (IsTCISigmaAxiom.tcEmpty _ hσ)
  | notationInduction φ =>
    obtain ⟨s, hφ⟩ := Bounding.Hierarchy.exists_level (substringBounding ℒ⌢ₑ) 𝚺 φ
    have : Nonempty ((binaryTranslation 𝗣𝗔).Model V) := ⟨∅⟩
    simpa [models_iff, Semiformula.eval_univCl] using fun ε ↦
      eval_notationInduction (binaryTranslation.equiv 𝗣𝗔 V) rfl rfl rfl append s hφ ε

/--
$\mathsf{PA}$ interprets $\mathsf{TCI}$ by the bijective binary numerals.
- [Gan09, §1]
-/
noncomputable instance binaryInterpretationPA : 𝗣𝗔 ⊳ 𝗧𝗖𝗜 where
  trln := binaryTranslation 𝗣𝗔
  interpret_theory _ hφ := Arithmetic.complete.{0} _ _ fun _ _ _ ↦
    DirectTranslation.models_translate_of_mem hφ

/--
$\mathsf{TCI}$ interprets $\mathsf{PA}$ by the tallies.
- [Gan09, §1]
-/
instance tallyInterpretationPA : 𝗧𝗖𝗜 ⊳ 𝗣𝗔 where
  trln := (tallyTranslation 0).ofWeakerThan
  interpret_theory _ hφ := completeEmpty.{0} _ _ fun V _ _ ↦ by
    have : Nonempty V := ⟨∅⟩
    have h (s : ℕ) : V↓[ℒ⌢ₑ] ⊧* TCISigma s := models_of_subtheory (U := 𝗧𝗖𝗜) inferInstance
    have : V↓[ℒ⌢ₑ] ⊧* TCISigma 1 := h 1
    have : (TallyNumber V)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_Peano_of_models_ISigma fun s ↦
      have : V↓[ℒ⌢ₑ] ⊧* TCISigma (s + 1) := h (s + 1)
      have := TallyNumber.models_ISigma (V := V) s
      mod_ISigma_of_le (Nat.le_succ s)
    have : TallyNumber V ≡ₑ[ℒₒᵣ] (tallyTranslation 0).Model V := by
      rw [tallyTranslation.struc_eq]
      exact Tarski.Structure.ElementaryEquiv.ofEquiv _
    have : ((tallyTranslation 0).Model V)↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
      (Tarski.Structure.ElementaryEquiv.modelsTheory (M₁ := TallyNumber V)).mp inferInstance
    simpa using DirectTranslation.models_translate_of_mem (τ := tallyTranslation 0) hφ

/--
$\mathsf{TCI}$ and $\mathsf{PA}$ are mutually interpretable.
- [Gan09, §1]
-/
noncomputable instance : 𝗧𝗖𝗜 ⋈ 𝗣𝗔 := ⟨tallyInterpretationPA, binaryInterpretationPA⟩

end FFL.FirstOrder.Concatenation
