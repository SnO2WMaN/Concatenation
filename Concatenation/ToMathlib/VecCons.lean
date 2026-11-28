module

public import Mathlib.Data.Fin.VecNotation

/-!
# Composing with `Matrix.vecCons`

Precomposition with a vector built by `Matrix.vecCons`, in the lambda form `simp` meets.
-/

@[expose] public section

namespace Matrix

variable {α β : Type*} {n : ℕ}

lemma fun_vecCons_apply (g : β → α) (a : β) (f : Fin n → β) :
    (fun i ↦ g (vecCons a f i)) = vecCons (g a) fun i ↦ g (f i) :=
  funext fun i ↦ by cases i using Fin.cases <;> simp

end Matrix
