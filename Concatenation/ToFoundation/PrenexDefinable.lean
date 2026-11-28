module

public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Basic

/-!
# Definability by prenex formulas over a bounding

Relations defined, with parameters, by prenex formulas whose matrix is bounded by `ℬ`.
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding

open scoped Bounding

variable {L : Language} {ℬ : Bounding L} {V : Type*} [Tarski.Structure L V]
  {Γ : Polarity} {s k l : ℕ} {P Q : (Fin k → V) → Prop}

/--
`P` is defined, with parameters, by a prenex formula of the class `Γ` and the level `s` whose
matrix is bounded by `ℬ`.
-/
def PrenexDefinable (ℬ : Bounding L) (Γ : Polarity) (s : ℕ) {k : ℕ} (P : (Fin k → V) → Prop) :
    Prop :=
  ∃ φ : ℬ.Prenex Γ s V k, IsDefinedByWithParam P φ.val

@[simp]
lemma hierarchy_emb_zero {ξ : Type*} (φ : 𝚺-[ℬ, 0].Semisentence k) :
    ℬ.Hierarchy Γ s (Rewriting.emb φ.val : Semiformula L ξ k) :=
  Hierarchy.of_zero (φ.sigma_prop.rew _)

@[simp]
lemma hierarchy_substs_zero {ξ : Type*} {m : ℕ} (φ : 𝚺-[ℬ, 0].Semiformula ξ k)
    (v : Fin k → Semiterm L ξ m) : ℬ.Hierarchy Γ s (φ.val ⇜ v) :=
  Hierarchy.of_zero (φ.sigma_prop.rew _)

lemma HierarchySymbol.Definable.not_zero (h : 𝚺-[ℬ, 0].Definable P) :
    𝚺-[ℬ, 0].Definable fun v ↦ ¬P v :=
  (HierarchySymbol.Definable.of_zero h (ℌ := 𝚷-[ℬ, 0])).notPi

namespace PrenexDefinable

lemma of_iff (h : ℬ.PrenexDefinable Γ s Q) (H : ∀ v, P v ↔ Q v) : ℬ.PrenexDefinable Γ s P := by
  rwa [show P = Q from funext fun v ↦ propext (H v)]

lemma sigma_succ_iff {P : (Fin k → V) → Prop} : ℬ.PrenexDefinable 𝚺 (s + 1) P ↔
    ∃ Q : (Fin (k + 1) → V) → Prop, ℬ.PrenexDefinable 𝚷 s Q ∧ ∀ v, P v ↔ ∃ x, Q (x :> v) := by
  constructor
  · rintro ⟨φ, h⟩
    exact ⟨_, ⟨φ.sigmaInv, fun _ ↦ Iff.rfl⟩, fun v ↦ (h v).symm.trans (φ.models_sigmaInv v)⟩
  · rintro ⟨Q, ⟨φ, h⟩, H⟩
    exact ⟨φ.sigma, fun v ↦ (φ.models_sigma v).trans <| by simp [h, H]⟩

lemma pi_succ_iff {P : (Fin k → V) → Prop} : ℬ.PrenexDefinable 𝚷 (s + 1) P ↔
    ∃ Q : (Fin (k + 1) → V) → Prop, ℬ.PrenexDefinable 𝚺 s Q ∧ ∀ v, P v ↔ ∀ x, Q (x :> v) := by
  constructor
  · rintro ⟨φ, h⟩
    exact ⟨_, ⟨φ.piInv, fun _ ↦ Iff.rfl⟩, fun v ↦ (h v).symm.trans (φ.models_piInv v)⟩
  · rintro ⟨Q, ⟨φ, h⟩, H⟩
    exact ⟨φ.pi, fun v ↦ (φ.models_pi v).trans <| by simp [h, H]⟩

lemma exs {Q : (Fin (k + 1) → V) → Prop} (h : ℬ.PrenexDefinable 𝚷 s Q) :
    ℬ.PrenexDefinable 𝚺 (s + 1) fun v ↦ ∃ x, Q (x :> v) :=
  sigma_succ_iff.mpr ⟨Q, h, fun _ ↦ Iff.rfl⟩

lemma all {Q : (Fin (k + 1) → V) → Prop} (h : ℬ.PrenexDefinable 𝚺 s Q) :
    ℬ.PrenexDefinable 𝚷 (s + 1) fun v ↦ ∀ x, Q (x :> v) :=
  pi_succ_iff.mpr ⟨Q, h, fun _ ↦ Iff.rfl⟩

lemma not (h : ℬ.PrenexDefinable Γ s P) : ℬ.PrenexDefinable Γ.alt s fun v ↦ ¬P v := by
  obtain ⟨φ, h⟩ := h
  exact ⟨∼φ, fun v ↦ by simp [h v]⟩

lemma retraction (h : ℬ.PrenexDefinable Γ s P) (f : Fin k → Fin l) :
    ℬ.PrenexDefinable Γ s fun v : Fin l → V ↦ P fun i ↦ v (f i) := by
  obtain ⟨φ, h⟩ := h
  exact ⟨φ.rew <| Rew.subst fun x ↦ #(f x), fun v ↦ by simp [← h, Function.comp_def]⟩

lemma retractiont (h : ℬ.PrenexDefinable Γ s P) (f : Fin k → Semiterm L V l) :
    ℬ.PrenexDefinable Γ s fun v : Fin l → V ↦ P fun i ↦ (f i).val v id := by
  obtain ⟨φ, h⟩ := h
  exact ⟨φ.rew <| Rew.subst f, fun v ↦ by simp [← h, Function.comp_def]⟩

variable [Nonempty V]

lemma of_delta0 (h : 𝚺-[ℬ, 0].Definable P) : ℬ.PrenexDefinable Γ s P := by
  obtain ⟨φ, h⟩ := h
  have hφ : ℬ.Closure φ.val := Hierarchy.zero_iff_bounded.mp φ.sigma_prop
  exact ⟨.ofΔ₀ ⟨φ.val, hφ⟩ Γ s, fun v ↦ (Prenex.models_ofΔ₀ _ v).trans (h v)⟩

lemma zero_iff : ℬ.PrenexDefinable Γ 0 P ↔ 𝚺-[ℬ, 0].Definable P := by
  constructor
  · rintro ⟨φ, h⟩
    exact .mkPolarity (Γ := 𝚺) φ.val (Hierarchy.zero_iff.mp φ.val_hierarchy) fun v ↦ (h v).symm
  · exact of_delta0

lemma and_delta0 (h : ℬ.PrenexDefinable Γ s P) (hQ : 𝚺-[ℬ, 0].Definable Q) :
    ℬ.PrenexDefinable Γ s fun v ↦ P v ∧ Q v := by
  induction s generalizing k Γ with
  | zero => exact zero_iff.mpr <| (zero_iff.mp h).and hQ
  | succ s ih =>
    rcases Γ
    · obtain ⟨R, hR, H⟩ := sigma_succ_iff.mp h
      exact sigma_succ_iff.mpr ⟨_, ih hR (hQ.retraction Fin.succ), fun v ↦ by simp [H]⟩
    · obtain ⟨R, hR, H⟩ := pi_succ_iff.mp h
      exact pi_succ_iff.mpr ⟨_, ih hR (hQ.retraction Fin.succ), fun v ↦ by simp [H, forall_and]⟩

lemma or_delta0 (h : ℬ.PrenexDefinable Γ s P) (hQ : 𝚺-[ℬ, 0].Definable Q) :
    ℬ.PrenexDefinable Γ s fun v ↦ P v ∨ Q v := by
  induction s generalizing k Γ with
  | zero => exact zero_iff.mpr <| (zero_iff.mp h).or hQ
  | succ s ih =>
    rcases Γ
    · obtain ⟨R, hR, H⟩ := sigma_succ_iff.mp h
      exact sigma_succ_iff.mpr ⟨_, ih hR (hQ.retraction Fin.succ), fun v ↦ by simp [H, exists_or]⟩
    · obtain ⟨R, hR, H⟩ := pi_succ_iff.mp h
      exact pi_succ_iff.mpr
        ⟨_, ih hR (hQ.retraction Fin.succ), fun v ↦ by simp [H, forall_or_right]⟩

/-- The parameters of a prenex definition can be read as free variables indexed by `ℕ`. -/
lemma exists_eval_iff (h : ℬ.PrenexDefinable Γ s P) :
    ∃ (e : ℕ → V) (φ : Semiformula L ℕ k), ℬ.PrenexHierarchy Γ s φ ∧ ∀ v, P v ↔ φ.Eval v e := by
  classical
  obtain ⟨φ, h⟩ := h
  have : Inhabited V := Classical.inhabited_of_nonempty'
  use φ.val.enumerateFVar, Rew.rewriteMap φ.val.idxOfFVar ▹ φ.val
  and_intros
  · exact (PrenexHierarchy.rew _ φ.val_prenexHierarchy)
  · intro v
    simp [Semiformula.eval_rewriteMap, h]

end PrenexDefinable

end FFL.FirstOrder.Bounding
