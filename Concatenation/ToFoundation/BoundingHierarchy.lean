module

public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy

/-!
# Every formula lies in the bounded hierarchy

Every formula is $\Sigma_s$ and $\Pi_s$ for some `s`, whatever the bounding.
-/

@[expose] public section

namespace FFL.FirstOrder.Bounding.Hierarchy

variable {L : Language} {ξ : Type*} (ℬ : Bounding L)

lemma exists_level (Γ : Polarity) {n : ℕ} (φ : Semiformula L ξ n) : ∃ s, ℬ.Hierarchy Γ s φ := by
  induction φ using Semiformula.rec' generalizing Γ with
  | hverum => exact ⟨0, by simp⟩
  | hfalsum => exact ⟨0, by simp⟩
  | hrel r v => exact ⟨0, by simp⟩
  | hnrel r v => exact ⟨0, by simp⟩
  | hand φ ψ ihφ ihψ =>
    obtain ⟨s, hφ⟩ := ihφ Γ
    obtain ⟨t, hψ⟩ := ihψ Γ
    exact ⟨max s t, .and (hφ.mono <| le_max_left s t) (hψ.mono <| le_max_right s t)⟩
  | hor φ ψ ihφ ihψ =>
    obtain ⟨s, hφ⟩ := ihφ Γ
    obtain ⟨t, hψ⟩ := ihψ Γ
    exact ⟨max s t, .or (hφ.mono <| le_max_left s t) (hψ.mono <| le_max_right s t)⟩
  | hall φ ih =>
    obtain ⟨s, h⟩ := ih 𝚺
    exact ⟨s + 1 + 1, h.pi.accum Γ⟩
  | hexs φ ih =>
    obtain ⟨s, h⟩ := ih 𝚷
    exact ⟨s + 1 + 1, h.sigma.accum Γ⟩

end FFL.FirstOrder.Bounding.Hierarchy
