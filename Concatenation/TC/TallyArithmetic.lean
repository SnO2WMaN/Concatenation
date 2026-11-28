module

public import Concatenation.TC.TallyMultiplication
public import Concatenation.ToMathlib.VecCons
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# $\Sigma_{n+1}\text{-}\mathsf{TCI}$ interprets $\mathsf{I}\Sigma_{n+1}$

The `1`-tallies of a model of $\Sigma_{n+1}\text{-}\mathsf{TCI}$, with concatenation as addition and
the multiplication of tallies, form a model of $\mathsf{I}\Sigma_{n+1}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open Bounding Arithmetic

section tallyNumber

variable (V : Type*) [ConcatenationEmptyStructure V]

/-- The `1`-tallies of `V`. -/
def TallyNumber : Type _ := {x : V // IsTally 1 x}

variable {V} [V↓[ℒ⌢ₑ] ⊧* TCISigma 1]

/--
The arithmetic of the `1`-tallies: `0` is the empty string, `1` is the letter `1`, the sum is the
concatenation, the product is the multiplication of tallies, and the order is the proper prefix
relation.
- [Gan09, §1, Definition 2]
-/
noncomputable instance : ORingStructure (TallyNumber V) where
  zero := ⟨∅, by simp⟩
  one := ⟨1, TCEmpty.isTally_one⟩
  add a b := ⟨a.1 ++ b.1, TCEmpty.isTally_append a.2 b.2⟩
  mul a b := ⟨(exists_isTallyMul a.2 b.2).choose, (exists_isTallyMul a.2 b.2).choose_spec.isTally⟩
  lt a b := IsProperPrefix a.1 b.1

namespace TallyNumber

variable {a b c : TallyNumber V}

omit [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] in
lemma ext_iff' : a = b ↔ a.1 = b.1 := Subtype.ext_iff

omit [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] in
lemma exists_iff {P : TallyNumber V → Prop} : (∃ a, P a) ↔ ∃ x, ∃ hx : IsTally 1 x, P ⟨x, hx⟩ :=
  Subtype.exists

omit [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] in
lemma forall_iff {P : TallyNumber V → Prop} : (∀ a, P a) ↔ ∀ x, ∀ hx : IsTally 1 x, P ⟨x, hx⟩ :=
  Subtype.forall

@[simp]
lemma val_zero : (0 : TallyNumber V).1 = ∅ := rfl

@[simp]
lemma val_one : (1 : TallyNumber V).1 = 1 := rfl

@[simp]
lemma val_add (a b : TallyNumber V) : (a + b).1 = a.1 ++ b.1 := rfl

lemma isTallyMul_val_mul (a b : TallyNumber V) : IsTallyMul a.1 b.1 (a * b).1 :=
  (exists_isTallyMul a.2 b.2).choose_spec

lemma val_mul_eq_iff {z : V} : (a * b).1 = z ↔ IsTallyMul a.1 b.1 z :=
  ⟨fun h ↦ h ▸ isTallyMul_val_mul a b, fun h ↦ (isTallyMul_val_mul a b).unique h⟩

lemma lt_iff : a < b ↔ IsProperPrefix a.1 b.1 := Iff.rfl

end TallyNumber

end tallyNumber

section definability

local notation "ℬₛ" => substringBounding ℒ⌢ₑ

variable {V : Type*} [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] {ξ : Type*} {k : ℕ}

/--
The graph of the value of an arithmetic term on the tallies has a $\Sigma_1$ definition.
- [Gan09, §1, Definition 2]
-/
lemma exists_termGraph (t : Semiterm ℒₒᵣ ξ k) (f : ξ → TallyNumber V) :
    ∃ G : (Fin (k + 1) → V) → Prop, PrenexDefinable ℬₛ 𝚺 1 G ∧
      ∀ (v : Fin k → TallyNumber V) (y : V), G (y :> fun i ↦ (v i).1) ↔ y = (t.val v f).1 := by
  have : Nonempty V := ⟨∅⟩
  induction t with
  | bvar i =>
    exact ⟨_, .of_delta0 (definable_eq_term #0 #i.succ), fun v y ↦ by simp⟩
  | fvar x =>
    exact ⟨_, .of_delta0 (definable_eq_term #0 &(f x).1), fun v y ↦ by simp⟩
  | func g ts ih =>
    cases g with
    | zero => exact ⟨_, .of_delta0 (definable_eq_term #0 ‘⋆’), fun v y ↦ by simp; rfl⟩
    | one => exact ⟨_, .of_delta0 (definable_eq_term #0 ‘!!(op(1).const)’), fun v y ↦ by simp; rfl⟩
    | add =>
      obtain ⟨G₁, hG₁, H₁⟩ := ih 0
      obtain ⟨G₂, hG₂, H₂⟩ := ih 1
      refine ⟨fun w ↦ ∃ y₁, ∃ y₂, G₁ (y₁ :> fun i ↦ w i.succ) ∧ G₂ (y₂ :> fun i ↦ w i.succ) ∧
        w 0 = y₁ ++ y₂, ?_, fun v y ↦ ?_⟩
      · refine (PrenexDefinable.exs_Sigma1 <| PrenexDefinable.exs_Sigma1 <|
          PrenexDefinable.and_Sigma1 (hG₁.retraction (1 :> fun i ↦ i.succ.succ.succ)) <|
            (hG₂.retraction (0 :> fun i ↦ i.succ.succ.succ)).and_delta0 <|
              definable_eq_term #2 ‘#1 ⌢ #0’).of_iff fun w ↦ ?_
        simp [Matrix.fun_vecCons_apply]
      · simp [H₁, H₂]
        rfl
    | mul =>
      obtain ⟨G₁, hG₁, H₁⟩ := ih 0
      obtain ⟨G₂, hG₂, H₂⟩ := ih 1
      refine ⟨fun w ↦ ∃ y₁, ∃ y₂, G₁ (y₁ :> fun i ↦ w i.succ) ∧ G₂ (y₂ :> fun i ↦ w i.succ) ∧
        IsTallyMul y₁ y₂ (w 0), ?_, fun v y ↦ ?_⟩
      · refine (PrenexDefinable.exs_Sigma1 <| PrenexDefinable.exs_Sigma1 <|
          PrenexDefinable.and_Sigma1 (hG₁.retraction (1 :> fun i ↦ i.succ.succ.succ)) <|
            PrenexDefinable.and_Sigma1 (hG₂.retraction (0 :> fun i ↦ i.succ.succ.succ)) <|
              prenexDefinable_isTallyMul.retraction ![1, 0, 2]).of_iff fun w ↦ ?_
        simp [Matrix.fun_vecCons_apply]
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, H₁, H₂]
        change _ ↔ y = ((ts 0).val v f * (ts 1).val v f).1
        constructor
        · rintro ⟨_, _, rfl, rfl, h⟩
          exact (TallyNumber.val_mul_eq_iff.mpr h).symm
        · rintro rfl
          exact ⟨_, _, rfl, rfl, TallyNumber.isTallyMul_val_mul _ _⟩

/-- A relation of three $\Sigma_1$ relations through the values of two terms. -/
private lemma exists_prenexDefinable_terms (t₁ t₂ : Semiterm ℒₒᵣ ξ k) (f : ξ → TallyNumber V)
    {R : V → V → Prop} (hR : PrenexDefinable ℬₛ 𝚺 1 fun v : Fin 2 → V ↦ R (v 0) (v 1)) :
    ∃ Q : (Fin k → V) → Prop, PrenexDefinable ℬₛ 𝚺 1 Q ∧ ∀ v : Fin k → TallyNumber V,
      (Q fun i ↦ (v i).1) ↔ R (t₁.val v f).1 (t₂.val v f).1 := by
  obtain ⟨G₁, hG₁, H₁⟩ := exists_termGraph t₁ f
  obtain ⟨G₂, hG₂, H₂⟩ := exists_termGraph t₂ f
  refine ⟨fun w ↦ ∃ y₁, ∃ y₂, G₁ (y₁ :> w) ∧ G₂ (y₂ :> w) ∧ R y₁ y₂, ?_, fun v ↦ ?_⟩
  · exact (PrenexDefinable.exs_Sigma1 <| PrenexDefinable.exs_Sigma1 <|
      PrenexDefinable.and_Sigma1 (hG₁.retraction (1 :> fun i ↦ i.succ.succ)) <|
        PrenexDefinable.and_Sigma1 (hG₂.retraction (0 :> fun i ↦ i.succ.succ)) <|
          hR.retraction ![1, 0]).of_iff fun w ↦ by simp [Matrix.fun_vecCons_apply]
  · simp [H₁, H₂]

/--
A bounded arithmetic formula is $\Sigma_1$ on the tallies.
- [HH14, Question 3]
-/
lemma exists_prenexDefinable_of_closure {φ : Semiformula ℒₒᵣ ξ k} (hφ : ℬ[<, ℒₒᵣ].Closure φ)
    (f : ξ → TallyNumber V) :
    ∃ Q : (Fin k → V) → Prop, PrenexDefinable ℬₛ 𝚺 1 Q ∧
      ∀ v : Fin k → TallyNumber V, (Q fun i ↦ (v i).1) ↔ φ.Eval v f := by
  have : Nonempty V := ⟨∅⟩
  induction hφ with
  | verum => exact ⟨fun _ ↦ True, .of_delta0 (by simp), by simp⟩
  | falsum => exact ⟨fun _ ↦ False, .of_delta0 (by simp), by simp⟩
  | rel r ts =>
    cases r with
    | eq =>
      obtain ⟨Q, hQ, H⟩ := exists_prenexDefinable_terms (ts 0) (ts 1) f (R := (· = ·))
        (.of_delta0 <| definable_eq_term #0 #1)
      exact ⟨Q, hQ, fun v ↦ (H v).trans TallyNumber.ext_iff'.symm⟩
    | lt =>
      obtain ⟨Q, hQ, H⟩ := exists_prenexDefinable_terms (ts 0) (ts 1) f (R := IsProperPrefix)
        (.of_delta0 isProperPrefix_definable)
      exact ⟨Q, hQ, fun v ↦ (H v).trans Iff.rfl⟩
  | nrel r ts =>
    cases r with
    | eq =>
      obtain ⟨Q, hQ, H⟩ := exists_prenexDefinable_terms (ts 0) (ts 1) f (R := (· ≠ ·))
        (.of_delta0 <| (definable_eq_term #0 #1).not_zero)
      exact ⟨Q, hQ, fun v ↦ (H v).trans (not_congr TallyNumber.ext_iff'.symm)⟩
    | lt =>
      obtain ⟨Q, hQ, H⟩ := exists_prenexDefinable_terms (ts 0) (ts 1) f
        (R := fun x y ↦ ¬IsProperPrefix x y) (.of_delta0 isProperPrefix_definable.not_zero)
      exact ⟨Q, hQ, fun v ↦ (H v).trans Iff.rfl⟩
  | and _ _ ih₁ ih₂ =>
    obtain ⟨Q₁, hQ₁, H₁⟩ := ih₁
    obtain ⟨Q₂, hQ₂, H₂⟩ := ih₂
    exact ⟨_, PrenexDefinable.and_Sigma1 hQ₁ hQ₂, fun v ↦ by simp [H₁, H₂]⟩
  | or _ _ ih₁ ih₂ =>
    obtain ⟨Q₁, hQ₁, H₁⟩ := ih₁
    obtain ⟨Q₂, hQ₂, H₂⟩ := ih₂
    exact ⟨_, PrenexDefinable.or_Sigma1 hQ₁ hQ₂, fun v ↦ by simp [H₁, H₂]⟩
  | @ball k R φ t hR ht _ ih =>
    obtain rfl : R = Semiformula.Operator.LT.lt := Set.mem_singleton_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    have key (v : Fin k → TallyNumber V) :
        (∀¹[(Semiformula.Operator.LT.lt).operator ![#0, Rew.bShift t]] φ).Eval v f ↔
          ∀ x : TallyNumber V, x < t.val v f → φ.Eval (x :> v) f := by
      simp [Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.val, Semiterm.val_bShift']
    obtain ⟨G, hG, HG⟩ := exists_termGraph t f
    obtain ⟨Q, hQ, HQ⟩ := ih
    obtain ⟨C, hC, HC⟩ := TCISigma.exists_prenexDefinable_ball (k := k)
      (P := fun u ↦ Q (u 0 :> fun i ↦ u i.succ.succ) ∨ u 0 = u 1)
      ((hQ.retraction (0 :> fun i ↦ i.succ.succ)).or_delta0 (definable_eq_term #0 #1) |>.of_iff
        fun u ↦ by simp [Matrix.fun_vecCons_apply])
    refine ⟨fun w ↦ ∃ b, G (b :> w) ∧ C (b :> w),
      PrenexDefinable.exs_Sigma1 (PrenexDefinable.and_Sigma1 hG hC), fun v ↦ ?_⟩
    have HC' := HC ((t.val v f).1 :> fun i ↦ (v i).1) (t.val v f).2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ] at HC'
    rw [key]
    constructor
    · rintro ⟨b, hb, hc⟩ x hx
      obtain rfl := (HG v b).mp hb
      have hx' := (TCISigma.isSubstring_and_ne_iff (t.val v f).2).mpr ⟨x.2, hx⟩
      rcases HC'.mp hc x.1 hx'.1 with h | h
      · exact (HQ (x :> v)).mp <|
          cast (congrArg Q (Matrix.fun_vecCons_apply Subtype.val x v).symm) h
      · exact absurd h hx'.2
    · intro h
      refine ⟨_, (HG v _).mpr rfl, HC'.mpr fun y hy ↦ ?_⟩
      by_cases hyb : y = (t.val v f).1
      · exact .inr hyb
      · obtain ⟨ty, hlt⟩ := (TCISigma.isSubstring_and_ne_iff (t.val v f).2).mp ⟨hy, hyb⟩
        have := (HQ ((⟨y, ty⟩ : TallyNumber V) :> v)).mpr (h ⟨y, ty⟩ hlt)
        exact .inl <| cast (congrArg Q (Matrix.fun_vecCons_apply Subtype.val _ v)) this
  | @bexs k R φ t hR ht _ ih =>
    obtain rfl : R = Semiformula.Operator.LT.lt := Set.mem_singleton_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    have key (v : Fin k → TallyNumber V) :
        (∃¹[(Semiformula.Operator.LT.lt).operator ![#0, Rew.bShift t]] φ).Eval v f ↔
          ∃ x : TallyNumber V, x < t.val v f ∧ φ.Eval (x :> v) f := by
      simp [Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.val, Semiterm.val_bShift']
    obtain ⟨G, hG, HG⟩ := exists_termGraph t f
    obtain ⟨Q, hQ, HQ⟩ := ih
    refine ⟨fun w ↦ ∃ b, G (b :> w) ∧ ∃ x, Q (x :> fun i ↦ w i) ∧ IsSubstring x b ∧ x ≠ b,
      (PrenexDefinable.exs_Sigma1 <| PrenexDefinable.and_Sigma1 hG <|
        PrenexDefinable.exs_Sigma1 <| (hQ.retraction (0 :> fun i ↦ i.succ.succ)).and_delta0 <|
          (definable_isSubstring_term #0 #1).and (definable_eq_term #0 #1).not_zero).of_iff
        fun w ↦ by simp [Matrix.fun_vecCons_apply], fun v ↦ ?_⟩
    rw [key]
    constructor
    · rintro ⟨b, hb, x, hx, hxb, hne⟩
      obtain rfl := (HG v b).mp hb
      obtain ⟨tx, hlt⟩ := (TCISigma.isSubstring_and_ne_iff (t.val v f).2).mp ⟨hxb, hne⟩
      refine ⟨⟨x, tx⟩, hlt, (HQ (⟨x, tx⟩ :> v)).mp ?_⟩
      exact cast (congrArg Q (Matrix.fun_vecCons_apply Subtype.val _ v).symm) hx
    · rintro ⟨x, hx, h⟩
      have hx' := (TCISigma.isSubstring_and_ne_iff (t.val v f).2).mpr ⟨x.2, hx⟩
      exact ⟨_, (HG v _).mpr rfl, x.1,
        cast (congrArg Q (Matrix.fun_vecCons_apply Subtype.val x v)) ((HQ (x :> v)).mpr h),
        hx'.1, hx'.2⟩

/--
A prenex arithmetic formula of the level `s + 1` has a prenex definition of the same class and level
on the tallies.
- [HH14, Question 3]
-/
lemma exists_prenexDefinable_of_prenex (Γ : Polarity) (s : ℕ)
    (φ : ℬ[<, ℒₒᵣ].Prenex Γ (s + 1) ξ k) (f : ξ → TallyNumber V) :
    ∃ Q : (Fin k → V) → Prop, PrenexDefinable ℬₛ Γ (s + 1) Q ∧
      ∀ v : Fin k → TallyNumber V, (Q fun i ↦ (v i).1) ↔ φ.val.Eval v f := by
  have : Nonempty V := ⟨∅⟩
  have hT : 𝚺-[ℬₛ, 0].Definable fun w : Fin (k + 1) → V ↦ IsTally 1 (w 0) :=
    isTally_one_definable.retraction ![0]
  have hcons (x : TallyNumber V) (v : Fin k → TallyNumber V) :
      (fun i ↦ ((x :> v) i).1) = x.1 :> fun i ↦ (v i).1 :=
    Matrix.fun_vecCons_apply Subtype.val x v
  induction s generalizing k Γ with
  | zero =>
    rcases Γ
    · have hθ : ℬ[<, ℒₒᵣ].Closure φ.sigmaInv.val :=
        Hierarchy.zero_iff_bounded.mp φ.sigmaInv.val_hierarchy
      obtain ⟨Q, hQ, HQ⟩ := exists_prenexDefinable_of_closure hθ f
      refine ⟨fun w ↦ ∃ x, Q (x :> w) ∧ IsTally 1 x,
        PrenexDefinable.exs_Sigma1 (hQ.and_delta0 hT), fun v ↦ ?_⟩
      rw [φ.models_sigmaInv, TallyNumber.exists_iff]
      refine exists_congr fun x ↦ ⟨fun ⟨h, hx⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, h⟩ ↦ ⟨?_, hx⟩⟩
      · exact (HQ (⟨x, hx⟩ :> v)).mp (cast (congrArg Q (hcons ⟨x, hx⟩ v).symm) h)
      · exact cast (congrArg Q (hcons ⟨x, hx⟩ v)) ((HQ (⟨x, hx⟩ :> v)).mpr h)
    · have hθ : ℬ[<, ℒₒᵣ].Closure (∼φ.piInv.val) :=
        (Hierarchy.zero_iff_bounded.mp φ.piInv.val_hierarchy).neg
      obtain ⟨Q, hQ, HQ⟩ := exists_prenexDefinable_of_closure hθ f
      refine ⟨fun w ↦ ∀ x, ¬Q (x :> w) ∨ ¬IsTally 1 x,
        PrenexDefinable.all_Pi1 (hQ.not.or_delta0 hT.not_zero), fun v ↦ ?_⟩
      rw [φ.models_piInv, TallyNumber.forall_iff]
      refine forall_congr' fun x ↦ ⟨fun h hx ↦ ?_, fun h ↦ ?_⟩
      · have := (h.resolve_right (not_not.mpr hx))
        rw [← hcons ⟨x, hx⟩ v, HQ] at this
        simpa using this
      · by_cases hx : IsTally 1 x
        · left
          rw [← hcons ⟨x, hx⟩ v, HQ]
          simpa using h hx
        · exact .inr hx
  | succ s ih =>
    rcases Γ
    · obtain ⟨Q, hQ, HQ⟩ := ih 𝚷 φ.sigmaInv (isTally_one_definable.retraction ![0])
        fun x v ↦ Matrix.fun_vecCons_apply _ x v
      refine ⟨fun w ↦ ∃ x, Q (x :> w) ∧ IsTally 1 x, PrenexDefinable.exs (hQ.and_delta0 hT),
        fun v ↦ ?_⟩
      rw [φ.models_sigmaInv, TallyNumber.exists_iff]
      refine exists_congr fun x ↦ ⟨fun ⟨h, hx⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, h⟩ ↦ ⟨?_, hx⟩⟩
      · exact (HQ (⟨x, hx⟩ :> v)).mp (cast (congrArg Q (hcons ⟨x, hx⟩ v).symm) h)
      · exact cast (congrArg Q (hcons ⟨x, hx⟩ v)) ((HQ (⟨x, hx⟩ :> v)).mpr h)
    · obtain ⟨Q, hQ, HQ⟩ := ih 𝚺 φ.piInv (isTally_one_definable.retraction ![0])
        fun x v ↦ Matrix.fun_vecCons_apply _ x v
      refine ⟨fun w ↦ ∀ x, Q (x :> w) ∨ ¬IsTally 1 x,
        PrenexDefinable.all (hQ.or_delta0 hT.not_zero), fun v ↦ ?_⟩
      rw [φ.models_piInv, TallyNumber.forall_iff]
      refine forall_congr' fun x ↦ ⟨fun h hx ↦ ?_, fun h ↦ ?_⟩
      · exact (HQ (⟨x, hx⟩ :> v)).mp
          (cast (congrArg Q (hcons ⟨x, hx⟩ v).symm) (h.resolve_right (not_not.mpr hx)))
      · by_cases hx : IsTally 1 x
        · exact .inl <| cast (congrArg Q (hcons ⟨x, hx⟩ v)) ((HQ (⟨x, hx⟩ :> v)).mpr (h hx))
        · exact .inr hx

end definability

section induction

variable {V : Type*} [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* TCISigma 1]

/--
The tallies of a model of $\Sigma_{n+1}\text{-}\mathsf{TCI}$ satisfy induction for the prenex
$\Sigma_{n+1}$ formulas.
- [HH14, Question 3]
-/
lemma TallyNumber.models_inductionScheme (n : ℕ) [V↓[ℒ⌢ₑ] ⊧* TCISigma (n + 1)] :
    (TallyNumber V)↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 (n + 1)) := by
  apply Semantics.modelsSet_iff.mpr
  rintro _ ⟨_, ⟨ψ, rfl⟩, rfl⟩
  have hv (a : TallyNumber V) : (fun i ↦ (![a] i).1) = ![a.1] :=
    funext fun i ↦ by fin_cases i; rfl
  have key : ∀ f : ℕ → TallyNumber V, ∃ Q : (Fin 1 → V) → Prop,
      PrenexDefinable (substringBounding ℒ⌢ₑ) 𝚺 (n + 1) Q ∧
        ∀ a : TallyNumber V, Q ![a.1] ↔ ψ.val.Eval ![a] f := fun f ↦
    let ⟨Q, hQ, HQ⟩ := exists_prenexDefinable_of_prenex 𝚺 n ψ f
    ⟨Q, hQ, fun a ↦ by rw [← hv, HQ]⟩
  generalize ψ.val = φ at key
  suffices ∀ f : ℕ → TallyNumber V, φ.Eval ![0] f →
      (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) → ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this
  intro f h₀ hs x
  obtain ⟨Q, hQ, H⟩ := key f
  have := TCISigma.tally_induction (s := n + 1) (P := fun y ↦ Q ![y])
    (hQ.of_iff fun v ↦ by rw [← Matrix.fun_eq_vec_one]) ((H 0).mpr h₀)
    (fun y hy h ↦ (H (⟨y, hy⟩ + 1)).mpr (hs _ ((H ⟨y, hy⟩).mp h))) x.1 x.2
  exact (H x).mp this

namespace TallyNumber

/-- Induction on the tallies for bounded arithmetic formulas. -/
lemma induction {P : TallyNumber V → Prop} (φ : Semiformula ℒₒᵣ ℕ 1)
    (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ) (e : ℕ → TallyNumber V) (hP : ∀ x, P x ↔ φ.Eval ![x] e)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  have := models_inductionScheme (V := V) 0
  have : Nonempty (TallyNumber V) := ⟨0⟩
  obtain ⟨ψ, hψ, H⟩ := PrenexHierarchy.exists_eval_iff_of_deltaZero hφ 𝚺 1
  exact InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 1)
    ⟨e, ψ, hψ, fun x ↦ (hP x).trans (H _ _ _)⟩ zero succ

variable {a b c : TallyNumber V}

protected lemma add_zero (a : TallyNumber V) : a + 0 = a := ext_iff'.mpr <| by simp

protected lemma add_assoc (a b c : TallyNumber V) : a + b + c = a + (b + c) :=
  ext_iff'.mpr <| by simp [TCEmpty.append_assoc]

protected lemma add_comm (a b : TallyNumber V) : a + b = b + a :=
  ext_iff'.mpr <| by simpa using TCISigma.append_comm a.2 b.2

lemma ne_zero_iff : a ≠ 0 ↔ a.1 ≠ ∅ := by simp [ext_iff']

lemma exists_add_eq_of_lt (h : a < b) : ∃ c < b + 1, a + c = b := by
  obtain ⟨z, hz, hb⟩ := h
  have tz : IsTally 1 z := TCEmpty.isTally_of_isSubstring b.2 (hb ▸ isSubstring_append_right _ _)
  refine ⟨⟨z, tz⟩, ⟨a.1 ++ 1, fun h ↦ TCEmpty.one_ne_empty
    (TCEmpty.eq_empty_of_append_eq_empty h).2, ?_⟩, ext_iff'.mpr hb.symm⟩
  simp [hb, ← TCEmpty.append_assoc, TCISigma.append_comm a.2 tz]

lemma zero_le (a : TallyNumber V) : 0 = a ∨ 0 < a := by
  by_cases h : a.1 = ∅
  · exact .inl (ext_iff'.mpr h.symm)
  · exact .inr ⟨a.1, h, by simp⟩

lemma zero_lt_one : (0 : TallyNumber V) < 1 := ⟨1, TCEmpty.one_ne_empty, by simp⟩

lemma one_le_of_zero_lt (h : 0 < a) : 1 = a ∨ 1 < a := by
  obtain ⟨z, hz, ha⟩ := h
  simp only [val_zero, TCEmpty.empty_append] at ha
  obtain ⟨x, tx, hx⟩ := TCISigma.eq_append_one_of_ne_empty a.2 (ha ▸ hz)
  by_cases hx' : x = ∅
  · exact .inl (ext_iff'.mpr (by simp [hx, hx']))
  · exact .inr ⟨x, hx', by simp [hx, TCISigma.append_comm tx TCEmpty.isTally_one]⟩

lemma add_lt_add (h : a < b) (c : TallyNumber V) : a + c < b + c := by
  obtain ⟨z, hz, hb⟩ := h
  have tz : IsTally 1 z := TCEmpty.isTally_of_isSubstring b.2 (hb ▸ isSubstring_append_right _ _)
  exact ⟨z, hz, by simp [hb, TCEmpty.append_assoc, TCISigma.append_comm tz c.2]⟩

lemma lt_irrefl (a : TallyNumber V) : ¬a < a := fun ⟨_, hz, h⟩ ↦
  hz (TCISigma.eq_empty_of_append_eq_self h.symm)

lemma lt_trans (hab : a < b) (hbc : b < c) : a < c := by
  obtain ⟨z, hz, hb⟩ := hab
  obtain ⟨z', -, hc⟩ := hbc
  exact ⟨z ++ z', fun h ↦ hz (TCEmpty.eq_empty_of_append_eq_empty h).1,
    by simp [hc, hb, TCEmpty.append_assoc]⟩

lemma lt_tri (a b : TallyNumber V) : a < b ∨ a = b ∨ b < a := by
  rcases TCISigma.exists_append_eq_or_exists_append_eq a.2 b.2 with ⟨z, h⟩ | ⟨z, h⟩
  · by_cases hz : z = ∅
    · exact .inr <| .inl <| ext_iff'.mpr (by simpa [hz] using h)
    · exact .inl ⟨z, hz, h.symm⟩
  · by_cases hz : z = ∅
    · exact .inr <| .inl <| ext_iff'.mpr (by simpa [hz] using h.symm)
    · exact .inr <| .inr ⟨z, hz, h.symm⟩

protected lemma mul_zero (a : TallyNumber V) : a * 0 = 0 :=
  ext_iff'.mpr <| val_mul_eq_iff.mpr (isTallyMul_empty a.2)

protected lemma zero_mul (a : TallyNumber V) : 0 * a = 0 :=
  ext_iff'.mpr <| val_mul_eq_iff.mpr ⟨∅, by simp, a.2, by simp, .inl ⟨.inl rfl, rfl⟩⟩

lemma mul_add_one (a b : TallyNumber V) : a * (b + 1) = a * b + a :=
  ext_iff'.mpr <| val_mul_eq_iff.mpr (isTallyMul_val_mul a b).append_one

protected lemma mul_one (a : TallyNumber V) : a * 1 = a := by
  simpa [TallyNumber.mul_zero, TallyNumber.add_comm 0, TallyNumber.add_zero,
    show (0 : TallyNumber V) + 1 = 1 from ext_iff'.mpr (by simp)] using mul_add_one a 0

protected lemma mul_add (a b c : TallyNumber V) : a * (b + c) = a * b + a * c := by
  refine induction (P := fun c ↦ a * (b + c) = a * b + a * c)
    “x. &0 * (&1 + x) = &0 * &1 + &0 * x” (by simp) (fun i ↦ if i = 0 then a else b)
    (fun x ↦ by simp) ?_ ?_ c
  · rw [TallyNumber.add_zero, TallyNumber.mul_zero, TallyNumber.add_zero]
  · intro c ih
    rw [← TallyNumber.add_assoc, mul_add_one, ih, mul_add_one, TallyNumber.add_assoc]

protected lemma mul_assoc (a b c : TallyNumber V) : a * b * c = a * (b * c) := by
  refine induction (P := fun c ↦ a * b * c = a * (b * c)) “x. &0 * &1 * x = &0 * (&1 * x)”
    (by simp) (fun i ↦ if i = 0 then a else b) (fun x ↦ by simp) ?_ ?_ c
  · simp only [TallyNumber.mul_zero]
  · intro c ih
    rw [mul_add_one, ih, mul_add_one, TallyNumber.mul_add]

lemma add_one_mul (a b : TallyNumber V) : (a + 1) * b = a * b + b := by
  refine induction (P := fun b ↦ (a + 1) * b = a * b + b) “x. (&0 + 1) * x = &0 * x + x”
    (by simp) (fun _ ↦ a) (fun x ↦ by simp) ?_ ?_ b
  · simp only [TallyNumber.mul_zero, TallyNumber.add_zero]
  · intro b ih
    rw [mul_add_one, ih, mul_add_one, TallyNumber.add_assoc, TallyNumber.add_assoc,
      ← TallyNumber.add_assoc b, TallyNumber.add_comm b a, TallyNumber.add_assoc a b]

protected lemma mul_comm (a b : TallyNumber V) : a * b = b * a := by
  refine induction (P := fun b ↦ a * b = b * a) “x. &0 * x = x * &0” (by simp) (fun _ ↦ a)
    (fun x ↦ by simp) ?_ ?_ b
  · rw [TallyNumber.mul_zero, TallyNumber.zero_mul]
  · intro b ih
    rw [mul_add_one, ih, add_one_mul]

lemma mul_lt_mul (h : a < b) (hc : 0 < c) : a * c < b * c := by
  obtain ⟨d, -, rfl⟩ := exists_add_eq_of_lt h
  have hd : d ≠ 0 := fun hd ↦ lt_irrefl a (by simpa [hd, TallyNumber.add_zero] using h)
  obtain rfl | ⟨c', rfl⟩ : c = 0 ∨ ∃ c', c = c' + 1 := by
    by_cases hc₀ : c.1 = ∅
    · exact .inl (ext_iff'.mpr hc₀)
    · obtain ⟨x, tx, hx⟩ := TCISigma.eq_append_one_of_ne_empty c.2 hc₀
      exact .inr ⟨⟨x, tx⟩, ext_iff'.mpr hx⟩
  · exact absurd hc (lt_irrefl 0)
  have e : (a + d) * (c' + 1) = a * (c' + 1) + (d * c' + d) := by
    rw [TallyNumber.mul_comm, TallyNumber.mul_add, TallyNumber.mul_comm _ a,
      TallyNumber.mul_comm _ d, mul_add_one d]
  rw [e]
  refine ⟨(d * c' + d).1, ?_, rfl⟩
  simpa using fun h ↦ (ne_zero_iff.mp hd) (TCEmpty.eq_empty_of_append_eq_empty h).2

end TallyNumber

/--
The tallies of a model of $\Sigma_1\text{-}\mathsf{TCI}$ form a model of $\mathsf{PA}^-$.
- [HH14, Question 3]
-/
instance TallyNumber.models_PeanoMinus : (TallyNumber V)↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case addZero => simpa [models_iff] using TallyNumber.add_zero (V := V)
  case addAssoc => simpa [models_iff] using TallyNumber.add_assoc (V := V)
  case addComm => simpa [models_iff] using TallyNumber.add_comm (V := V)
  case addEqOfLt =>
    simpa [models_iff, Semiformula.eval_bexsLTSucc] using
      fun a b ↦ TallyNumber.exists_add_eq_of_lt (V := V) (a := a) (b := b)
  case zeroLe =>
    simpa [models_iff, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
      Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq] using
      TallyNumber.zero_le (V := V)
  case zeroLtOne => simpa [models_iff] using TallyNumber.zero_lt_one (V := V)
  case oneLeOfZeroLt =>
    simpa [models_iff, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
      Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq] using
      fun a ↦ TallyNumber.one_le_of_zero_lt (V := V) (a := a)
  case addLtAdd =>
    simpa [models_iff] using fun a b c h ↦ TallyNumber.add_lt_add (V := V) (a := a) (b := b) h c
  case mulZero => simpa [models_iff] using TallyNumber.mul_zero (V := V)
  case mulOne => simpa [models_iff] using TallyNumber.mul_one (V := V)
  case mulAssoc => simpa [models_iff] using TallyNumber.mul_assoc (V := V)
  case mulComm => simpa [models_iff] using TallyNumber.mul_comm (V := V)
  case mulLtMul =>
    simpa [models_iff] using fun a b c ↦ TallyNumber.mul_lt_mul (V := V) (a := a) (b := b) (c := c)
  case distr => simpa [models_iff] using TallyNumber.mul_add (V := V)
  case ltIrrefl => simpa [models_iff] using TallyNumber.lt_irrefl (V := V)
  case ltTrans =>
    simpa [models_iff] using fun a b c ↦ TallyNumber.lt_trans (V := V) (a := a) (b := b) (c := c)
  case ltTri => simpa [models_iff] using TallyNumber.lt_tri (V := V)

/--
The tallies of a model of $\Sigma_{n+1}\text{-}\mathsf{TCI}$ form a model of
$\mathsf{I}\Sigma_{n+1}$.
- [HH14, Question 3]
-/
lemma TallyNumber.models_ISigma (n : ℕ) [V↓[ℒ⌢ₑ] ⊧* TCISigma (n + 1)] :
    (TallyNumber V)↓[ℒₒᵣ] ⊧* 𝗜𝚺 (n + 1) :=
  have := TallyNumber.models_inductionScheme (V := V) n
  Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, this⟩

end induction

section translation

open DirectTranslation

/-- `z` is the product of the `1`-tallies `x` and `y`. -/
def isTallyMulDef : Semisentence ℒ⌢ₑ 3 := “z x y. ∃ r, !isTallyMulWitnessDef.val r x y z”

instance isTallyMul_defined {V : Type*} [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] :
    ℒ⌢ₑ-relation₃[V] (fun z x y ↦ IsTallyMul x y z) via isTallyMulDef :=
  ⟨fun v ↦ by simp [isTallyMulDef, IsTallyMul]⟩

variable (n : ℕ)

/--
The translation of the language of arithmetic into $\Sigma_{n+1}\text{-}\mathsf{TCI}$: the
numbers are the `1`-tallies, `0` is the empty string, `1` is the letter `1`, `+` is the
concatenation, `*` is the multiplication of tallies, and `<` is the proper prefix relation.
- [HH14, Question 3]
- [Gan09, §1, Definition 2]
-/
def tallyTranslation : DirectTranslation (TCISigma (n + 1)) ℒₒᵣ where
  domain := ⟨isTallyOneDef.val⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
    | .lt => ⟨isProperPrefixDef.val⟩
  func
    | .zero => ⟨“z. z = ⋆”⟩
    | .one => ⟨“z. z = !!(op(1).const)”⟩
    | .add => ⟨“z x y. z = x ⌢ y”⟩
    | .mul => ⟨isTallyMulDef⟩
  domain_nonempty := completeEmpty.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    have : V↓[ℒ⌢ₑ] ⊧* TCISigma 1 := TCISigma.models_of_le (s' := n + 1) (by omega)
    exact ⟨∅, by simp [Semiformula.Operator.val]⟩
  func_defined f := completeEmpty.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    have : V↓[ℒ⌢ₑ] ⊧* TCISigma 1 := TCISigma.models_of_le (s' := n + 1) (by omega)
    intro e he
    have he (i) : IsTally 1 (e i) := by simpa [Semiformula.Operator.val] using he i
    cases f
    · suffices ∃! y : V, IsTally 1 y ∧ y = ∅ by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      exact ⟨∅, by simp, fun _ h ↦ h.2⟩
    · suffices ∃! y : V, IsTally 1 y ∧ y = 1 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      exact ⟨1, ⟨TCEmpty.isTally_one, rfl⟩, fun _ h ↦ h.2⟩
    · suffices ∃! y : V, IsTally 1 y ∧ y = e 0 ++ e 1 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      exact ⟨_, ⟨TCEmpty.isTally_append (he 0) (he 1), rfl⟩, fun _ h ↦ h.2⟩
    · suffices ∃! y : V, IsTally 1 y ∧ IsTallyMul (e 0) (e 1) y by
        simpa [Semiformula.Operator.val]
      obtain ⟨z, hz⟩ := exists_isTallyMul (he 0) (he 1)
      exact ⟨z, ⟨hz.isTally, hz⟩, fun _ h ↦ h.2.unique hz⟩
  preserve_eq := completeEmpty.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

namespace tallyTranslation

variable {n} {V : Type*} [ConcatenationEmptyStructure V]

@[simp]
lemma dom_iff [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] {x : V} : (tallyTranslation n).Dom x ↔ IsTally 1 x := by
  simp [DirectTranslation.dom_iff, tallyTranslation, Semiformula.Operator.val]

variable [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] [V↓[ℒ⌢ₑ] ⊧* TCISigma (n + 1)]

/-- The tallies of `V` are the elements of the model of `tallyTranslation`. -/
def equiv : TallyNumber V ≃ (tallyTranslation n).Model V where
  toFun a := ⟨a.1, dom_iff.mpr a.2⟩
  invFun x := ⟨x.1, dom_iff.mp x.dom⟩

lemma struc_eq : Model.struc (tallyTranslation n) V = Tarski.Structure.ofEquiv equiv := by
  apply Tarski.Structure.ext
  · funext k f v
    symm
    apply Model.func_iff.mpr
    obtain ⟨v, rfl⟩ : ∃ w, v = equiv ∘ w := ⟨equiv.symm ∘ v, by simp [← Function.comp_assoc]⟩
    cases f
    · simp [tallyTranslation, Semiformula.Operator.val]
      rfl
    · simp [tallyTranslation, Semiformula.Operator.val]
      rfl
    · simp [tallyTranslation, Semiformula.Operator.val]
      rfl
    · simp only [Semiformula.Operator.val, tallyTranslation, Fin.isValue, Function.comp_apply,
        Defined.eval_iff, Matrix.cons_val_one, Matrix.cons_app_two, Matrix.cons_val_zero]
      exact TallyNumber.isTallyMul_val_mul (v 0) (v 1)
  · funext k r v
    cases r
    · exact propext <| (Model.eq_iff v).trans equiv.symm.apply_eq_iff_eq.symm
    · apply propext
      rw [Model.rel_iff, Matrix.fun_eq_vec_two (fun i ↦ (v i : V))]
      simp [tallyTranslation, Semiformula.Operator.val]
      rfl

end tallyTranslation

/--
The tallies of a model of $\Sigma_{n+1}\text{-}\mathsf{TCI}$ form a model of
$\mathsf{I}\Sigma_{n+1}$.
- [HH14, Question 3]
-/
instance {V : Type*} [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* TCISigma (n + 1)] :
    ((tallyTranslation n).Model V)↓[ℒₒᵣ] ⊧* 𝗜𝚺 (n + 1) := by
  have : V↓[ℒ⌢ₑ] ⊧* TCISigma 1 := TCISigma.models_of_le (s' := n + 1) (by omega)
  have : Nonempty ((tallyTranslation n).Model V) := ⟨tallyTranslation.equiv 0⟩
  have : TallyNumber V ≡ₑ[ℒₒᵣ] (tallyTranslation n).Model V := by
    rw [tallyTranslation.struc_eq]
    exact Tarski.Structure.ElementaryEquiv.ofEquiv _
  have := TallyNumber.models_ISigma (V := V) n
  exact (Tarski.Structure.ElementaryEquiv.modelsTheory (M₁ := TallyNumber V)).mp this

/--
$\Sigma_{n+1}\text{-}\mathsf{TCI}$ interprets $\mathsf{I}\Sigma_{n+1}$.
- [HH14, Question 3]
-/
instance tallyInterpretation : TCISigma (n + 1) ⊳ 𝗜𝚺 (n + 1) where
  trln := tallyTranslation n
  interpret_theory _ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    DirectTranslation.models_translate_of_mem hφ

end translation

end FFL.FirstOrder.Concatenation
