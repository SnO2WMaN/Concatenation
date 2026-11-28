module

public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-!
# Coding of the sum of two languages

The symbols of `L₁.add L₂` are primitive-recursively coded if those of `L₁` and `L₂` are.
-/

@[expose] public section

namespace FFL.FirstOrder.Language

variable {L₁ L₂ : Language} [L₁.Encodable] [L₂.Encodable]

instance : (L₁.add L₂).Encodable where
  func k := inferInstanceAs (Encodable (L₁.Func k ⊕ L₂.Func k))
  rel k := inferInstanceAs (Encodable (L₁.Rel k ⊕ L₂.Rel k))

/-- The code of the sum of two options, given by their codes, at the code `e`. -/
def sumCode (a b : ℕ → ℕ) (e : ℕ) : ℕ :=
  bif e.bodd then bif b e.div2 == 0 then 0 else 2 * b e.div2
  else bif a e.div2 == 0 then 0 else 2 * a e.div2 - 1

lemma encode_decode_sum {α β : Type*} [Encodable α] [Encodable β] (e : ℕ) :
    Encodable.encode (Encodable.decode e : Option (α ⊕ β)) =
      sumCode (fun e ↦ Encodable.encode (Encodable.decode e : Option α))
        (fun e ↦ Encodable.encode (Encodable.decode e : Option β)) e := by
  change Encodable.encode (Encodable.decodeSum e : Option (α ⊕ β)) = _
  unfold Encodable.decodeSum sumCode
  cases e.bodd
  · cases h' : (Encodable.decode e.div2 : Option α) <;> simp [h']; omega
  · cases h' : (Encodable.decode e.div2 : Option β) <;> simp [h']; omega

lemma primrec_sumCode {a b : ℕ → ℕ → ℕ} (ha : Primrec₂ a) (hb : Primrec₂ b) :
    Primrec₂ fun k e ↦ sumCode (a k) (b k) e := by
  have hd : Primrec fun p : ℕ × ℕ ↦ p.2.div2 := Primrec.nat_div2.comp .snd
  have ha' := ha.comp Primrec.fst hd
  have hb' := hb.comp Primrec.fst hd
  apply Primrec.cond (Primrec.nat_bodd.comp .snd)
  · exact Primrec.cond (Primrec.beq.comp hb' (.const 0)) (.const 0)
      (Primrec.nat_mul.comp (.const 2) hb')
  · exact Primrec.cond (Primrec.beq.comp ha' (.const 0)) (.const 0)
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp (.const 2) ha') (.const 1))

instance [L₁.Primcodable] [L₂.Primcodable] : (L₁.add L₂).Primcodable where
  func := (primrec_sumCode Primcodable.func Primcodable.func).of_eq
    fun _ _ ↦ (encode_decode_sum _).symm
  rel := (primrec_sumCode Primcodable.rel Primcodable.rel).of_eq
    fun _ _ ↦ (encode_decode_sum _).symm

end FFL.FirstOrder.Language
