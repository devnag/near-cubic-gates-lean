import Proof.Wire_3_5.PrimAsmEmit
import Proof.Gates.Codec.Field

/-! Q04: actual binary field preparation for the balanced-circuit decoder.
The padded low-bit word has exact natural value, including the zero case. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.PhysicalFields

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ}

def paddedBits (v : ℕ) : List Bool := WilliamsPublishedForm.fixedWidthNatBits (natBitLength v) v

theorem paddedBits_length (v : ℕ) : (paddedBits v).length = natBitLength v := by
  simp [paddedBits, WilliamsPublishedForm.fixedWidthNatBits]

theorem paddedBits_value (v : ℕ) : RadixSemantics.value (paddedBits v) = v := by
  rw [paddedBits, NearCubicGates.Close.Codec.fixedWidthNatBits_eq_binary]
  exact SignedSortKey.binary_value _ _ (Nat.lt_pow_succ_log_self (by decide) v)

def writeBits (O : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (bitLenM R) (.seq (payM O R) (.seq (WM.clear (R 4))
    (.seq (emitC O (R 7) false) (WM.rewind O (R 7)))))

/-- Writes and rewinds the exact physical binary frame; all registers are restored. -/
theorem write_bits (cap : ℕ) (O : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (σ : WState ns nr)
    (hz : ∀ i : Fin 8, i ≠ 0 → σ.val (R i) = 0) (ho : σ.st O = []) (hh : σ.sh O = 0)
    (hcap : σ.val (R 0) + 6 * natBitLength (σ.val (R 0)) + 10 ≤ cap) :
    WExec cap (writeBits O R) σ (σ.sets O (frame (paddedBits (σ.val (R 0)))))
      (1000 * (σ.val (R 0) + 1) ^ 2) := by
  have hne {i j : Fin 8} (h : i ≠ j) : R i ≠ R j := R.injective.ne h
  let v := σ.val (R 0)
  let ℓ := natBitLength v
  change v + 6 * ℓ + 10 ≤ cap at hcap
  have hbits : ℓ ≤ v + 1 := by
    dsimp [ℓ, natBitLength]
    have h := Nat.log_lt_self 2 (show v + 1 ≠ 0 by omega)
    have hm := Nat.log_mono_right (show v ≤ v + 1 by omega) (b := 2)
    omega
  have e1 := bitLenM_spec cap R σ (hz 1 (by decide)) (hz 2 (by decide))
    (hz 3 (by decide)) (hz 4 (by decide)) (hz 6 (by decide)) (by change v + 2 ≤ cap; omega)
  let σ1 := σ.setv (R 4) ℓ
  have e2 := payM_spec cap O R σ1
    (by simp [σ1, hne, hz]) (by simp [σ1, hne, hz]) (by simp [σ1, hne, hz])
    (by simp [σ1, hne, hz]) (by simp [σ1, hne, hz]) (by simp [σ1, ho, hh])
    (by simpa [σ1, hne, v, ℓ, natBitLength] using (Nat.lt_pow_succ_log_self (b := 2) (by decide) v))
    (by simp [σ1, hne, hz]; change v + ℓ + 0 + 2 * ℓ + 2 ≤ cap; omega)
  simp only [σ1, WState.setv_val, Function.update_self,
    Function.update_of_ne (hne (show (0 : Fin 8) ≠ 4 by decide))] at e2
  let σ2 := appendO σ1 O (R 7) (Streaming.marks (paddedBits v))
  have hlen : (Streaming.marks (paddedBits v)).length = 2 * ℓ := by
    rw [Streaming.marks_length, paddedBits_length]
  have e3 := wclear_spec cap (R 4) ℓ σ2
    (by simp [σ2, σ1, hne]) (by simp [σ2, σ1, hne]; omega)
  let σ3 := σ2.setv (R 4) 0
  have e4 := emitC_spec cap O (R 7) false σ3
    (by simp [σ3, σ2, σ1, ho, hh]) (by simp [σ3, σ2, σ1, hne, hz, hlen]; omega)
  let σ4 := appendO σ3 O (R 7) [false]
  have e5 := wrewind_spec cap O (R 7) (2 * ℓ + 1) σ4
    (by simp [σ4, σ3, σ2, σ1, hne, hz, hlen])
    (by simp [σ4, σ3, σ2, σ1, hne, hz, hlen]; omega)
  have he := WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))
  have hs : (σ4.setv (R 7) 0).seth O (σ4.sh O - (2 * ℓ + 1)) = σ.sets O (frame (paddedBits v)) := by
    apply WState.eq
    · funext i
      by_cases hi : i = O
      · subst i; simp [σ4, σ3, σ2, σ1, hh, hlen]
      · simp [σ4, σ3, σ2, σ1, hi]
    · funext i
      by_cases hi : i = O
      · subst i
        simp [σ4, σ3, σ2, σ1, ho]
        exact (NearCubicWires.WireExponent3_5.PrimAsm.FiltRec.frame_eq _).symm
      · simp [σ4, σ3, σ2, σ1, hi]
    · funext i
      by_cases h7 : i = R 7
      · subst i; simp [hz]
      · by_cases h4 : i = R 4
        · subst i; simp [σ4, σ3, σ2, σ1, hne, hz]
        · simp [σ4, σ3, σ2, σ1, h7, h4]
    · rfl
  rw [hs] at he
  refine he.cast cap rfl ?_
  change 60 * v + 60 + 1 + (ℓ * (10 * v + 40) + 40 * v + 40 * ℓ + 20 + 1 +
    (3 * ℓ + 1 + 1 + (8 + (5 * (2 * ℓ + 1) + 1)))) ≤ 1000 * (v + 1) ^ 2
  have hm := Nat.mul_le_mul_right (10 * v + 40) hbits
  nlinarith

end NearCubicGates.Adapters.Proximity.PhysicalFields
