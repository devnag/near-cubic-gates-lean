import SourceAdapters.Proximity.DecoderBankFields
import Proof.CaseAnalysis.WitnessOracleCallRun

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": exact prepared-bank correspondence to the released
balanced circuit decoder. Padded arity bits have the same decoded value. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.DecoderBank

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Expand.PolyTab
open PhysicalFields CloseoutWitness

def decoderSlots (i : Fin (Oracle.tapes + 1)) : Fin 1382 :=
  if i.val = 0 then 1381 else i.castSucc

theorem decoderSlots_injective : Function.Injective decoderSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  dsimp [decoderSlots] at hv
  split_ifs at hv with hi hj hj
  · exact Fin.ext (by omega)
  · simp only [Fin.val_castSucc] at hv
    have hj := j.isLt
    change j.val < 1381 at hj
    omega
  · simp only [Fin.val_castSucc] at hv
    have hi := i.isLt
    change i.val < 1381 at hi
    omega
  · exact Fin.ext hv

theorem decoderSlots_ne_zero (i : Fin (Oracle.tapes + 1)) : decoderSlots i ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [decoderSlots] at hv
  split_ifs at hv with hi
  · contradiction
  · exact hi hv

theorem prepared_heads (C : Circuit) (i : Fin (Oracle.tapes + 1)) : (prepared C).sh (decoderSlots i) = 0 := by
  have hi := decoderSlots_ne_zero i
  simp [prepared, guardCountLoaded, unaryLoaded, binaryLoaded, bitsLoaded,
    afterArity, afterLength, initial, idealStart, hi]

theorem prepared_tapes (C : Circuit) (i : Fin (Oracle.tapes + 1)) :
    (prepared C).st (decoderSlots i) = Oracle.coldInput (decoderGuard C) (decoderBits C) (paddedBits C.n) i := by
  rw [OracleCall.parser_input_shape, paddedBits_value]
  have hi := i.isLt
  change i.val < 1381 at hi
  by_cases h0 : i.val = 0
  · have he : i = 0 := Fin.ext h0
    subst i
    simp [decoderSlots, prepared, guardCountLoaded, unaryLoaded, binaryLoaded, bitsLoaded,
      afterArity, afterLength, initial, idealStart]
  · by_cases h1 : i.val = 1
    · have he : i = 1 := Fin.ext h1
      subst i
      simp [decoderSlots, prepared, guardCountLoaded, unaryLoaded, binaryLoaded, bitsLoaded,
        afterArity, afterLength, initial, idealStart]
    · by_cases h2 : i.val = 2
      · have he : i = 2 := Fin.ext h2
        subst i
        simp [decoderSlots, prepared, guardCountLoaded, unaryLoaded, binaryLoaded, bitsLoaded,
          afterArity, afterLength, initial, idealStart, Oracle.tapes]
      · by_cases h3 : i.val = 3
        · have he : i = 3 := Fin.ext h3
          subst i
          simp [decoderSlots, prepared, guardCountLoaded, unaryLoaded, binaryLoaded, bitsLoaded,
            afterArity, afterLength, initial, idealStart, Oracle.tapes]
        · have hg : i.val ≠ 1381 := by omega
          have hc {k : Fin 1382} (hk : i.val ≠ k.val) : i.castSucc ≠ k :=
            fun he => hk (congrArg Fin.val he)
          simp [decoderSlots, h0, h1, h2, h3, hc (k := 1381) hg, hc (k := 1) h1, hc (k := 2) h2, hc (k := 3) h3, hc (k := 0) h0,
            prepared, guardCountLoaded, unaryLoaded, binaryLoaded,
            bitsLoaded, afterArity, afterLength, initial, idealStart]

def paddedBudget (C : Circuit) := Oracle.budget (decoderGuard C) (decoderBits C) (paddedBits C.n)

theorem padded_ready (C : Circuit) :
    ∃ out, ClockJoin.ReadyRun Oracle.machine (paddedBudget C)
      (Oracle.coldInput (decoderGuard C) (decoderBits C) (paddedBits C.n)) out ∧
      out Oracle.descriptorSlot = PCPPNative.descriptor C.D := by
  obtain ⟨hN, hcap, _, hn⟩ := decoder_guard_conditions C
  have hb : (paddedBits C.n).length ≤ (decoderGuard C).length + 1 := by
    rw [paddedBits_length]
    have h := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le C.n
    omega
  obtain ⟨out, hr, _, hd⟩ := Oracle.cold_run (decoderGuard C) (decoderBits C) (paddedBits C.n) hN hcap hb
  have hbits : value (decoderBits C) = encodeBooleanCircuit C.D := DimensionProducer.bits_value _
  rw [paddedBits_value, hbits] at hd
  exact ⟨out, hr, hd C.D (decodeBooleanCircuit_encode C.D)⟩

theorem padded_budget (C : Circuit) :
    paddedBudget C ≤ (40000000000000000000000 * 18 ^ 25) * (C.word.length + 1) ^ 25 := by
  obtain ⟨hN, hcap, _, hn⟩ := decoder_guard_conditions C
  have h := Oracle.budget_polynomial (decoderGuard C) (decoderBits C) (paddedBits C.n)
    hN hcap (by simpa only [paddedBits_value] using hn)
  have hg : (decoderGuard C).length + 2 ≤ 18 * (C.word.length + 1) := by
    simp only [decoderGuard, List.length_replicate]
    omega
  calc
    paddedBudget C ≤ 40000000000000000000000 * ((decoderGuard C).length + 2) ^ 25 := h
    _ ≤ 40000000000000000000000 * (18 * (C.word.length + 1)) ^ 25 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hg 25)
    _ = _ := by rw [mul_pow, Nat.mul_assoc]

end NearCubicGates.Adapters.Proximity.DecoderBank
