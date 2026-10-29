import SourceAdapters.Proximity.TargetLengths
import Proof.CaseAnalysis.CloseoutWitnessOracleBudget

/-!
Q01/Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": reuse the released actual balanced-circuit decoder.
The prepared input banks and the output native descriptor are explicit.
The bank loader and the native-descriptor to source-word transducer remain
separate ordinary programs; this theorem does not infer either from a size
bound or change the source leaf's encoding.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.RepairOrdinary NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.RepairSource.ProjectionNormalization

/-- A physical unary workspace guard, polynomial in the actual target word. -/
def decoderGuard (C : Circuit) : List Bool := List.replicate (16 * (C.word.length + 1)) true

def decoderBits (C : Circuit) : List Bool := (encodeBooleanCircuit C.D).bits

def decoderBudget (C : Circuit) : ℕ :=
  CloseoutWitness.Oracle.budget (decoderGuard C) (decoderBits C) C.n.bits

def decoderInputTapes (C : Circuit) :=
  CloseoutWitness.Oracle.coldInput (decoderGuard C) (decoderBits C) C.n.bits

theorem decoder_guard_conditions (C : Circuit) :
    2 ≤ (decoderGuard C).length ∧ 16 * (decoderBits C).length ≤ (decoderGuard C).length ∧
      C.n.bits.length ≤ (decoderGuard C).length + 1 ∧ C.n ≤ (decoderGuard C).length := by
  have hn : C.n ≤ C.m := C.sizeAtLeast
  have hm := target_nodes_le_word C
  have hb : (decoderBits C).length ≤ C.word.length := by
    simp only [decoderBits, Circuit.word, List.length_append]
    omega
  have hnb : C.n.bits.length ≤ C.n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [decoderGuard, List.length_replicate]
  omega

/-- Actual cold run, exact flat descriptor, and physical reset of every head. -/
theorem native_descriptor_ready (C : Circuit) :
    ∃ out, ClockJoin.ReadyRun CloseoutWitness.Oracle.machine (decoderBudget C)
      (decoderInputTapes C) out ∧
      out CloseoutWitness.Oracle.descriptorSlot = PCPPNative.descriptor C.D := by
  obtain ⟨hN, hcap, hb, _⟩ := decoder_guard_conditions C
  obtain ⟨out, hr, _, hd⟩ := CloseoutWitness.Oracle.cold_run
    (decoderGuard C) (decoderBits C) C.n.bits hN hcap hb
  have hnat : value C.n.bits = C.n := DimensionProducer.bits_value C.n
  have hbits : value (decoderBits C) = encodeBooleanCircuit C.D := DimensionProducer.bits_value _
  rw [hnat, hbits] at hd
  exact ⟨out, hr, hd C.D (decodeBooleanCircuit_encode C.D)⟩

/-- Every decoding step is included in this fixed polynomial. -/
theorem native_descriptor_budget (C : Circuit) :
    decoderBudget C ≤ (40000000000000000000000 * 18 ^ 25) * (C.word.length + 1) ^ 25 := by
  obtain ⟨hN, hcap, _, hn⟩ := decoder_guard_conditions C
  have h := CloseoutWitness.Oracle.budget_polynomial (decoderGuard C) (decoderBits C) C.n.bits
    hN hcap (by simpa only [DimensionProducer.bits_value] using hn)
  have hg : (decoderGuard C).length + 2 ≤ 18 * (C.word.length + 1) := by
    simp only [decoderGuard, List.length_replicate]
    omega
  calc
    decoderBudget C ≤ 40000000000000000000000 * ((decoderGuard C).length + 2) ^ 25 := h
    _ ≤ 40000000000000000000000 * (18 * (C.word.length + 1)) ^ 25 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hg 25)
    _ = _ := by rw [mul_pow, Nat.mul_assoc]

end NearCubicGates.Adapters.Proximity
