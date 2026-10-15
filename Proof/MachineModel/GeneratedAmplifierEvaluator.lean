import Proof.MachineModel.GeneratedAmplifierRuntime

/-! The literal generated-table evaluator, with the required linear
input-length times address-width bound. The result is a RAW singleton;
only the ordinary input carrier is additionally framed. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier
open LocalBitMultitape RadixSemantics SourceInterfaces ExecutableInterfaces RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem runtime_bound {n : ℕ} (f : BoolFunction n) (address : BitInput n) :
    Runtime.budget f address≤128*(payload f address).length*(n+1)+128 := by
  let L := (payload f address).length
  have hp : n+1≤2^n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hlen := payload_length f address
  have ht : 2^n≤L := by dsimp only [L]; omega
  have hn : n≤L := by omega
  have hw : n.bits.length≤n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hm : n*n.bits.length≤L*(n+1) := Nat.mul_le_mul hn (by omega)
  have hi : value (List.ofFn address)+1≤L := (Nat.succ_le_of_lt (address_lt address)).trans ht
  have hl := Nat.mul_le_mul_right (4*n+7) hi
  have he : (frame n.bits++(boolFunctionTable f++frame (List.ofFn address))).length=L := by
    simp only [L,payload,List.append_assoc]
  change Runtime.budget f address≤128*L*(n+1)+128
  simp only [Runtime.budget,Entry.budget,Prepared.budget,Arity.budget,MatrixUnaryTemplate.budget,
    Lookup.cost,he]
  nlinarith

noncomputable def evaluator {c d : ℕ} (amplifier : ScheduleAmplifier c d) : GeneratedAmplifierEvaluator amplifier where
  coefficient := 128
  coefficientPositive := by decide
  evaluator := {
    program := Runtime.program
    realizes := by
      intro request
      let f := (amplifier.output request.sourceArity request.sourceFunction).function
      obtain ⟨r,hr,_,hout,_⟩ := Runtime.runtime_run f request.address
      have hb := runtime_bound f request.address
      have hm := run_moreFuel Runtime.machine (Runtime.budget f request.address)
        (128*(payload f request.address).length*
          ((amplifier.output request.sourceArity request.sourceFunction).arity+1)+128-
          Runtime.budget f request.address) _ r hr
      rw [Nat.add_sub_of_le hb] at hm
      have hi : Entry.input (payload f request.address)=Runtime.program.inputTapes (generatedAmplifierInput request) := by
        funext i
        simp only [Entry.input,Program.inputTapes,Fin.ext_iff,Fin.val_zero,generated_input]
        rfl
      rw [hi] at hm
      exact ⟨r,hm,hout⟩ }

theorem evaluator_exists {c d : ℕ} (amplifier : ScheduleAmplifier c d) :
    Nonempty (GeneratedAmplifierEvaluator amplifier) := ⟨evaluator amplifier⟩

end NearCubicWires.RepairOrdinary.GeneratedAmplifier
