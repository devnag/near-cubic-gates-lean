import Proof.Amplification.RecoveryTseitinLoop
import Proof.Amplification.RecoveryTseitinWidth

/-! Whole original tautology-prefix stream, including actual binary index
updates. One input-length-derived quadratic capacity discharges every cell's
local bound. The unary loop/capacity drivers remain physical caller data. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinKernel CircuitInputCNF ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def uniformCapacity (total : Nat) := 8388608*(natBitLength total+1)^2

theorem index_capacity (index total : Nat) (hi : index ≤ total) : capacity index ≤ uniformCapacity total := by
  exact RecoveryTseitin.capacity_bound (Prepare.literals signs (fun _=>index)) (natBitLength total)
    (by unfold natBitLength; omega) (fun _=>Nat.add_le_add_right (Nat.log_mono_right hi) 1)

theorem emitted_snoc (index count : Nat) :
    emitted index (count+1)=emitted index count++RepairOrdinary.frame (word (index+count)) := by
  induction count generalizing index with
  | zero => simp only [emitted,List.append_nil,List.nil_append,Nat.add_zero]
  | succ count ih =>
    have he : index+1+count=index+(count+1) := by omega
    simpa only [emitted,he,List.append_assoc] using
      congrArg (fun xs=>RepairOrdinary.frame (word index)++xs) (ih (index+1))

theorem emitted_original (count : Nat) :
    emitted 0 count=RecoveryFormulaPayload.input (circuitInputTautologies count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [emitted_snoc,ih]
    simp only [circuitInputTautologies,RecoveryFormulaPayload.input,RecoveryFormulaPayload.fields,
      FieldList.stream,List.map_append,List.flatten_append,List.map_cons,List.map_nil,List.flatten_cons,
      List.flatten_nil,List.append_nil,Nat.zero_add,word]

theorem stream_run (cap count : Nat) (ambient : Fin 239→List Bool) (out : List Bool)
    (hcap : uniformCapacity count ≤ cap) (hv : Valid cap 0 ambient) :
    ∃ after : Fin 239→List Bool,∃ r,
      runFrom loopMachine (count*(24*cap+19)+3)
        (loopCfg 0 cap ambient out count 1)=some r ∧
      r.final=loopCfg 3 cap after
        (out++RecoveryFormulaPayload.input (circuitInputTautologies count)) count 1 ∧
      Valid cap count after ∧
      (∀ i : Fin 239,1 ≤ i.val → i.val<3 → after i=ambient i) ∧
      r.steps ≤ count*(24*cap+19)+3 := by
  have h := remaining_run cap 0 count ambient out count 0 (by omega) hv (by
    intro j hj
    exact (index_capacity (0+j) count (by omega)).trans hcap)
  have he : count*(bodyBudget cap+2)+count+3=count*(24*cap+19)+3 := by
    simp only [bodyBudget,Nat.mul_add]
    omega
  simpa only [he,Nat.zero_add,emitted_original] using h

end NearCubicWires.RepairSource.RecoveryTseitinTautology
