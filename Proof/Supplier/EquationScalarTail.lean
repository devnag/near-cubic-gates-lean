import Proof.Supplier.EquationScalarGraph

/-! Actual zero scan and canonical signed frame emission in the common graph. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar.Graph
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def scanned (a : Fin 12→List Bool) (bits : List Bool) := install scanSlots a (Scan.output bits)
def finished (negate : Bool) (a : Fin 12→List Bool) (bits : List Bool) (sign : Bool) :=
  install emitSlots (scanned a bits) (Emit.output negate bits sign (DecompositionBitFields.present bits))

theorem finished_source (negate : Bool) (a : Fin 12→List Bool) (bits : List Bool) (sign : Bool) :
    finished negate a bits sign 0=a 0 := by simp [finished,scanned,install,pick_emit,pick_scan]
theorem finished_output (negate : Bool) (a : Fin 12→List Bool) (bits : List Bool) (sign : Bool) :
    finished negate a bits sign 9=frame (Emit.negative negate sign (DecompositionBitFields.present bits)::bits) := by
  simp [finished,install,pick_emit,Emit.output]

theorem tail (negate : Bool) (a : Fin 12→List Bool) (bits : List Bool) (sign : Bool)
    (hmag : a 2=frame bits) (hsign : a 1=[sign])
    (h6 : a 6=[]) (h7 : a 7=[false]) (h8 : a 8=[]) (h9 : a 9=[]) (h11 : a 11=[]) :
    Timed (machine negate) (12*bits.length+16) (entry negate 3 a)
      (RecoveryCalls.stopped sizes (fun _=>0) (finished negate a bits sign)) := by
  have hscan : ReadyRun (programs negate 3) (8*bits.length+4) a (scanned a bits) :=
    (Scan.ready bits).focus scanSlots (by decide) a (by
      intro i; fin_cases i <;> simp [scanSlots,Scan.input,hmag,h6,h7,h8])
  have hemit : ReadyRun (programs negate 4) (4*bits.length+10) (scanned a bits)
      (finished negate a bits sign) :=
    (Emit.ready negate bits sign (DecompositionBitFields.present bits)).focus emitSlots (by decide) _ (by
      intro i; fin_cases i <;>
        simp [emitSlots,scanned,install,pick_scan,Scan.output,Emit.input,hsign,h9,h11])
  have hc := hscan.call sizes (programs negate) 0 (next negate) 3 4 (by intro q; rfl)
  have he := hemit.stop sizes (programs negate) 0 (next negate) 4 (by intro q; rfl)
  have h := hc.trans he
  have ht : (8*bits.length+4+1)+(4*bits.length+10+1)=12*bits.length+16 := by omega
  rw [ht] at h
  exact h

end
end NearCubicWires.RepairOrdinary.EquationScalar.Graph
