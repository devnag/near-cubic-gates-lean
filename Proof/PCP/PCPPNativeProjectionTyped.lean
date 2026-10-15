import Proof.PCP.PCPPNativeProjectionLookupTemplate
import Proof.Amplification.RecoveryUnpairCode

/-! The executed retained-row lookup is specialized to the source's exact
projection code. The returned kind and index are the fields used by the
finite input-node emitter; no unary expansion of the paired code occurs. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeProjectionTyped
open LocalBitMultitape RadixSemantics SourceInterfaces RepairSource
open ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def kind {r : ℕ} : ProjectedRandomBit r → Fin 5
  | .bit _ => 0
  | .negatedBit _ => 1
  | .constant _ => 2
def index {r : ℕ} : ProjectedRandomBit r → ℕ
  | .bit i => i.val
  | .negatedBit i => i.val
  | .constant b => b.toNat

theorem decoded {r : ℕ} (p : ProjectedRandomBit r) :
    Nat.unpair (value (projectionCode p).bits)=((kind p).val,index p) := by
  rw [RecoveryUnpair.bits_value]
  cases p <;> simp only [projectionCode,kind,index,Nat.unpair_pair] <;> rfl

theorem lookup_run {r : ℕ} (pre : List Bool) (skipped : List (List Bool))
    (p : ProjectedRandomBit r) (suffix : List Bool) :
    ∃ result,runFrom PCPPNativeProjectionLookup.machine
      (PCPPNativeProjectionLookup.budget skipped (projectionCode p).bits)
      (PCPPNativeProjectionLookup.templateEntry
        (pre++FieldList.stream skipped++frame (projectionCode p).bits++suffix)
        pre.length skipped.length)=some result ∧
      result.steps ≤ PCPPNativeProjectionLookup.budget skipped (projectionCode p).bits ∧
      result.final.tapes 0=pre++FieldList.stream skipped++frame (projectionCode p).bits++suffix ∧
      result.final.heads 0=pre.length+(FieldList.stream skipped).length+2*(projectionCode p).bits.length+1 ∧
      result.final.tapes 2=UnaryTemplate.tape skipped.length ∧ result.final.heads 2=1 ∧
      result.final.tapes 22=CompareMachine.word (kind p).val ∧
      result.final.tapes 26=CompareMachine.word (index p) ∧
      result.final.heads 22=1 ∧ result.final.heads 26=1 := by
  simpa only [decoded] using PCPPNativeProjectionLookup.template_run pre skipped (projectionCode p).bits suffix

end NearCubicWires.RepairOrdinary.PCPPNativeProjectionTyped
