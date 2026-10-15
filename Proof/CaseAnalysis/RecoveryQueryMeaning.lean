import Proof.CaseAnalysis.RecoveryQueryState

/-! Opaque enclosing query-list identity keeps the original recursion and
list associativity out of the physical repeat controller's large bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueries
open LocalBitMultitape RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem final_entry_cons {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total W D L : ℕ) (out pre source refs : List Bool) (ht : total ≤ bound)
    (address : BitInput n) (rest : List (BitInput n)) :
    let head:=compileUniversalOutput b address total ht
    let tail:=compileUniversalOutputs head.compiled.final total ht rest
    entry tail.final total W D L
      ((out++head.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native)++native head.compiled.final total ht rest)
      ((pre++List.ofFn address)++addressWord rest) source
      ((refs++frame (List.replicate head.compiled.output.val true))++sourceWord (references head.compiled.final total ht rest))=
    entry (compileUniversalOutputs b total ht (address::rest)).final total W D L
      (out++native b total ht (address::rest)) (pre++addressWord (address::rest)) source
      (refs++sourceWord (references b total ht (address::rest))) := by
  dsimp only
  rw [final_cons,native_cons,references_cons,addressWord_cons]
  simp only [sourceWord,List.flatMap_cons,List.append_assoc]

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueries
