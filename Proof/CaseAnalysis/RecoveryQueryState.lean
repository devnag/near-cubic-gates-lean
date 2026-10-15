import Proof.CaseAnalysis.RecoveryQueryIteration

/-! Exact original query-list recursion and the retained physical entry.
The outer query driver is separate from the fixed per-query table driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueries
open LocalBitMultitape RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def addressWord {n : ℕ} (addresses : List (BitInput n)):=addresses.flatMap List.ofFn
def native {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total : ℕ) (ht : total ≤ bound) (addresses : List (BitInput n)):=
  (compileUniversalOutputs b total ht addresses).extension.suffix.flatMap PCPPRequestNodeSchema.native
def references {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total : ℕ) (ht : total ≤ bound) (addresses : List (BitInput n)):=
  (compileUniversalOutputs b total ht addresses).values.map (fun w=>w.output.val)
def Fits {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total W : ℕ) (ht : total ≤ bound) : List (BitInput n)→Prop
  | []=>True
  | address::rest=>RecoveryBoundedTable.Fits b address total W ht ∧
    RecoveryBoundedTableOutput.Fits b address total W ht ∧
    Fits (compileUniversalOutput b address total ht).compiled.final total W ht rest

noncomputable def entry {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total W D L : ℕ) (out pre source refs : List Bool):=
  (⟨RecoveryBoundedQuery.machine.start,RecoveryBoundedQuery.heads out pre.length refs,
    RecoveryBoundedQuery.data 6 b.nodes.length (capacity W) D 0 (OuterPCPRecovery.boundedCircuitFieldLimit n bound) 0 L out
      (ZeroPadding.pad (capacity W) []) (6+OuterPCPRecovery.boundedCircuitFieldLimit n bound) 0 [] n total source refs⟩ : Configuration 60 _)

theorem addressWord_cons {n : ℕ} (address : BitInput n) (rest : List (BitInput n)) :
    addressWord (address::rest)=List.ofFn address++addressWord rest := by rfl
theorem native_cons {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total : ℕ) (ht : total ≤ bound) (address : BitInput n) (rest : List (BitInput n)) :
    native b total ht (address::rest)=
      (compileUniversalOutput b address total ht).compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native++
      native (compileUniversalOutput b address total ht).compiled.final total ht rest := by
  change List.flatMap PCPPRequestNodeSchema.native (_++_)=_
  rw [List.flatMap_append]
  rfl
theorem references_cons {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total : ℕ) (ht : total ≤ bound) (address : BitInput n) (rest : List (BitInput n)) :
    references b total ht (address::rest)=(compileUniversalOutput b address total ht).compiled.output.val::
      references (compileUniversalOutput b address total ht).compiled.final total ht rest := by rfl
theorem final_cons {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total : ℕ) (ht : total ≤ bound) (address : BitInput n) (rest : List (BitInput n)) :
    (compileUniversalOutputs b total ht (address::rest)).final=
      (compileUniversalOutputs (compileUniversalOutput b address total ht).compiled.final total ht rest).final := by rfl

theorem query_step {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total W D L : ℕ) (out pre tail refs : List Bool) (ht : total ≤ bound)
    (hfit : RecoveryBoundedTable.Fits b address total W ht)
    (hout : RecoveryBoundedTableOutput.Fits b address total W ht) (hn : n ≤ W)
    (hD : 8388608*(W+1)^3 ≤ D) (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    let source:=pre++List.ofFn address++tail
    let compiled:=compileUniversalOutput b address total ht
    let next:=entry compiled.compiled.final total W D L
      (out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native)
      (pre++List.ofFn address) source (refs++frame (List.replicate compiled.compiled.output.val true))
    ∃ r,runFrom RecoveryBoundedQuery.machine (RecoveryBoundedQuery.budget W)
      (entry b total W D L out pre source refs)=some r ∧
      r.steps ≤ RecoveryBoundedQuery.budget W ∧ r.final.heads=next.heads ∧ r.final.tapes=next.tapes := by
  obtain ⟨r,hr,rs,rh,rt⟩:=RecoveryBoundedQuery.query_run b address total W D L out pre tail refs ht hfit hout hn hD hL
  refine ⟨r,hr,rs,?_,rt⟩
  change r.final.heads=RecoveryBoundedQuery.heads _ (pre++List.ofFn address).length _
  rw [List.length_append,List.length_ofFn]
  exact rh

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueries
