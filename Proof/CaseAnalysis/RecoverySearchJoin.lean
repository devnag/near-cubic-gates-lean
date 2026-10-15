import Proof.CaseAnalysis.RecoverySearchLayout
import Proof.CaseAnalysis.RecoverySearchCompose

/-! Compose an actual ordinary graph producer with the completed oracle
search at symbolic state counts. Unused graph cursors are preserved. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedColdSearchJoin
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryExecution RecoveryRootRound
open RecoveryOracle RecoveryBoundedSearchGraphDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem run {u s : Nat} (first : Machine (1664+u) s) (fuel payload total B : Nat)
    (A : Fin (1664+u)→List Bool) (r : ExecutionReceipt (1664+u) s)
    (hr : LocalBitMultitape.run first fuel A=some r)
    (hp : r.final.tapes (payloadPort u)=frame payload.bits)
    (ha : r.final.tapes (arityPort u)=ZeroPadding.pad B (List.replicate total true))
    (hhp : r.final.heads (payloadPort u)=0) (hha : r.final.heads (arityPort u)=0) :
    ∃ cost ≤ fuel+2+1099511627776*(RecoveryPrefixCold.radius payload total)^3,∃ final,
      OrdinaryOracleTrace correctedSat (program first) cost
        (initialConfiguration (program first).base.machine
          (Fin.addCases (m:=1664+u) (n:=790) A (fun _=>[]))) final ∧
      (program first).base.machine.halted final.control=true ∧
      final.heads=Fin.addCases (m:=1664+u) (n:=790) r.final.heads (fun _=>0) ∧
      readTapeBit (final.tapes ((369 : Fin 790).natAdd (1664+u))) 0=
        correctedSat (RecoveryQuery.code true payload 0 0) ∧
      final.tapes ((787 : Fin 790).natAdd (1664+u))=
        frame (RecoveryPrefixBody.search true payload total []) ∧
      (final.tapes ((356 : Fin 790).natAdd (1664+u))).length ≤ cost ∧
      final.heads ((356 : Fin 790).natAdd (1664+u))=0 ∧
      (∀ i : Fin (1664+u),i≠payloadPort u → i≠arityPort u →
        final.tapes (old u i)=r.final.tapes i) := by
  let embedded:=TapeEmbedding.receipt (fun _ : Fin 790=>0) (fun _ : Fin 790=>[]) r
  have he:=TapeEmbedding.run_embed first (fun _ : Fin 790=>0) (fun _ : Fin 790=>[]) fuel _ r hr
  rw [RecoveryTseitinNative.Serialize.embedded_initial] at he
  obtain ⟨searchCost,searchBound,searched,searchTrace,searchHalt,searchHeads,flag,description,keep⟩:=
    RecoveryBoundedSearchGraphDock.run u payload total B r.final.heads r.final.tapes hp ha hhp hha
  obtain ⟨final,whole,halted,heads,tapes⟩:=RecoveryBoundedColdSearchCompose.run correctedSat
    (ports u) (TapeEmbedding.machine 790 first)
    (focused (RecoveryBoundedSearchExecution.program 1073741824) (slots u))
    fuel _ embedded he searchCost searched searchTrace searchHalt
  have support:=trace_support whole 0 (by intro i;rfl)
    (fun i=>(Fin.addCases (m:=1664+u) (n:=790) (motive:=fun _=>List Bool) A (fun _=>[]) i).length)
    (by intro i;exact Nat.le_max_left _ _)
  have queryBound:=(support ((356 : Fin 790).natAdd (1664+u))).2
  refine ⟨embedded.steps+(1+(searchCost+1)),?_,final,whole,halted,
    heads.trans searchHeads,?_,?_,?_,?_,?_⟩
  · have hs:=runFrom_steps_le first fuel _ r hr
    change r.steps+(1+(searchCost+1)) ≤ _
    omega
  · rw [tapes];exact flag
  · rw [tapes];exact description
  · simpa only [Fin.addCases_right,List.length_nil,Nat.zero_add,Nat.zero_max] using queryBound
  · rw [heads]
    exact (congrFun searchHeads _).trans (Fin.addCases_right (356 : Fin 790))
  · rw [tapes];exact keep

end NearCubicWires.RepairSource.RecoveryBoundedColdSearchJoin
