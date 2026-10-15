import Proof.CaseAnalysis.RecoveryQueryRewind

/-! Full61-bank query-list output and the two coarse stream dominations.
The same retained references enter the original clause compiler. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueries
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bankHeads (out : List Bool) (pos : ℕ) (refs : List Bool) : Fin 61→ℕ:=
  Fin.addCases (m:=60) (n:=1) (motive:=fun _=>ℕ) (RecoveryBoundedQuery.heads out pos refs) (fun _=>1)
def bankData (base C D F L : ℕ) (out : List Bool) (n total : ℕ) (source refs : List Bool) (queries : ℕ) : Fin 61→List Bool:=
  Fin.addCases (m:=60) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryBoundedQuery.data 6 base C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] n total source refs)
    (fun _=>CompareMachine.word queries)

theorem configuration_heads {n bound : ℕ} (phase : Fin 5) (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total W D L : ℕ) (out pre source refs : List Bool) (queries : ℕ) :
    (configuration phase b total W D L out pre source refs queries 1).heads=bankHeads out pre.length refs := by rfl
theorem configuration_tapes {n bound : ℕ} (phase : Fin 5) (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total W D L : ℕ) (out pre source refs : List Bool) (queries : ℕ) :
    (configuration phase b total W D L out pre source refs queries 1).tapes=
      bankData b.nodes.length (capacity W) D (OuterPCPRecovery.boundedCircuitFieldLimit n bound) L out n total source refs queries := by rfl
theorem initial_config {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total W D L : ℕ) (out source : List Bool) (queries : ℕ) :
    configuration 0 b total W D L out [] source [] queries 1=
      (⟨machine.start,bankHeads out 0 [],bankData b.nodes.length (capacity W) D
        (OuterPCPRecovery.boundedCircuitFieldLimit n bound) L out n total source [] queries⟩ : Configuration 61 _) := by
  apply configuration_ext
  · rfl
  · rfl
  · rfl
theorem rewound_heads (out refs : List Bool) (pos : ℕ) :
    RecoveryBoundedQueryRewind.heads (RecoveryBoundedQueryRewind.heads (bankHeads out pos refs) false) true=
      bankHeads out 0 [] := by
  funext i
  fin_cases i <;> rfl

theorem addressWord_length {n : ℕ} (addresses : List (BitInput n)) :
    (addressWord addresses).length=addresses.length*n := by
  induction addresses with
  | nil=>simp only [addressWord,List.flatMap_nil,List.length_nil,Nat.zero_mul]
  | cons address addresses ih=>
    rw [addressWord_cons,List.length_append,List.length_ofFn,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
theorem references_length {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total : ℕ) (ht : total ≤ bound) (addresses : List (BitInput n)) :
    (references b total ht addresses).length=addresses.length := by
  simp only [references,List.length_map,compileUniversalOutputs_values_length]

theorem streams_fit {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (total W : ℕ) (ht : total ≤ bound) (addresses : List (BitInput n))
    (hn : n ≤ W) (hq : addresses.length ≤ W)
    (hg : (compileUniversalOutputs b total ht addresses).final.nodes.length ≤ W) :
    (addressWord addresses).length ≤ capacity W ∧
      (sourceWord (references b total ht addresses)).length ≤ capacity W := by
  constructor
  · rw [addressWord_length]
    have hm:=Nat.mul_le_mul hq hn
    unfold capacity
    nlinarith [Nat.zero_le (W^2)]
  · have hr : ∀ r∈references b total ht addresses,r≤W := by
      intro r hmem
      obtain ⟨w,_,rfl⟩:=List.mem_map.mp hmem
      exact w.output.isLt.le.trans hg
    have hs:=RecoveryBoundedTableReferenceReset.source_length_bound (references b total ht addresses) W hr
    rw [references_length] at hs
    have hm:=Nat.mul_le_mul_right (2*W+1) hq
    unfold capacity
    nlinarith [Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueries
