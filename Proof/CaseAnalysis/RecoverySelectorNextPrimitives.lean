import Proof.CaseAnalysis.RecoverySelectorState

/-! Exact output bytes and fixed restoration ports of the repeated original
selector. These describe the checked body; they add no machine operations. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nextOut {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value ref : ℕ) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :=
  out++((compileExpr b (unaryEqualsExpr row start limit value hblock)).extension.suffix).flatMap
    PCPPRequestNodeSchema.native++PCPPNativeClauseBank.nodeBits 3 0 3 0 1
      (RecoveryBoundedNativeFold.values ref (RecoveryBoundedSelectorJoin.counter b row start limit value hblock))

theorem condition_output {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value : ℕ) (hblock : start+limit ≤ rowWidth n bound) :
    (compileExpr b (unaryEqualsExpr row start limit value hblock)).output.val=
      RecoveryBoundedSelectorJoin.counter b row start limit value hblock := by
  rw [compileExpr_output,unary_expression,all_nodeCount]
  have hl : (unaryItems row start limit value hblock).length=limit := by simp [unaryItems]
  rw [hl]
  unfold RecoveryBoundedSelectorJoin.counter
  omega

theorem nextOut_eq {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value : ℕ) (wire : LiveWire b) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :
    nextOut b row start limit value wire.output.val out hblock=
      out++(head b (unaryEqualsExpr row start limit value hblock) wire).extension.suffix.flatMap
        PCPPRequestNodeSchema.native := by
  rw [head_suffix,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    condition_output]
  simp [nextOut,PCPPNativeClauseBank.nodeBits,RecoveryBoundedNativeFold.values,
    PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.append_assoc]

theorem restore_pick (i : Fin 42) :
    RecoveryFocus.pick restoreSlots i=
      if i=1 then some 0 else if i=41 then some 1 else if i=36 then some 2 else if i=29 then some 3 else if i=34 then some 4 else if i=32 then some 5 else if i=22 then some 6 else if i=23 then some 7 else none := by
  by_cases h0 : i=1
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot restoreSlots (by decide) 0
  rw [if_neg h0]
  by_cases h1 : i=41
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot restoreSlots (by decide) 1
  rw [if_neg h1]
  by_cases h2 : i=36
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot restoreSlots (by decide) 2
  rw [if_neg h2]
  by_cases h3 : i=29
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot restoreSlots (by decide) 3
  rw [if_neg h3]
  by_cases h4 : i=34
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot restoreSlots (by decide) 4
  rw [if_neg h4]
  by_cases h5 : i=32
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot restoreSlots (by decide) 5
  rw [if_neg h5]
  by_cases h6 : i=22
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot restoreSlots (by decide) 6
  rw [if_neg h6]
  by_cases h7 : i=23
  · subst i
    rw [if_pos rfl]
    exact RecoveryFocus.pick_slot restoreSlots (by decide) 7
  rw [if_neg h7]
  have hn : ¬∃ j,restoreSlots j=i := by
    rintro ⟨j,hj⟩
    fin_cases j
    · exact h0 hj.symm
    · exact h1 hj.symm
    · exact h2 hj.symm
    · exact h3 hj.symm
    · exact h4 hj.symm
    · exact h5 hj.symm
    · exact h6 hj.symm
    · exact h7 hj.symm
  simp only [RecoveryFocus.pick,dif_neg hn]

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
