import Proof.Amplification.RecoveryRawSATState

/-! The actual outer-clause field is copied into the old evaluator's code
bank; the valuation source and every other valuation field are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copied_extra_tapes (x : State) (bits : List Bool) (hw : bits.length=x.width) :
    (copied x bits).valuation.tapes (copied x bits).clause=x.valuation.tapes x.clause := by
  have hc := copied_capacity x bits hw
  simp only [RecoveryClauseEvaluation.Extra.tapes,copied]
  rw [hw,hc]
  rfl

theorem copied_clause_tapes (x : State) (bits : List Bool) (hw : bits.length=x.width) :
    RecoveryClauseEvaluation.tapes (copied x bits).clause (copied x bits).valuation=
      Function.update (Function.update (RecoveryClauseEvaluation.tapes x.clause x.valuation) 0 (frame bits))
        22 (List.replicate (max x.clause.capacity (4*bits.length+3)) false) := by
  have hc := RecoveryRawView.replace_core_tapes x.clause bits (max x.clause.capacity (4*bits.length+3))
    (copied_capacity x bits hw)
  change Fin.addCases (m:=28) (n:=14) (motive:=fun _=>List Bool) (copied x bits).clause.tapes
    ((copied x bits).valuation.tapes (copied x bits).clause)=_
  rw [copied_extra_tapes x bits hw]
  change Fin.addCases (m:=28) (n:=14) (motive:=fun _=>List Bool)
    ({x.clause with bits:=bits,capacity:=max x.clause.capacity (4*bits.length+3)} : RecoveryClauseState.State).tapes
    (x.valuation.tapes x.clause)=_
  rw [hc,bank_update_left,bank_update_left]
  rfl

theorem copied_tapes (x : State) (bits : List Bool) (hw : bits.length=x.width) :
    (copied x bits).tapes=
      Function.update (Function.update (Function.update x.tapes 64
        (List.replicate (max x.outer.capacity (2*bits.length+1)) false)) 0 (frame bits))
        22 (List.replicate (max x.clause.capacity (4*bits.length+3)) false) := by
  have ho := RecoveryRawView.reset_core_tapes x.outer (max x.outer.capacity (2*bits.length+1))
  change Fin.addCases (m:=42) (n:=28) (motive:=fun _=>List Bool)
    (RecoveryClauseEvaluation.tapes (copied x bits).clause (copied x bits).valuation)
    ({x.outer with capacity:=max x.outer.capacity (2*bits.length+1)} : RecoveryClauseState.State).tapes=_
  rw [copied_clause_tapes x bits hw,ho,bank_update_left,bank_update_left,bank_update_right]
  rfl

theorem copy_install (ambient : Fin 70→List Bool) (bits : List Bool) (capacity reset : Nat)
    (hf : ambient 66=frame bits) :
    install copySlots ambient ![frame bits,frame bits,List.replicate capacity false,List.replicate reset false]=
      Function.update (Function.update (Function.update ambient 64 (List.replicate capacity false)) 0 (frame bits))
        22 (List.replicate reset false) := by
  funext i
  by_cases hi : ∃ j,copySlots j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [install_slot copySlots copySlots_injective]
    fin_cases j
    · exact hf.symm
    · rfl
    · rfl
    · rfl
  · rw [install_other copySlots _ _ _ (by intro j hj; exact hi ⟨j,hj⟩)]
    have h0 : i≠(0 : Fin 70) := by intro he; exact hi ⟨1,he.symm⟩
    have h64 : i≠(64 : Fin 70) := by intro he; exact hi ⟨2,he.symm⟩
    have h22 : i≠(22 : Fin 70) := by intro he; exact hi ⟨3,he.symm⟩
    rw [Function.update_of_ne h22,Function.update_of_ne h0,Function.update_of_ne h64]

end NearCubicWires.RepairOrdinary.RecoveryRawSAT
