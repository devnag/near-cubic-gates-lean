import Proof.Amplification.RecoveryMarkerClauseState

/-! Literal paid calls for marker replay: outer-cell extraction, framed
clause-code copy, natural literal decoding, and an empty-clause test. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerClause
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copy_install (ambient : Fin 57→List Bool) (bits : List Bool) (capacity reset : Nat)
    (hf : ambient 53=frame bits) :
    install copySlots ambient ![frame bits,frame bits,List.replicate capacity false,List.replicate reset false]=
      Function.update (Function.update (Function.update ambient 51 (List.replicate capacity false)) 0 (frame bits))
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
    have h0 : i≠(0 : Fin 57) := by intro he; exact hi ⟨1,he.symm⟩
    have h51 : i≠(51 : Fin 57) := by intro he; exact hi ⟨2,he.symm⟩
    have h22 : i≠(22 : Fin 57) := by intro he; exact hi ⟨3,he.symm⟩
    rw [Function.update_of_ne h22,Function.update_of_ne h0,Function.update_of_ne h51]

theorem copy_ready (x : State) (bits : List Bool) (hw : bits.length=x.width)
    (hf : x.outer.fields 0=frame bits) :
    ReadyRun copyMachine (8*bits.length+8) x.tapes (copied x bits).tapes := by
  have hb : (frame x.inner.data.bits).length ≤ 2*bits.length+1 := by
    rw [frame_length,hw]
    exact Nat.le_refl _
  have h := (RecoveryRootRound.copy_ready bits (frame x.inner.data.bits) x.outer.capacity x.inner.data.capacity hb).focus
    copySlots copySlots_injective x.tapes (by
      intro j; fin_cases j
      · exact hf
      · rfl
      · rfl
      · rfl)
  have hi := copy_install x.tapes bits (max x.outer.capacity (2*bits.length+1))
    (max x.inner.data.capacity (4*bits.length+3)) hf
  rw [hi,←copied_tapes x bits hw] at h
  exact h

theorem outer_ready (x : State) (hx : x.outer.Valid) :
    ReadyRun outerMachine (RecoveryStoredListCell.time x.outer.bits) x.tapes (outerStep x).tapes := by
  obtain ⟨base,hr,ht,hh,hs⟩ := RecoveryClauseState.cell_ready x.outer 0 hx
  have hrun := RecoveryBankPair.right_run (RecoveryClauseState.machine 0) (RecoveryStoredListCell.time x.outer.bits)
    (initialConfiguration (RecoveryClauseState.machine 0) x.outer.tapes) base hr
    (fun _ : Fin 29=>0) x.inner.tapes
  obtain ⟨r,h,hsteps,hfinal⟩ := hrun
  have hi : RecoveryBankPair.cfg (fun _ : Fin 29=>0) x.inner.tapes
      (initialConfiguration (RecoveryClauseState.machine 0) x.outer.tapes).heads
      (initialConfiguration (RecoveryClauseState.machine 0) x.outer.tapes).tapes
      (initialConfiguration (RecoveryClauseState.machine 0) x.outer.tapes).control=initialConfiguration outerMachine x.tapes := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=29) (n:=28) (fun _=>?_) (fun _=>?_) i <;>
        simp [RecoveryBankPair.cfg,initialConfiguration]
    · rfl
  rw [hi] at h
  refine ⟨r,h,?_,?_,hsteps.trans hs⟩
  · rw [hfinal]
    change Fin.addCases (m:=29) (n:=28) (motive:=fun _=>List Bool) x.inner.tapes base.final.tapes=_
    rw [ht]
    rfl
  · intro i
    rw [hfinal]
    change Fin.addCases (m:=29) (n:=28) (motive:=fun _=>Nat) (fun _=>0) base.final.heads i=0
    refine Fin.addCases (m:=29) (n:=28) (fun _=>?_) (fun j=>?_) i
    · simp only [Fin.addCases_left]
    · simpa only [Fin.addCases_right] using hh j

theorem empty_ready (x : State) (hx : x.inner.data.Valid) :
    ReadyRun emptyMachine (RecoveryStoredListCell.time x.inner.data.bits) x.tapes (emptyStep x).tapes :=
  ((RecoveryClauseState.cell_ready x.inner.data 0 hx).embed (fun _ : Fin 1=>[x.inner.present])).embed x.outer.tapes

theorem literal_run (x : State) (hx : x.inner.data.Valid) :
    ∃ r,runFrom literalMachine (RecoveryRawLiteral.cost x.inner) (x.cfg literalMachine.start)=some r ∧
      r.final=(literalStep x).cfg r.final.control ∧ r.steps ≤ RecoveryRawLiteral.cost x.inner := by
  have hrun := RecoveryRawLiteral.literal_run x.inner hx
  obtain ⟨base,hr,hf,hs,_⟩ := hrun
  have h := TapeEmbedding.run_embed RecoveryRawLiteral.machine (fun _ : Fin 28=>0) x.outer.tapes
    (RecoveryRawLiteral.cost x.inner) _ base hr
  have hi : TapeEmbedding.config (fun _ : Fin 28=>0) x.outer.tapes
      (x.inner.cfg RecoveryRawLiteral.machine.start)=x.cfg literalMachine.start := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=29) (n:=28) (fun _=>?_) (fun _=>?_) i <;>
        simp [TapeEmbedding.config,RecoveryRawLiteral.State.cfg,State.cfg]
    · rfl
  rw [hi] at h
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 28=>0) x.outer.tapes base,h,?_,hs⟩
  change TapeEmbedding.config (fun _ : Fin 28=>0) x.outer.tapes base.final=_
  rw [hf]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=29) (n:=28) (fun _=>?_) (fun _=>?_) i <;>
      simp [TapeEmbedding.config,RecoveryRawLiteral.State.cfg,State.cfg]
  · rfl

end NearCubicWires.RepairOrdinary.RecoveryMarkerClause
