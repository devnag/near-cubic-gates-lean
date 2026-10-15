import Proof.Amplification.RecoveryRowStructureChildrenCopyTapes

/-! Paid child-key and left-count copies for the actual paired-row caller.
The large padded decoder output is read directly and preserved; the key
and saved-count outputs have the exact fixed width. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bankKey_valid (x : Children) (key word bits : List Bool) (hx : x.Valid word bits)
    (hw : key.length=x.base.state.bits.length) : (bankKey x key).Valid word bits := by
  exact ⟨hx.1,⟨⟨hx.2.1.1.1,hw.trans hx.2.1.2.1.symm,hx.2.1.1.2.2⟩,hx.2.1.2⟩,hx.2.2⟩

theorem leftSaved_valid (x : Children) (word bits : List Bool) (hx : x.Valid word bits) :
    (leftSaved x).Valid word bits :=
  ⟨setCode_valid x.base x.bank.saved word hx.1 (hx.2.2.2.1.trans hx.2.1.2.1).le,hx.2⟩

def childCopyTapes (source old : List Bool) (padding capacity reset : Nat) : Fin 4→List Bool :=
  ![ZeroPadding.pad padding (frame source),old,List.replicate capacity false,List.replicate reset false]

theorem padded_copy_ready (source old : List Bool) (padding capacity reset : Nat)
    (hold : old.length≤2*source.length+1) (hc : 2*source.length+1≤capacity) (hr : 4*source.length+3≤reset) :
    ReadyRun RecoveryRootRound.copyMachine (8*source.length+8)
      (childCopyTapes source old padding capacity reset)
      (childCopyTapes source (frame source) padding capacity reset) := by
  have hbase := RecoveryRootRound.copy_ready source old capacity reset hold
  rw [Nat.max_eq_left hc,Nat.max_eq_left hr] at hbase
  have h := RecoveryChildSelection.ReadyRun.pad hbase ![padding,0,0,0]
  have hin : (fun i : Fin 4=>ZeroPadding.pad (![padding,0,0,0] i)
      (![frame source,old,List.replicate capacity false,List.replicate reset false] i))=
      childCopyTapes source old padding capacity reset := by
    funext i
    fin_cases i <;> simp [childCopyTapes]
  have hout : (fun i : Fin 4=>ZeroPadding.pad (![padding,0,0,0] i)
      (![frame source,frame source,List.replicate capacity false,List.replicate reset false] i))=
      childCopyTapes source (frame source) padding capacity reset := by
    funext i
    fin_cases i <;> simp [childCopyTapes]
  rw [hin,hout] at h
  exact h

theorem key_copy_run (left : Bool) (x : Children) (key word bits : List Bool) (padding : Nat)
    (hx : x.Valid word bits) (hw : key.length=x.base.state.bits.length)
    (hsource : x.tapes (if left then 17 else 24)=ZeroPadding.pad padding (frame key)) :
    ∃ r,runFrom (keyCopyMachine left) (8*key.length+8) (x.cfg (keyCopyMachine left).start)=some r ∧
      r.final=(bankKey x key).cfg r.final.control ∧ r.steps=8*key.length+8 ∧ (bankKey x key).Valid word bits := by
  have hkey : x.bank.key.length=key.length := hx.2.1.1.2.1.trans (hx.2.1.2.1.trans hw.symm)
  have hold : (frame x.bank.key).length≤2*key.length+1 := by rw [frame_length,hkey]
  have hc : 2*key.length+1≤x.copyCapacity := by rw [hw]; exact hx.2.2.2.2.1
  have hr : 4*key.length+3≤x.base.state.capacity := by
    have hb := hx.1.2.1.reset
    change 8192*(x.base.state.bits.length+1)^2+1≤x.base.state.capacity at hb
    rw [hw]
    nlinarith
  have h := padded_copy_ready key (frame x.bank.key) padding x.copyCapacity x.base.state.capacity hold hc hr
  obtain ⟨r,hrun,hheads,htapes,hsteps⟩ := h.focus_at (keyCopySlots left) (keyCopySlots_injective left) x.heads x.tapes
    (by intro j; fin_cases j <;> cases left <;> first | exact hsource | rfl)
    (by intro j; fin_cases j <;> cases left <;> rfl)
  refine ⟨r,hrun,?_,hsteps,bankKey_valid x key word bits hx hw⟩
  apply configuration_ext
  · rfl
  · exact hheads
  · exact htapes.trans ((key_copy_output left x.tapes key padding x.copyCapacity x.base.state.capacity
      hsource (by rfl) (by rfl)).trans (bankKey_tapes x key).symm)

theorem save_count_run (x : Children) (word bits : List Bool) (hx : x.Valid word bits) :
    ∃ r,runFrom saveCountMachine (8*x.bank.saved.length+8) (x.cfg saveCountMachine.start)=some r ∧
      r.final=(leftSaved x).cfg r.final.control ∧ r.steps=8*x.bank.saved.length+8 ∧ (leftSaved x).Valid word bits := by
  have hw : x.bank.saved.length=x.base.state.bits.length := hx.2.2.2.1.trans hx.2.1.2.1
  have hold : (frame x.base.code).length≤2*x.bank.saved.length+1 := by
    rw [frame_length,hw]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hx.1.2.2.2.1) 1
  have hc : 2*x.bank.saved.length+1≤x.copyCapacity := by rw [hw]; exact hx.2.2.2.2.1
  have hr : 4*x.bank.saved.length+3≤x.base.state.capacity := by
    have hb := hx.1.2.1.reset
    change 8192*(x.base.state.bits.length+1)^2+1≤x.base.state.capacity at hb
    rw [hw]
    nlinarith
  have h := RecoveryRootRound.copy_ready x.bank.saved (frame x.base.code) x.copyCapacity x.base.state.capacity hold
  rw [Nat.max_eq_left hc,Nat.max_eq_left hr] at h
  obtain ⟨r,hrun,hheads,htapes,hsteps⟩ := h.focus_at saveCountSlots saveCountSlots_injective x.heads x.tapes
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hrun,?_,hsteps,leftSaved_valid x word bits hx⟩
  apply configuration_ext
  · rfl
  · exact hheads
  · exact htapes.trans ((save_count_output x.tapes x.bank.saved x.copyCapacity x.base.state.capacity
      (by rfl) (by rfl) (by rfl)).trans (leftSaved_tapes x).symm)

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
