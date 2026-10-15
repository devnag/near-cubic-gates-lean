import Proof.Amplification.RecoveryMarkerHandoffState

/-! Actual marker-to-checker metadata copies. Only the four selected local
heads must start at zero; the table cursors and count drivers are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def oldWord (x : CheckState) : Fin 3→List Bool :=
  ![x.outer.key,x.inner.base.extra.committed,x.inner.base.extra.binaryCount]
theorem selected_source (marker : MarkerState) (x : CheckState) (which : Fin 3) :
    tapes marker x (source which)=marker.tapes (RecoveryMarkerSave.target which) := by
  fin_cases which <;> rfl
theorem selected_target (marker : MarkerState) (x : CheckState) (which : Fin 3) :
    tapes marker x (target which)=frame (oldWord x which) := by fin_cases which <;> rfl
theorem copy_heads (x : CheckState) (which : Fin 3) (j : Fin 4) : heads x (slots which j)=0 := by
  fin_cases which <;> fin_cases j <;> rfl

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem copy_run (marker : MarkerState) (x : CheckState) (which : Fin 3) (word : List Bool)
    (hsource : marker.tapes (RecoveryMarkerSave.target which)=frame word)
    (hback : (oldWord x which).length ≤ word.length)
    (hcopy : 2*word.length+1 ≤ x.inner.copyCapacity)
    (hreset : 4*word.length+3 ≤ x.inner.base.state.capacity) :
    ∃ r,runFrom (copyMachine which) (8*word.length+8) (cfg marker x (copyMachine which).start)=some r ∧
      r.final=cfg marker (stored x which word) r.final.control ∧ r.steps=8*word.length+8 := by
  have h := RecoveryRootRound.copy_ready word (frame (oldWord x which))
    x.inner.copyCapacity x.inner.base.state.capacity (by rw [frame_length]; omega)
  rw [Nat.max_eq_left hcopy,Nat.max_eq_left hreset] at h
  obtain ⟨r,hr,hh,ht,hs⟩ := h.focus_at (slots which) (slots_injective which) (heads x) (tapes marker x)
    (by
      intro j
      fin_cases j
      · exact (selected_source marker x which).trans hsource
      · exact selected_target marker x which
      · rfl
      · rfl) (copy_heads x which)
  have he : install (slots which) (tapes marker x)
      ![frame word,frame word,List.replicate x.inner.copyCapacity false,List.replicate x.inner.base.state.capacity false]=
      Function.update (tapes marker x) (target which) (frame word) := by
    apply install_eq (slots which) (slots_injective which)
    · intro j
      fin_cases j
      · have hn : source which≠target which := by fin_cases which <;> decide
        change frame word=Function.update (tapes marker x) (target which) (frame word) (source which)
        rw [Function.update_of_ne hn,selected_source,hsource]
      · change frame word=Function.update (tapes marker x) (target which) (frame word) (target which)
        rw [Function.update_self]
      · have hn : (108 : Fin 212)≠target which := by fin_cases which <;> decide
        change _=Function.update (tapes marker x) (target which) (frame word) 108
        rw [Function.update_of_ne hn]
        rfl
      · have hn : (79 : Fin 212)≠target which := by fin_cases which <;> decide
        change _=Function.update (tapes marker x) (target which) (frame word) 79
        rw [Function.update_of_ne hn]
        rfl
    · intro i hi
      have hn : i≠target which := by intro h; exact hi 1 h.symm
      rw [Function.update_of_ne hn]
  refine ⟨r,hr,?_,hs⟩
  apply configuration_ext
  · rfl
  · exact hh.trans (stored_heads x which word).symm
  · exact ht.trans (he.trans (stored_ambient marker x which word).symm)

end NearCubicWires.RepairOrdinary.RecoveryMarkerHandoff
