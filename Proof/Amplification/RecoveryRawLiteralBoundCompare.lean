import Proof.Amplification.RecoveryRawLiteralBoundState

/-! Paid binary index comparison inside the raw inspector. Only the four
selected heads are reset; the retained witness cursor is unchanged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteralBound
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem compared_tapes {s : Nat} (x : State) (index : List Bool) (q : Fin s) :
    ((compared x index).cfg q).tapes=Function.update (x.cfg q).tapes 32
      [decide (RadixSemantics.value x.bound ≤ RadixSemantics.value index)] := by
  funext i
  refine Fin.addCases (m:=31) (n:=4) (motive:=fun i=>
    ((compared x index).cfg q).tapes i=Function.update (x.cfg q).tapes 32
      [decide (RadixSemantics.value x.bound ≤ RadixSemantics.value index)] i) ?_ ?_ i
  · intro j
    have hj : j.castAdd 4≠(32 : Fin 35) := by intro h; have hv:=congrArg Fin.val h; simp at hv; omega
    simp only [Function.update_of_ne hj,State.cfg,TapeEmbedding.config,Fin.addCases_left]
    rfl
  · intro j; fin_cases j <;> rfl

theorem compare_run (x : State) (index : List Bool)
    (hf : x.stream.data.data.fields 0=frame index)
    (hw : x.bound.length=index.length)
    (hc : 2*x.bound.length+3 ≤ x.stream.data.data.capacity) :
    ∃ r,runFrom compareMachine (4*x.bound.length+8) (x.cfg compareMachine.start)=some r ∧
      r.final=(compared x index).cfg r.final.control ∧ r.steps=4*x.bound.length+8 := by
  have h := RecoveryPrefixCompare.compare_ready x.bound index x.bad x.stream.data.data.capacity hw
  rw [Nat.max_eq_left hc] at h
  obtain ⟨r,hr,hh,ht,hs⟩ := h.focus_at slots slots_injective
    (x.cfg compareMachine.start).heads (x.cfg compareMachine.start).tapes
    (by intro j; fin_cases j
        · rfl
        · exact hf
        · rfl
        · rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,?_,hs⟩
  apply configuration_ext
  · rfl
  · exact hh
  · rw [ht,compared_tapes]
    funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [install_slot slots slots_injective]
      fin_cases j
      · rfl
      · exact hf.symm
      · rfl
      · rfl
    · rw [install_other slots _ _ _ (by intro j hj; exact hi ⟨j,hj⟩)]
      have hn : i≠(32 : Fin 35) := by intro he; exact hi ⟨2,he.symm⟩
      rw [Function.update_of_ne hn]
      rfl

end NearCubicWires.RepairOrdinary.RecoveryRawLiteralBound
