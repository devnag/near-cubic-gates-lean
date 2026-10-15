import Proof.Amplification.RecoverySourceClauseReadLayout

/-! One actual native source-field read, proved at the seven-tape ambient
cursor. Concrete configuration layouts are checked separately. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseRead
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem phase_run (pre : List Bool) (bits : Fin 3→List Bool) (suffix : List Bool) (k : Fin 3) : ∃ r,
    runFrom (phase k) (4*(bits k).length+4) (cfg (phase k).start pre bits suffix k.castSucc)=some r ∧
      r.final=cfg r.final.control pre bits suffix k.succ ∧ r.steps=4*(bits k).length+4 := by
  obtain ⟨base,hbase,bt,bh,bs⟩ := PCPFieldMoves.advance_run (pre++prefixes bits k.castSucc) (bits k) (suffixes bits suffix k) 0 0
  have hin : ∀ j,(cfg (phase k).start pre bits suffix k.castSucc).tapes (slots k j)=
      (PCPFieldMoves.entry (pre++prefixes bits k.castSucc) (bits k) (suffixes bits suffix k) 0 0).tapes j := by
    intro j
    fin_cases j
    · change source pre bits suffix=_
      rw [source_split pre bits suffix k]
      exact (ZeroPadding.pad_zero _).symm
    all_goals fin_cases k <;> rfl
  have hheads : ∀ j,(cfg (phase k).start pre bits suffix k.castSucc).heads (slots k j)=
      (PCPFieldMoves.entry (pre++prefixes bits k.castSucc) (bits k) (suffixes bits suffix k) 0 0).heads j := by
    intro j; fin_cases j
    · rfl
    all_goals fin_cases k <;> rfl
  obtain ⟨r,hr,_rc,rs,rh,rt,ro⟩ := RecoveryFocus.dock (slots k) (slots_injective k)
    PCPFieldMoves.advanceMachine (4*(bits k).length+4)
    (cfg (phase k).start pre bits suffix k.castSucc).heads
    (cfg (phase k).start pre bits suffix k.castSucc).tapes
    _ hheads hin base hbase
  refine ⟨r,hr,?_,rs.trans bs⟩
  apply configuration_ext
  · rfl
  · exact heads_done pre bits suffix k r.final.heads
      (by rw [rh,bh]; rfl) (by rw [rh,bh]; rfl) (by rw [rh,bh]; rfl)
      (fun i hi=>(ro i hi).1)
  · exact tapes_done pre bits suffix k r.final.tapes
      (by rw [rt,bt]; exact (source_split pre bits suffix k).symm)
      (by rw [rt,bt]; exact ZeroPadding.pad_zero _)
      (by rw [rt,bt]; rfl) (fun i hi=>(ro i hi).2)

end NearCubicWires.RepairSource.RecoverySourceClauseRead
