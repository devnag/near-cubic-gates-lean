import Proof.CaseAnalysis.RecoveryRowLoopClear

/-! Advance the original little-endian randomness field in place while
retaining the exact reusable row bank and its graph/stack append cursors. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open LocalBitMultitape RecoveryRootRound SourceInterfaces RepairSource CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def incrementMachine:=RecoveryFocus.machine projectionSlots RecoveryPCPFormulaResumeRandomness.machine

theorem projection_install (A : Fin 78→List Bool) (P Q : Fin 37→List Bool) :
    install projectionSlots (data A P) Q=data A Q := by
  funext i
  refine Fin.addCases (m:=78) (n:=37) (fun j=>?_) (fun j=>?_) i
  · change install _ _ _ (rowSlots j)=data _ _ (rowSlots j)
    rw [install_other _ _ _ _ (by
      intro k he
      have hv:=congrArg (fun i : Fin 115=>i.val) he
      have hj:=j.isLt
      change 78+k.val=j.val at hv
      omega),data_row,data_row]
  · change install _ _ _ (projectionSlots j)=data _ _ (projectionSlots j)
    rw [install_slot _ projection_injective,data_projection]

theorem increment_run (p : RawProjectionPCP) (R Q k B : ℕ) (hk : k+1<2^R)
    (H : Fin 78→ℕ) (A : Fin 78→List Bool) :
    ∃ r,runFrom incrementMachine (4*R+2)
      ⟨incrementMachine.start,heads H,data A (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) B)⟩=some r ∧
      r.steps≤4*R+2 ∧ r.final.heads=heads H ∧
      r.final.tapes=data A (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R (k+1)) B) := by
  have base:=RecoveryBoundedRowProjection.increment_ready p R Q k B hk
  obtain ⟨r,rr,rh,rt,rs⟩:=base.focus_at projectionSlots projection_injective (heads H)
    (data A (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R k) B))
    (data_projection A _) (heads_projection H)
  exact ⟨r,rr,rs,rh,rt.trans (projection_install A _ _)⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows
