import Proof.Hierarchy.CompetitorSameBucketPairEmitLayout

/-! Dock the actual signed-key appender into the classified pair workspace.
The contribution output cursor is preserved through the local call. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketPairEmit
open LocalBitMultitape SignedSortKey MatrixScoreBatch RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem tapes_out_other (work : Fin 31 → List Bool) (cap p k : ℕ) (coefficient : ℤ)
    (out out' : List Bool) {z z' : ℕ} (q : Fin z) (q' : Fin z') (i : Fin 36) (hi : i≠34) :
    (cfg q work cap p k coefficient out).tapes i=(cfg q' work cap p k coefficient out').tapes i := by
  fin_cases i <;> simp_all [cfg,extras,Fin.addCases]

theorem append_output (cap s k u p : ℕ) (sa sb coefficient : ℤ) (a b ra rb : ℕ)
    (out out' : List Bool) (q : Fin 17) :
    RecoveryFocus.config appendSlots
      (cfg append.start (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3) cap p k coefficient out).heads
      (cfg append.start (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3) cap p k coefficient out).tapes
      (CompetitorSameBucketKeyAppend.paddedCfg q (signMagnitude p coefficient) k b a cap out')=
    cfg q (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3) cap p k coefficient out' := by
  have pick34 : RecoveryFocus.pick appendSlots 34=some 6 := RecoveryFocus.pick_slot appendSlots append_injective 6
  apply configuration_ext
  · rfl
  · funext i
    cases h : RecoveryFocus.pick appendSlots i with
    | none =>
      have hn : i≠34 := by intro he; subst i; rw [pick34] at h; contradiction
      simp [RecoveryFocus.config,h,cfg,heads,hn]
    | some j =>
      have he := RecoveryFocus.slot_of_pick appendSlots h
      simp only [RecoveryFocus.config,h]
      rw [←he]
      exact (append_slots cap s k u p sa sb coefficient a b ra rb out' j).1.symm
  · funext i
    cases h : RecoveryFocus.pick appendSlots i with
    | none =>
      have hn : i≠34 := by intro he; subst i; rw [pick34] at h; contradiction
      simp only [RecoveryFocus.config,h]
      exact tapes_out_other _ _ _ _ _ _ _ _ _ i hn
    | some j =>
      have he := RecoveryFocus.slot_of_pick appendSlots h
      simp only [RecoveryFocus.config,h]
      rw [←he]
      exact (append_slots cap s k u p sa sb coefficient a b ra rb out' j).2.symm

theorem append_run (cap s k u p : ℕ) (sa sb coefficient : ℤ) (a b ra rb : ℕ) (out : List Bool)
    (hp : 2*(p+1)≤cap) (hk : 2*k≤cap) :
    ∃ r,runFrom append (4*p+8*k+17)
        (cfg append.start (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3) cap p k coefficient out)=some r ∧
      r.final.heads=heads (out++CompetitorSameBucketKeyAppend.word p k coefficient a b) ∧
      r.final.tapes=(cfg append.start (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3) cap p k coefficient
        (out++CompetitorSameBucketKeyAppend.word p k coefficient a b)).tapes ∧ r.steps≤4*p+8*k+17 := by
  obtain ⟨base,hb,bh,bt,bs⟩ := CompetitorSameBucketKeyAppend.signed_run p k b a cap coefficient out hp hk
  let entry := cfg append.start (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3) cap p k coefficient out
  have hi : RecoveryFocus.config appendSlots entry.heads entry.tapes
      (CompetitorSameBucketKeyAppend.paddedCfg CompetitorSameBucketKeyAppend.machine.start (signMagnitude p coefficient) k b a cap out)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; exact (append_slots cap s k u p sa sb coefficient a b ra rb out i).1
    · intro i; exact (append_slots cap s k u p sa sb coefficient a b ra rb out i).2
  obtain ⟨actual,hr,hf,hs⟩ := RecoveryFocus.run_config appendSlots append_injective CompetitorSameBucketKeyAppend.machine
    entry.heads entry.tapes _ _ base hb
  rw [hi] at hr
  have he : base.final=CompetitorSameBucketKeyAppend.paddedCfg base.final.control (signMagnitude p coefficient) k b a cap
      (out++CompetitorSameBucketKeyAppend.word p k coefficient a b) := configuration_ext rfl bh bt
  refine ⟨actual,hr,?_,?_,hs.trans_le bs⟩
  · rw [hf,he]
    rw [append_output]
    rfl
  · rw [hf,he]
    rw [append_output]
    rfl

end NearCubicWires.RepairOrdinary.CompetitorSameBucketPairEmit
