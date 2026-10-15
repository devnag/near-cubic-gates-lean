import Proof.Amplification.RecoveryCompactRetained

/-! Retain the exact original source-vector equality at the whole
materializer endpoint. Canonical completeness can identify its actual
counts and table suffixes without reexecuting or guessing their values. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem materialize_exact (bits word : List Bool) (H : Fin 338→Nat) (A : Fin 338→List Bool)
    (hr : RecoveryColdMarker.Ready bits word H A) :
    ∃ n innerBits m outerBits,n≤limit bits ∧ m≤limit bits ∧
      (fun j=>A (sourceSlots j))=sourceTapes bits word innerBits outerBits n m ∧
      ∃ r,runFrom materializeProgram (materializeBudget bits word n m)
        ⟨materializeProgram.start,liftedHeads H,bankInput A⟩=some r ∧
        r.final.heads=finishHeads (bankHeads H) ∧
        r.final.tapes=finishTapes (stage34 bits word innerBits outerBits n m (bankInput A)) ∧
        r.steps=materializeBudget bits word n m := by
  obtain ⟨n,innerBits,m,outerBits,hn,hm,ht,hh,hrst,he,hhr,hhe⟩ := source_ready bits word H A hr
  have hsrc := bank_sources bits word innerBits outerBits n m H A ht hh hrst he hhr hhe
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := count_boot H A (congrFun hh 8) (congrFun hh 9)
  obtain ⟨copied,hcopy,hch,hct,hcs⟩ := bank_run bits word innerBits outerBits n m
    (bankHeads H) (bankInput A) hsrc
  have hcstart : Composition.restart first.final bankProgram.start=
      (⟨bankProgram.start,bankHeads H,bankInput A⟩ : Configuration 493 _) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  rw [←hcstart] at hcopy
  have hjoin := Composition.run_join countBoot bankProgram 1 (bankBudget bits word n m)
    _ first copied hfirst hcopy
  obtain ⟨ha,hb⟩ := prior_blank bits word innerBits outerBits n m (bankInput A) hsrc.fresh
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := finish_run (bankHeads H)
    (stage34 bits word innerBits outerBits n m (bankInput A)) hsrc.fresh_head ha hb
  have hlstart : Composition.restart (Composition.joinedReceipt first copied).final finish.start=
      (⟨finish.start,bankHeads H,stage34 bits word innerBits outerBits n m (bankInput A)⟩ :
        Configuration 493 2) := by
    apply configuration_ext
    · rfl
    · exact hch
    · exact hct
  rw [←hlstart] at hlast
  have hrun := Composition.run_join entryProgram finish (1+1+bankBudget bits word n m) 1
    _ (Composition.joinedReceipt first copied) last hjoin hlast
  have hbudget : (1+1+bankBudget bits word n m)+1+1=materializeBudget bits word n m := by
    unfold materializeBudget
    omega
  rw [hbudget] at hrun
  refine ⟨n,innerBits,m,outerBits,hn,hm,ht,
    Composition.joinedReceipt (Composition.joinedReceipt first copied) last,hrun,hlh,hlt,?_⟩
  change (first.steps+1+copied.steps)+1+last.steps=materializeBudget bits word n m
  rw [hfs,hcs,hls]
  exact hbudget

end NearCubicWires.RepairOrdinary.RecoveryColdCompact
