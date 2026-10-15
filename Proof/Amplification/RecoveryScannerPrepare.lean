import Proof.Amplification.RecoveryScannerLayout

/-! Reuse the actual cold reader on the fresh scanner bank. The two final
raw banks and their streaming heads are retained exactly. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdScanner
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prepare_run (bits word : List Bool) (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (hh : h 0=0 ∧ h 1=0) (ht : a 0=frame bits ∧ a 1=frame word)
    (table : List (Nat×Bool)) (tail : List Bool)
    (hp : readList (limit bits) (readEntry (width bits)) word=some (table,tail)) :
    ∃ r,runFrom program (RecoveryColdView.coldBudget bits word)
        ⟨program.start,heads h,tapes a⟩=some r ∧
      r.steps≤RecoveryColdView.coldBudget bits word ∧
      (fun i : Fin 172=>r.final.heads (i.castAdd 98))=h ∧
      (fun i : Fin 172=>r.final.tapes (i.castAdd 98))=a ∧
      RecoveryColdView.Ready bits word (fun j=>r.final.heads (slots j)) (fun j=>r.final.tapes (slots j)) := by
  obtain ⟨base,hbase,hbound,_,_,hready⟩ := RecoveryColdView.cold_run bits word
  have hb := hready (by simp only [hp,Option.isSome_some])
  have horiginal := RecoveryColdView.cold_original bits word base hbase table tail hp
  have hwitness := (RecoveryColdView.cold_retained bits word base hbase table tail hp).1
  have hheads : base.final.heads 0=0 ∧ base.final.heads 1=0 := by
    obtain ⟨_,_,count,_,_,_,_,_,_,_,hc,_⟩ := hb
    rw [hc]
    exact ⟨rfl,rfl⟩
  obtain ⟨r,hr,hfinal,hsteps⟩ := RecoveryFocus.run_config slots slots_injective
    RecoveryColdView.coldProgram (heads h) (tapes a) (RecoveryColdView.coldBudget bits word) _ base hbase
  have hi : RecoveryFocus.config slots (heads h) (tapes a)
      (initialConfiguration RecoveryColdView.coldProgram (RecoveryColdView.input bits word))=
      (⟨program.start,heads h,tapes a⟩ : Configuration 270 _) :=
    initial_layout bits word h a hh ht _
  rw [hi] at hr
  have hk := retained h a base.final ⟨hheads.1.trans hh.1.symm,hheads.2.trans hh.2.symm⟩
    ⟨horiginal.trans ht.1.symm,hwitness.trans ht.2.symm⟩
  refine ⟨r,hr,hsteps.le.trans hbound,?_,?_,?_⟩
  · rw [hfinal]
    exact hk.1
  · rw [hfinal]
    exact hk.2
  · rw [hfinal]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using hb

end NearCubicWires.RepairOrdinary.RecoveryColdScanner
