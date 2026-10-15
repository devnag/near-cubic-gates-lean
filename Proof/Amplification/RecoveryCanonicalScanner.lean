import Proof.Amplification.RecoveryCanonicalReader

/-! Positive canonical execution of the complete existing cold scanner.
The exact retained source cursor is the start of the table counts. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scanner_run (code : Nat) (c : Certificate) (hc : Fits code c)
    (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (hh : h 0=0 ∧ h 1=0)
    (ht : a 0=frame code.bits ∧ a 1=frame (TableFirst.pack (Serialization.width code) c)) :
    ∃ r,runFrom RecoveryColdScanner.scanProgram
      (RecoveryColdScanner.scanBudget code.bits (TableFirst.pack (Serialization.width code) c))
      ⟨RecoveryColdScanner.scanProgram.start,RecoveryColdScanner.heads h,RecoveryColdScanner.tapes a⟩=some r ∧
      r.final.heads RecoveryColdScanner.flag=0 ∧ r.final.tapes RecoveryColdScanner.flag=[true] ∧
      r.final.heads RecoveryColdScanner.source=2*tablePosition code c ∧
      r.final.tapes RecoveryColdScanner.source=frame (TableFirst.pack (Serialization.width code) c) ∧
      (fun i : Fin 172=>r.final.heads (i.castAdd 98))=h ∧
      (fun i : Fin 172=>r.final.tapes (i.castAdd 98))=a := by
  let word := TableFirst.pack (Serialization.width code) c
  let x := view code.bits word (2*(valuationPrefix code c).length)
  obtain ⟨first,hfirst,_,hfh,hft,hready⟩ := RecoveryColdScanner.prepare_run code.bits word h a
    hh ht c.table (suffix code c) (valuation_parse code c hc)
  have hn := ready_native code c hc (fun j=>first.final.heads (RecoveryColdScanner.slots j))
    (fun j=>first.final.tapes (RecoveryColdScanner.slots j)) hready RecoveryRawViewEntry.machine.start
  obtain ⟨base,hbase,hhb,htb,hpb,hsb⟩ := native_reader code c hc
    (fun j=>first.final.heads (RecoveryColdScanner.readSlots j))
    (fun j=>first.final.tapes (RecoveryColdScanner.readSlots j)) hn
  obtain ⟨last,hlast,hlfinal,_⟩ := RecoveryFocus.run_config RecoveryColdScanner.readSlots
    RecoveryColdScanner.readSlots_injective RecoveryRawViewEntry.machine
    first.final.heads first.final.tapes (RecoveryRawViewEntry.budget x) _ base hbase
  rw [RecoveryColdScanner.read_input] at hlast
  have hb : RecoveryRawViewEntry.budget x≤536870912*(RecoveryColdView.width code.bits+1)^4 := by
    have hb := RecoveryRawViewEntry.budget_bound x (view_valid _ _ _)
    rw [view_width] at hb
    exact hb
  have hm := runFrom_moreFuel RecoveryColdScanner.readProgram (RecoveryRawViewEntry.budget x)
    (536870912*(RecoveryColdView.width code.bits+1)^4-RecoveryRawViewEntry.budget x) _ last hlast
  rw [Nat.add_sub_of_le hb] at hm
  have hr := Composition.run_join RecoveryColdScanner.program RecoveryColdScanner.readProgram
    (RecoveryColdView.coldBudget code.bits word) (536870912*(RecoveryColdView.width code.bits+1)^4)
    _ first last hfirst hm
  have hk := RecoveryColdScanner.read_retained first.final.heads first.final.tapes base.final
  have heh (j : Fin 66) : last.final.heads (RecoveryColdScanner.readSlots j)=base.final.heads j := by
    rw [hlfinal]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot RecoveryColdScanner.readSlots
      RecoveryColdScanner.readSlots_injective]
  have het (j : Fin 66) : last.final.tapes (RecoveryColdScanner.readSlots j)=base.final.tapes j := by
    rw [hlfinal]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot RecoveryColdScanner.readSlots
      RecoveryColdScanner.readSlots_injective]
  refine ⟨Composition.joinedReceipt first last,hr,(heh 28).trans hhb,(het 28).trans htb,
    (heh 29).trans hpb,(het 29).trans hsb,?_,?_⟩
  · change (fun i : Fin 172=>last.final.heads (i.castAdd 98))=h
    rw [hlfinal]
    exact hk.1.trans hfh
  · change (fun i : Fin 172=>last.final.tapes (i.castAdd 98))=a
    rw [hlfinal]
    exact hk.2.trans hft

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
