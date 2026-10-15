import Proof.Amplification.RecoveryCanonicalTables

/-! The canonical scanner supplies the exact table-start Sources predicate
on the same279-tape front, while retaining both prepared raw banks. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem front_scan (code : Nat) (c : Certificate) (hc : Fits code c)
    (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (ha : RecoveryColdSAT.Ready code.bits (TableFirst.pack (Serialization.width code) c) h a)
    (hcode : a 0=frame code.bits) :
    ∃ (g : Fin 270→Nat) (b : Fin 270→List Bool),∃ r,
      runFrom RecoveryColdFront.scanProgram
        (RecoveryColdScanner.scanBudget code.bits (TableFirst.pack (Serialization.width code) c))
        ⟨RecoveryColdFront.scanProgram.start,RecoveryColdFront.heads h,RecoveryColdFront.tapes a⟩=some r ∧
      r.final.heads=RecoveryColdTablesAmbient.heads g ∧ r.final.tapes=RecoveryColdTablesAmbient.tapes b ∧
      g 230=0 ∧ b 230=[true] ∧
      (fun i : Fin 172=>g (i.castAdd 98))=h ∧ (fun i : Fin 172=>b (i.castAdd 98))=a ∧
      RecoveryColdTablesAmbient.Sources (TableFirst.pack (Serialization.width code) c)
        (tablePosition code c) (RecoveryColdView.width code.bits) (RecoveryColdView.limit code.bits) g b := by
  let word := TableFirst.pack (Serialization.width code) c
  have hh : h 0=0 ∧ h 1=0 := by
    obtain ⟨pos,_,_,_,he,_⟩ := ha
    rw [he]
    exact ⟨rfl,rfl⟩
  have hw := (RecoveryColdSAT.ready_retained code.bits word h a ha).1
  obtain ⟨base,hr,hflagh,hflagt,hpos,hsource,hkeepH,hkeepT⟩ := scanner_run code c hc h a hh ⟨hcode,hw⟩
  let r := TapeEmbedding.receipt RecoveryColdTablesAmbient.tailHeads RecoveryColdTablesAmbient.tailTapes base
  have hrun := TapeEmbedding.run_embed RecoveryColdScanner.scanProgram
    RecoveryColdTablesAmbient.tailHeads RecoveryColdTablesAmbient.tailTapes _ _ base hr
  rw [show RecoveryColdScanner.flag=(230 : Fin 270) by decide] at hflagh hflagt
  refine ⟨base.final.heads,base.final.tapes,r,hrun,rfl,rfl,hflagh,hflagt,hkeepH,hkeepT,?_⟩
  exact RecoveryColdFront.scan_sources code.bits word h a ha base.final.heads base.final.tapes
    hkeepH hkeepT (tablePosition code c) ⟨hpos,hsource⟩

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
