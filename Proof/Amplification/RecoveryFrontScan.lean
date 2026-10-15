import Proof.Amplification.RecoveryFrontPrefix

/-! The whole scanner consumes the prepared RawSAT prefix while retaining
the initialized table bank. Its actual successful cursor supplies Sources. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdFront
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def scanProgram := TapeEmbedding.machine 9 RecoveryColdScanner.scanProgram

theorem scan_sources (bits word : List Bool) (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (ha : RecoveryColdSAT.Ready bits word h a) (g : Fin 270→Nat) (b : Fin 270→List Bool)
    (hh : (fun i : Fin 172=>g (i.castAdd 98))=h)
    (ht : (fun i : Fin 172=>b (i.castAdd 98))=a) (k : Nat)
    (hs : g RecoveryColdScanner.source=2*k ∧ b RecoveryColdScanner.source=frame word) :
    RecoveryColdTablesAmbient.Sources word k (width bits) (limit bits) g b := by
  obtain ⟨hh62,ht62,hh96,ht96⟩ := RecoveryColdSAT.ready_drivers bits word h a ha
  have hh62' := congrFun hh (62 : Fin 172)
  have ht62' := congrFun ht (62 : Fin 172)
  have hh96' := congrFun hh (96 : Fin 172)
  have ht96' := congrFun ht (96 : Fin 172)
  simp only [show (62 : Fin 172).castAdd 98=(62 : Fin 270) by decide] at hh62' ht62'
  simp only [show (96 : Fin 172).castAdd 98=(96 : Fin 270) by decide] at hh96' ht96'
  rw [show RecoveryColdScanner.source=(193 : Fin 270) by decide] at hs
  exact ⟨hs.1,hs.2,hh62'.trans hh62,ht62'.trans ht62,hh96'.trans hh96,ht96'.trans ht96⟩

theorem scan_run (bits word : List Bool) (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (ha : RecoveryColdSAT.Ready bits word h a) (hcode : a 0=frame bits)
    (table : List (Nat×Bool)) (tail : List Bool)
    (hp : readList (limit bits) (readEntry (width bits)) word=some (table,tail)) :
    ∃ bit,∃ (g : Fin 270→Nat) (b : Fin 270→List Bool),∃ r,
      runFrom scanProgram (RecoveryColdScanner.scanBudget bits word)
        ⟨scanProgram.start,heads h,tapes a⟩=some r ∧
      r.steps ≤ RecoveryColdScanner.scanBudget bits word ∧
      r.final.heads=RecoveryColdTablesAmbient.heads g ∧
      r.final.tapes=RecoveryColdTablesAmbient.tapes b ∧
      g 230=0 ∧ b 230=[bit] ∧
      (fun i : Fin 172=>g (i.castAdd 98))=h ∧
      (fun i : Fin 172=>b (i.castAdd 98))=a ∧
      (bit=true → ∃ k,RecoveryColdTablesAmbient.Sources word k (width bits) (limit bits) g b) := by
  have hh : h 0=0 ∧ h 1=0 := by
    obtain ⟨pos,_,_,_,he,_⟩ := ha
    rw [he]
    exact ⟨rfl,rfl⟩
  have hw := (RecoveryColdSAT.ready_retained bits word h a ha).1
  obtain ⟨bit,base,hr,hb,hflagh,hflagt,hkeepH,hkeepT,hgood⟩ :=
    RecoveryColdScanner.scan_run bits word h a hh ⟨hcode,hw⟩ table tail hp
  let r := TapeEmbedding.receipt RecoveryColdTablesAmbient.tailHeads RecoveryColdTablesAmbient.tailTapes base
  have hrun := TapeEmbedding.run_embed RecoveryColdScanner.scanProgram
    RecoveryColdTablesAmbient.tailHeads RecoveryColdTablesAmbient.tailTapes _ _ base hr
  rw [show RecoveryColdScanner.flag=(230 : Fin 270) by decide] at hflagh hflagt
  refine ⟨bit,base.final.heads,base.final.tapes,r,hrun,hb,rfl,rfl,hflagh,hflagt,hkeepH,hkeepT,?_⟩
  intro hbit
  obtain ⟨k,hk⟩ := hgood hbit
  exact ⟨k,scan_sources bits word h a ha base.final.heads base.final.tapes hkeepH hkeepT k hk⟩

end NearCubicWires.RepairOrdinary.RecoveryColdFront
