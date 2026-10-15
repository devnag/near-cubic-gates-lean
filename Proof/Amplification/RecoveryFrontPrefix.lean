import Proof.Amplification.RecoveryTablesAmbientRun

/-! Actual cold prefix for the final parser front: initialize the fresh
table flags/counters, then execute the full172-tape RawSAT preparation. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdFront
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (h : Fin 172→Nat) := RecoveryColdTablesAmbient.heads (RecoveryColdScanner.heads h)
def tapes (a : Fin 172→List Bool) := RecoveryColdTablesAmbient.tapes (RecoveryColdScanner.tapes a)
def input (bits word : List Bool) :=
  RecoveryColdTablesAmbient.coldTapes (RecoveryColdScanner.tapes (RecoveryColdSAT.input bits word))
noncomputable def nativeProgram := TapeEmbedding.machine 9 (TapeEmbedding.machine 98 RecoveryColdSAT.coldProgram)
noncomputable def prefixProgram := Composition.machine RecoveryColdTablesAmbient.ambientBoot nativeProgram
def prefixBudget (bits word : List Bool) := RecoveryColdSAT.coldBudget bits word+2

theorem scanner_zero_heads : RecoveryColdScanner.heads (fun _=>0)=(fun _=>0) := by
  funext i
  refine Fin.addCases (m:=172) (n:=98) (motive:=fun i=>RecoveryColdScanner.heads (fun _=>0) i=0) ?_ ?_ i
  · intro j; simp only [RecoveryColdScanner.heads,Fin.addCases_left]
  · intro j; simp only [RecoveryColdScanner.heads,Fin.addCases_right]

theorem native_run (bits word : List Bool) (base : ExecutionReceipt 172 _)
    (hr : run RecoveryColdSAT.coldProgram (RecoveryColdSAT.coldBudget bits word)
      (RecoveryColdSAT.input bits word)=some base) :
    ∃ r,runFrom nativeProgram (RecoveryColdSAT.coldBudget bits word)
        ⟨nativeProgram.start,heads (fun _=>0),tapes (RecoveryColdSAT.input bits word)⟩=some r ∧
      r.final.heads=heads base.final.heads ∧ r.final.tapes=tapes base.final.tapes := by
  let middle := TapeEmbedding.receipt (fun _ : Fin 98=>0) (fun _=>[]) base
  have hmiddle := TapeEmbedding.run_embed RecoveryColdSAT.coldProgram
    (fun _ : Fin 98=>0) (fun _=>[]) _ _ base hr
  let r := TapeEmbedding.receipt RecoveryColdTablesAmbient.tailHeads RecoveryColdTablesAmbient.tailTapes middle
  have h := TapeEmbedding.run_embed (TapeEmbedding.machine 98 RecoveryColdSAT.coldProgram)
    RecoveryColdTablesAmbient.tailHeads RecoveryColdTablesAmbient.tailTapes _ _ middle hmiddle
  exact ⟨r,h,rfl,rfl⟩

theorem prefix_run (bits word : List Bool) :
    ∃ base,run RecoveryColdSAT.coldProgram (RecoveryColdSAT.coldBudget bits word)
        (RecoveryColdSAT.input bits word)=some base ∧
      base.final.heads 30=0 ∧
      base.final.tapes 30=[(readList (limit bits) (readEntry (width bits)) word).isSome] ∧
      ((readList (limit bits) (readEntry (width bits)) word).isSome=true →
        RecoveryColdSAT.Ready bits word base.final.heads base.final.tapes) ∧
      ∃ r,run prefixProgram (prefixBudget bits word) (input bits word)=some r ∧
        r.steps ≤ prefixBudget bits word ∧
        r.final.heads=heads base.final.heads ∧ r.final.tapes=tapes base.final.tapes := by
  obtain ⟨base,hbase,_,hbh,hbt,hready⟩ := RecoveryColdSAT.cold_run bits word
  obtain ⟨first,hfirst,hfh,hft,_⟩ := RecoveryColdTablesAmbient.boot_ambient
    (fun _ : Fin 270=>0) (RecoveryColdScanner.tapes (RecoveryColdSAT.input bits word))
  obtain ⟨last,hlast,hlh,hlt⟩ := native_run bits word base hbase
  have hi : Composition.restart first.final nativeProgram.start=
      (⟨nativeProgram.start,heads (fun _=>0),tapes (RecoveryColdSAT.input bits word)⟩ : Configuration 279 _) := by
    apply configuration_ext
    · rfl
    · change first.final.heads=heads (fun _=>0)
      rw [hfh]
      unfold heads
      rw [scanner_zero_heads]
    · exact hft
  rw [←hi] at hlast
  have h := Composition.run_join RecoveryColdTablesAmbient.ambientBoot nativeProgram 1
    (RecoveryColdSAT.coldBudget bits word) _ first last hfirst hlast
  rw [show 1+1+RecoveryColdSAT.coldBudget bits word=prefixBudget bits word by unfold prefixBudget; omega] at h
  let r := Composition.joinedReceipt first last
  have hi0 : RecoveryColdTablesAmbient.coldHeads (fun _=>0)=(fun _=>0) := by
    funext i
    refine Fin.addCases (m:=270) (n:=9)
      (motive:=fun i=>RecoveryColdTablesAmbient.coldHeads (fun _=>0) i=0) ?_ ?_ i
    · intro j; simp only [RecoveryColdTablesAmbient.coldHeads,Fin.addCases_left]
    · intro j; simp only [RecoveryColdTablesAmbient.coldHeads,Fin.addCases_right]
  change runFrom prefixProgram (prefixBudget bits word)
    ⟨prefixProgram.start,RecoveryColdTablesAmbient.coldHeads (fun _=>0),input bits word⟩=some r at h
  rw [hi0] at h
  exact ⟨base,hbase,hbh,hbt,hready,r,h,runFrom_steps_le prefixProgram (prefixBudget bits word) _ r h,hlh,hlt⟩

end NearCubicWires.RepairOrdinary.RecoveryColdFront
