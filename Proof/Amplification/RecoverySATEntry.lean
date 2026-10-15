import Proof.Amplification.RecoverySATLayout

/-! The successful cold valuation/raw-view execution supplies every source
for the RawSAT copies. Its original witness and length are retained outputs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem embed_run {s : Nat} (p : Machine 100 s) (fuel : Nat) (a : Fin 100→List Bool)
    (base : ExecutionReceipt 100 s) (hb : run p fuel a=some base) :
    run (TapeEmbedding.machine 72 p) fuel (lift a)=
      some (TapeEmbedding.receipt (fun _ : Fin 72=>0) (fun _=>[]) base) := by
  have h := TapeEmbedding.run_embed p (fun _ : Fin 72=>0) (fun _=>[]) fuel _ base hb
  have hi : TapeEmbedding.config (fun _ : Fin 72=>0) (fun _=>[]) (initialConfiguration p a)=
      initialConfiguration (TapeEmbedding.machine 72 p) (lift a) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at h
  exact h

noncomputable def prefixProgram := TapeEmbedding.machine 72 RecoveryColdView.coldProgram
def input (bits word : List Bool) := lift (RecoveryColdView.input bits word)

theorem prefix_run (bits word : List Bool) :
    ∃ r,run prefixProgram (RecoveryColdView.coldBudget bits word) (input bits word)=some r ∧
      r.final.heads 30=0 ∧
      r.final.tapes 30=[(readList (limit bits) (readEntry (width bits)) word).isSome] ∧
      ∀ table tail,readList (limit bits) (readEntry (width bits)) word=some (table,tail) →
        ∃ pos,r.final.heads=heads pos ∧ Sources bits word r.final.tapes ∧
          RecoveryColdView.Ready bits word (fun j=>r.final.heads (j.castAdd 72))
            (fun j=>r.final.tapes (j.castAdd 72)) := by
  obtain ⟨base,hbase,_,hh,ht,hgood⟩ := RecoveryColdView.cold_run bits word
  let r := TapeEmbedding.receipt (fun _ : Fin 72=>0) (fun _=>[]) base
  have hr := embed_run RecoveryColdView.coldProgram (RecoveryColdView.coldBudget bits word) _ base hbase
  refine ⟨r,hr,hh,ht,?_⟩
  intro table tail hp
  have ha := hgood (by simp only [hp,Option.isSome_some])
  have hk := RecoveryColdView.cold_retained bits word base hbase table tail hp
  have hs := sources_of_return bits word base.final.heads base.final.tapes ha hk.1 hk.2.1 hk.2.2
  obtain ⟨table',tail',count,a,_,_,_,_,_,_,hheads,_⟩ := ha
  refine ⟨2*(count*(width bits+2)+1),?_,hs,?_⟩
  · change Fin.addCases (m:=100) (n:=72) (motive:=fun _=>Nat) base.final.heads (fun _=>0)=_
    rw [hheads]
    rfl
  · have heh : (fun j : Fin 100=>r.final.heads (j.castAdd 72))=base.final.heads := by
      funext j
      simp only [r,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
    have het : (fun j : Fin 100=>r.final.tapes (j.castAdd 72))=base.final.tapes := by
      funext j
      simp only [r,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
    rw [heh,het]
    exact hgood (by simp only [hp,Option.isSome_some])

end NearCubicWires.RepairOrdinary.RecoveryColdSAT
