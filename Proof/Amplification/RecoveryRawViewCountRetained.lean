import Proof.Amplification.RecoveryRawViewClause

/-! Even a rejected count keeps the raw-view body's physical result cell.
This is needed by the enclosing early-stop branch, which does not rewind
or repair the rejected count workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem count_retained_run (x : State) (word : List Bool) (k : Nat)
    (hz : x.count=0) (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) :
    ∃ r,runFrom countMachine (3*x.limit+3) (x.cfg countMachine.start)=some r ∧
      r.steps ≤ 3*x.limit+3 ∧
      (r.final.control=3 ↔ (readCount x.limit (word.drop k)).isSome=true) ∧
      r.final.heads 28=0 ∧ r.final.tapes 28=[x.inner.stream.data.present] ∧
      (∀ n rest,readCount x.limit (word.drop k)=some (n,rest) →
        n ≤ x.limit ∧ r.final=(counted x n).cfg 3) := by
  obtain ⟨base,hr,hb,hc,hf⟩ := RecoveryCertificateCount.padded_bounded_at x.capacity x.limit word k
  obtain ⟨r,h,hfinal,hsteps⟩ := RecoveryFocus.run_config countSlots countSlots_injective
    RecoveryCertificateCount.machine (x.cfg (0 : Fin 5)).heads (x.cfg (0 : Fin 5)).tapes _ _ base hr
  rw [count_input x word k hz hs hp] at h
  have hpick : RecoveryFocus.pick countSlots (28 : Fin 65)=none := by
    have hn : ¬∃ j,countSlots j=(28 : Fin 65) := by decide
    simp only [RecoveryFocus.pick,dif_neg hn]
  refine ⟨r,h,hsteps.le.trans hb,?_,?_,?_,?_⟩
  · simpa only [hfinal,RecoveryFocus.config] using hc
  · rw [hfinal]
    simp only [RecoveryFocus.config,hpick]
    rfl
  · rw [hfinal]
    simp only [RecoveryFocus.config,hpick]
    rfl
  · intro n rest hparse
    obtain ⟨hn,he⟩ := hf n rest hparse
    refine ⟨hn,?_⟩
    rw [hfinal,he]
    exact count_output x word k n hs hp

end NearCubicWires.RepairOrdinary.RecoveryRawView
