import Proof.Amplification.RecoveryRawViewEntryState

/-! All-position outer-count parsing on the actual 66-tape raw-view bank.
The source cursor and loop counter are the selected tapes; all other banks,
including the false result on rejection, are retained literally. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem count_input (x : State) (word : List Bool) (k : Nat)
    (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) :
    RecoveryFocus.config countSlots (RecoveryRawViewEnd.cfg x 0 (0 : Fin 5)).heads
      (RecoveryRawViewEnd.cfg x 0 (0 : Fin 5)).tapes
      (RecoveryCertificateCount.scan 0 (frame word) (2*k) 0 x.limit)=RecoveryRawViewEnd.cfg x 0 0 := by
  apply focus_configuration countSlots countSlots_injective
  · rfl
  · intro j; fin_cases j
    · exact hp.symm
    · rfl
    · rfl
  · intro j; fin_cases j
    · exact hs.symm
    · rfl
    · rfl
  · intro i _; rfl
  · intro i _; rfl

theorem count_output (x : State) (word : List Bool) (k n : Nat)
    (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) :
    RecoveryFocus.config countSlots (RecoveryRawViewEnd.cfg x 0 (0 : Fin 5)).heads
      (RecoveryRawViewEnd.cfg x 0 (0 : Fin 5)).tapes
      (RecoveryCertificateCount.cfg 3 (frame word) (2*k+2*n+2) n x.limit 1)=
      RecoveryRawViewEnd.cfg (advanced x n) n 3 := by
  apply focus_configuration countSlots countSlots_injective
  · rfl
  · intro j; fin_cases j
    · change 2*k+2*n+2=x.inner.stream.pos+2*n+2
      rw [hp]
    · rfl
    · rfl
  · intro j; fin_cases j
    · exact hs.symm
    · rfl
    · rfl
  · intro i hi
    rw [counted_heads]
    exact (Function.update_of_ne (Ne.symm (hi 0)) _ _).symm
  · intro i hi
    rw [counted_tapes]
    exact (Function.update_of_ne (Ne.symm (hi 1)) _ _).symm

theorem count_run (x : State) (word : List Bool) (k : Nat)
    (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) :
    ∃ r,runFrom countMachine (3*x.limit+3) (RecoveryRawViewEnd.cfg x 0 countMachine.start)=some r ∧
      r.steps ≤ 3*x.limit+3 ∧
      (r.final.control=3 ↔ (readCount x.limit (word.drop k)).isSome=true) ∧
      r.final.heads 28=0 ∧ r.final.tapes 28=[x.inner.stream.data.present] ∧
      (∀ n rest,readCount x.limit (word.drop k)=some (n,rest) →
        n ≤ x.limit ∧ r.final=RecoveryRawViewEnd.cfg (advanced x n) n 3) := by
  obtain ⟨base,hr,hb,hc,hf⟩ := RecoveryCertificateCount.bounded_at x.limit word k
  obtain ⟨r,h,hfinal,hsteps⟩ := RecoveryFocus.run_config countSlots countSlots_injective
    RecoveryCertificateCount.machine (RecoveryRawViewEnd.cfg x 0 (0 : Fin 5)).heads
    (RecoveryRawViewEnd.cfg x 0 (0 : Fin 5)).tapes _ _ base hr
  rw [count_input x word k hs hp] at h
  have hpick : RecoveryFocus.pick countSlots (28 : Fin 66)=none := by
    have hn : ¬∃ j,countSlots j=(28 : Fin 66) := by decide
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

end NearCubicWires.RepairOrdinary.RecoveryRawViewEntry
