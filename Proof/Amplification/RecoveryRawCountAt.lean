import Proof.Amplification.RecoveryRawClauseRetained

/-! Counts are read at the retained physical witness cursor. Skipping
unused fields may pass the final frame marker; those positions physically
read false and reject rather than acquiring an artificial padded source. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCertificateCount
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem frame_marker (word : List Bool) (k : Nat) :
    readTapeBit (frame word) (2*k)=decide (k<word.length) := by
  induction word generalizing k with
  | nil=>cases k <;> simp [frame,readTapeBit,List.getD]
  | cons bit word ih=>
    cases k with
    | zero=>rfl
    | succ k=>simpa [frame,readTapeBit,Nat.mul_add,Nat.add_assoc] using ih k

theorem past_marker_run (word : List Bool) (k cap : Nat) (hk : word.length ≤ k) :
    ∃ r,runFrom machine 1 (scan 0 (frame word) (2*k) 0 cap)=some r ∧
      r.final=scan 4 (frame word) (2*k+1) 0 cap ∧ r.steps=1 := by
  have hb : readTapeBit (frame word) (2*k)=false := by rw [frame_marker]; exact decide_eq_false (by omega)
  have h : step machine (scan 0 (frame word) (2*k) 0 cap)=some (scan 4 (frame word) (2*k+1) 0 cap) := by
    simp [step,machine,scan,cfg,Configuration.scanned,hb]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem bounded_at (cap : Nat) (word : List Bool) (k : Nat) :
    ∃ r,runFrom machine (3*cap+3) (scan 0 (frame word) (2*k) 0 cap)=some r ∧
      r.steps ≤ 3*cap+3 ∧ (r.final.control=3 ↔ (readCount cap (word.drop k)).isSome=true) ∧
      ∀ n rest,readCount cap (word.drop k)=some (n,rest) →
        n ≤ cap ∧ r.final=cfg 3 (frame word) (2*k+2*n+2) n cap 1 := by
  by_cases hk : k ≤ word.length
  · have hw : Streaming.marks (word.take k)++frame (word.drop k)=frame word := by
      rw [←Streaming.frame_append,List.take_append_drop]
    have hl : (Streaming.marks (word.take k)).length=2*k := by
      rw [Streaming.marks_length,List.length_take,Nat.min_eq_left hk]
    obtain ⟨r,hr,hb,hc,hf⟩ := bounded_witness cap (Streaming.marks (word.take k)) (word.drop k)
    rw [hw,hl] at hr
    refine ⟨r,hr,hb,hc,?_⟩
    intro n rest hp
    obtain ⟨hn,he⟩ := hf n rest hp
    rw [hw,hl] at he
    exact ⟨hn,he⟩
  · have hdrop : word.drop k=[] := List.drop_eq_nil_of_le (by omega)
    obtain ⟨r,hr,hf,hs⟩ := past_marker_run word k cap (by omega)
    have hm := runFrom_moreFuel machine 1 (3*cap+3-1) _ r hr
    have hn : 1+(3*cap+3-1)=3*cap+3 := by omega
    rw [hn] at hm
    refine ⟨r,hm,by omega,?_,?_⟩
    · rw [hf,hdrop]
      simp [scan,cfg,readCount]
    · intro n rest hp
      rw [hdrop] at hp
      simp [readCount] at hp

end NearCubicWires.RepairOrdinary.RecoveryCertificateCount
