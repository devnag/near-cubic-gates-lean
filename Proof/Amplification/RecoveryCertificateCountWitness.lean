import Proof.Amplification.RecoveryValuationTableSemantics

/-! The physical capped count parser supplies the literal reusable repeat
driver and exact next witness position on every successful parse. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCertificateCount
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem readCount_some (cap n : Nat) (word rest : List Bool)
    (h : readCount cap word=some (n,rest)) :
    n≤cap ∧ word=List.replicate n true++false::rest := by
  rw [readCount_eq] at h
  cases hu : unary word with
  | none => rw [hu] at h; contradiction
  | some pair =>
    rcases pair with ⟨count,tail⟩
    rw [hu] at h
    change (if count≤cap then some (count,tail) else none)=some (n,rest) at h
    by_cases hc : count≤cap
    · rw [if_pos hc] at h
      have he := Option.some.inj h
      cases he
      exact ⟨hc,UnaryMachine.unary_decomposition hu⟩
    · rw [if_neg hc] at h
      contradiction

theorem bounded_witness (cap : Nat) (pre word : List Bool) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom machine (3*cap+3) (scan 0 (pre++frame word) pre.length 0 cap)=some r ∧
      r.steps≤3*cap+3 ∧ (r.final.control=3 ↔ (readCount cap word).isSome=true) ∧
      ∀ n rest,readCount cap word=some (n,rest) →
        n≤cap ∧ r.final=cfg 3 (pre++frame word) (pre.length+2*n+2) n cap 1 := by
  obtain ⟨r,hr,hc⟩ := bounded_parse cap pre word
  refine ⟨r,hr,runFrom_steps_le machine _ _ r hr,hc,?_⟩
  intro n rest hp
  obtain ⟨hn,hw⟩ := readCount_some cap n word rest hp
  obtain ⟨r',hr',hf',_⟩ := parse_run n cap pre rest hn
  rw [←hw] at hr'
  have hcost : 3*n+3≤3*cap+3 := by omega
  have hm := runFrom_moreFuel machine (3*n+3) (3*cap+3-(3*n+3)) _ r' hr'
  rw [Nat.add_sub_of_le hcost,hr] at hm
  have he : r=r' := Option.some.inj hm
  subst r'
  exact ⟨hn,by simpa only [←hw] using hf'⟩

end NearCubicWires.RepairOrdinary.RecoveryCertificateCount
