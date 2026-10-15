import Proof.Amplification.RecoveryRawCountAt

/-! The count parser reuses actual zero-filled counter storage. The fixed
padding is retained in the endpoint, and is never treated as free erasure. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCertificateCount
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def paddedCfg (capacity : Nat) (q : Fin 5) (source : List Bool) (pos count cap head : Nat) :=
  ZeroPadding.config ![0,capacity,0] (cfg q source pos count cap head)

theorem empty_driver (capacity : Nat) (hc : 1 ≤ capacity) :
    ZeroPadding.pad capacity (CompareMachine.word 0)=List.replicate capacity false := by
  change [false]++List.replicate (capacity-1) false=List.replicate capacity false
  rw [show [false]=List.replicate 1 false from rfl,←List.replicate_add]
  congr 1
  omega

theorem padded_bounded_at (capacity cap : Nat) (word : List Bool) (k : Nat) :
    ∃ r,runFrom machine (3*cap+3) (paddedCfg capacity 0 (frame word) (2*k) 0 cap 1)=some r ∧
      r.steps ≤ 3*cap+3 ∧ (r.final.control=3 ↔ (readCount cap (word.drop k)).isSome=true) ∧
      ∀ n rest,readCount cap (word.drop k)=some (n,rest) →
        n ≤ cap ∧ r.final=paddedCfg capacity 3 (frame word) (2*k+2*n+2) n cap 1 := by
  obtain ⟨base,hr,hb,hc,hf⟩ := bounded_at cap word k
  obtain ⟨r,h,hfinal,hsteps,_⟩ := ZeroPadding.run_config machine ![0,capacity,0] _ _ base hr
  refine ⟨r,h,hsteps.le.trans hb,?_,?_⟩
  · simpa only [hfinal,ZeroPadding.config] using hc
  · intro n rest hp
    obtain ⟨hn,he⟩ := hf n rest hp
    refine ⟨hn,?_⟩
    rw [hfinal,he]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryCertificateCount
