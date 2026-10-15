import Proof.Amplification.RecoveryOuterRootFront

/-! An actual two-call gate with a Boolean endpoint. Abstract control sizes
keep large already-checked table programs opaque to the joining proof. -/
namespace NearCubicWires.RepairOrdinary.RecoveryGatedSequence
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem boolean_run {t s u : Nat} (p : Machine t s) (q : Machine t u) (slot : Fin t)
    (b1 b2 : Nat) (source : Configuration t s) (first : ExecutionReceipt t s)
    (gate answer : Bool)
    (hr : runFrom p b1 source=some first) (hh : first.final.heads slot=0)
    (ht : first.final.tapes slot=[gate])
    (hreject : gate=false → answer=false)
    (hnext : gate=true → ∃ last,
      runFrom q b2 (RecoveryCalls.restarted q first.final.heads first.final.tapes)=some last ∧
      last.final.heads slot=0 ∧ last.final.tapes slot=[answer]) :
    ∃ r,runFrom (machine p q slot) (b1+b2+2)
        (controlConfig (RecoveryCalls.code (sizes s u) 0) source)=some r ∧
      r.steps ≤ b1+b2+2 ∧ r.final.heads slot=0 ∧ r.final.tapes slot=[answer] := by
  cases hg : gate
  · rw [hg] at ht
    obtain ⟨r,hr,hb,hf⟩ := reject_run p q slot b1 source first hr hh ht
    have hm := runFrom_moreFuel (machine p q slot) (b1+1) (b2+1) _ r hr
    have he : b1+1+(b2+1)=b1+b2+2 := by omega
    rw [he] at hm
    refine ⟨r,hm,by omega,?_,?_⟩
    · rw [hf]; exact hh
    · rw [hf]; change first.final.tapes slot=_; rw [ht,hreject hg]
  · obtain ⟨last,hl,hh1,ht1⟩ := hnext hg
    rw [hg] at ht
    obtain ⟨r,hr,hb,hf⟩ := accept_run p q slot b1 b2 source first last hr hh ht hl
    refine ⟨r,hr,hb,?_,?_⟩
    · rw [hf]; exact hh1
    · rw [hf]; exact ht1

end NearCubicWires.RepairOrdinary.RecoveryGatedSequence
