import Proof.CaseAnalysis.WitnessSumBodyFields
import Proof.Amplification.RecoveryGatedSequence

/-! The existing gated composition retains symbolic state counts at the
sum boundary. These projections do not add instructions or tape work. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumControl
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def start {t a b : ℕ} (_p : Machine t a) (_q : Machine t b) (source : Configuration t a) :=
  controlConfig (RecoveryCalls.code (RecoveryGatedSequence.sizes a b) 0) source

theorem reject_run {t a b : ℕ} (p : Machine t a) (q : Machine t b) (bit : Fin t)
    (fuel : ℕ) (source : Configuration t a) (first : ExecutionReceipt t a)
    (hr : runFrom p fuel source=some first) (hh : first.final.heads bit=0)
    (ht : first.final.tapes bit=[false]) :
    ∃ r,runFrom (RecoveryGatedSequence.machine p q bit) (fuel+1) (start p q source)=some r ∧
      r.steps ≤ fuel+1 ∧ r.final.heads=first.final.heads ∧ r.final.tapes=first.final.tapes := by
  obtain ⟨r,run,rs,rf⟩ := RecoveryGatedSequence.reject_run p q bit fuel source first hr hh ht
  exact ⟨r,run,rs,by rw [rf];rfl,by rw [rf];rfl⟩

theorem accept_run {t a b : ℕ} (p : Machine t a) (q : Machine t b) (bit : Fin t)
    (left right : ℕ) (source : Configuration t a) (first : ExecutionReceipt t a) (last : ExecutionReceipt t b)
    (hr : runFrom p left source=some first) (hh : first.final.heads bit=0)
    (ht : first.final.tapes bit=[true])
    (hl : runFrom q right (RecoveryCalls.restarted q first.final.heads first.final.tapes)=some last) :
    ∃ r,runFrom (RecoveryGatedSequence.machine p q bit) (left+right+2) (start p q source)=some r ∧
      r.steps ≤ left+right+2 ∧ r.final.heads=last.final.heads ∧ r.final.tapes=last.final.tapes := by
  obtain ⟨r,run,rs,rf⟩ := RecoveryGatedSequence.accept_run p q bit left right source first last hr hh ht hl
  exact ⟨r,run,rs,by rw [rf];rfl,by rw [rf];rfl⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumControl
