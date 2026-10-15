import Proof.Amplification.RecoveryAllCodeCalls

/-! Whole prepared all-code checker. Both branch soundness theorems refer
to the original code, so the executed final OR preserves their language.
No all-witness equality to the old stronger semantic checker is needed. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAllCode
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem checker_run (x : State) (limit : Nat) (word : List Bool) (k : Nat)
    (innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word k innerBits outerBits innerPre outerPre) :
    ∃ r,runFrom machine (budget x.width) (cfg x machine.start)=some r ∧
      r.steps ≤ 4294967296*(x.width+1)^4 ∧ r.final.heads 93=0 ∧
      (∃ bit,r.final.tapes 93=[bit]) ∧
      (r.final.tapes 93=[true] → correctedSat x.code=true) := by
  obtain ⟨left,hl,hlh,hlt,hls⟩ := raw_run x limit word k innerBits outerBits innerPre outerPre hx
  obtain ⟨right,hr,hrh,⟨bit,hrt⟩,hrs⟩ := compact_run x limit word k innerBits outerBits innerPre outerPre hx
  obtain ⟨r,hrun,hsteps,hh,ht⟩ := RecoveryBranchDisjunction.joined_run RecoveryRawBranch.machine RecoveryCompactBranch.machine
    (93 : Fin 136) (107 : Fin 212) (RecoveryRawBranch.cfg x.raw 0 (0 : Fin 1)).heads
    (RecoveryRawBranch.cfg x.raw 0 (0 : Fin 1)).tapes (RecoveryMarkerHandoff.heads x.compact)
    (RecoveryMarkerHandoff.tapes x.marker x.compact) (RecoveryRawBranch.budget x.width)
    (RecoveryCompactBranch.budget x.width) left right hl hr (RecoveryRawBranch.answer x.raw word k) bit hlh hlt hrh hrt
  refine ⟨r,hrun,hsteps.trans (budget_le x.width),hh,⟨_,ht⟩,?_⟩
  intro htrue
  have hb : (RecoveryRawBranch.answer x.raw word k || bit)=true := List.singleton_inj.mp (ht.symm.trans htrue)
  rw [Bool.or_eq_true] at hb
  rcases hb with hb|hb
  · apply hls
    rw [hlt,hb]
  · apply hrs
    rw [hrt,hb]

end NearCubicWires.RepairOrdinary.RecoveryAllCode
