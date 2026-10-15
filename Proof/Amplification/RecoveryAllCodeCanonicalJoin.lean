import Proof.Amplification.RecoveryAllCodeWhole

/-! Canonical acceptance joins at the literal executed child boundary.
The chosen child's existing canonical run and the other child's general
run imply acceptance by the same fixed all-code machine. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAllCode
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem accept_left (x : State) (limit : Nat) (word : List Bool) (k : Nat)
    (innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word k innerBits outerBits innerPre outerPre)
    (left : ExecutionReceipt 136 _)
    (hl : runFrom RecoveryRawBranch.machine (RecoveryRawBranch.budget x.width)
      (RecoveryRawBranch.cfg x.raw 0 RecoveryRawBranch.machine.start)=some left)
    (hlh : left.final.heads 93=0) (hlt : left.final.tapes 93=[true]) :
    ∃ r,runFrom machine (budget x.width) (cfg x machine.start)=some r ∧
      r.steps ≤ 4294967296*(x.width+1)^4 ∧ r.final.heads 93=0 ∧ r.final.tapes 93=[true] := by
  obtain ⟨right,hr,hrh,⟨bit,hrt⟩,_⟩ := compact_run x limit word k innerBits outerBits innerPre outerPre hx
  obtain ⟨r,hrun,hsteps,hh,ht⟩ := RecoveryBranchDisjunction.joined_run RecoveryRawBranch.machine RecoveryCompactBranch.machine
    (93 : Fin 136) (107 : Fin 212) (RecoveryRawBranch.cfg x.raw 0 (0 : Fin 1)).heads
    (RecoveryRawBranch.cfg x.raw 0 (0 : Fin 1)).tapes (RecoveryMarkerHandoff.heads x.compact)
    (RecoveryMarkerHandoff.tapes x.marker x.compact) (RecoveryRawBranch.budget x.width)
    (RecoveryCompactBranch.budget x.width) left right hl hr true bit hlh hlt hrh hrt
  change r.final.tapes 93=[true || bit] at ht
  rw [Bool.true_or] at ht
  exact ⟨r,hrun,hsteps.trans (budget_le x.width),hh,ht⟩

theorem accept_right (x : State) (limit : Nat) (word : List Bool) (k : Nat)
    (innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word k innerBits outerBits innerPre outerPre)
    (right : ExecutionReceipt 212 _)
    (hr : runFrom RecoveryCompactBranch.machine (RecoveryCompactBranch.budget x.width)
      (RecoveryMarkerHandoff.cfg x.marker x.compact RecoveryCompactBranch.machine.start)=some right)
    (hrh : right.final.heads 107=0) (hrt : right.final.tapes 107=[true]) :
    ∃ r,runFrom machine (budget x.width) (cfg x machine.start)=some r ∧
      r.steps ≤ 4294967296*(x.width+1)^4 ∧ r.final.heads 93=0 ∧ r.final.tapes 93=[true] := by
  obtain ⟨left,hl,hlh,hlt,_⟩ := raw_run x limit word k innerBits outerBits innerPre outerPre hx
  obtain ⟨r,hrun,hsteps,hh,ht⟩ := RecoveryBranchDisjunction.joined_run RecoveryRawBranch.machine RecoveryCompactBranch.machine
    (93 : Fin 136) (107 : Fin 212) (RecoveryRawBranch.cfg x.raw 0 (0 : Fin 1)).heads
    (RecoveryRawBranch.cfg x.raw 0 (0 : Fin 1)).tapes (RecoveryMarkerHandoff.heads x.compact)
    (RecoveryMarkerHandoff.tapes x.marker x.compact) (RecoveryRawBranch.budget x.width)
    (RecoveryCompactBranch.budget x.width) left right hl hr (RecoveryRawBranch.answer x.raw word k) true hlh hlt hrh hrt
  change r.final.tapes 93=[RecoveryRawBranch.answer x.raw word k || true] at ht
  rw [Bool.or_true] at ht
  exact ⟨r,hrun,hsteps.trans (budget_le x.width),hh,ht⟩

end NearCubicWires.RepairOrdinary.RecoveryAllCode
