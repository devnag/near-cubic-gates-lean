import Proof.Amplification.RecoveryAllCodeState

/-! The selected prepared checker supplies both literal child runs.
Each accepting child already proves corrected SAT of the same code. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAllCode
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem raw_run (x : State) (limit : Nat) (word : List Bool) (k : Nat)
    (innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word k innerBits outerBits innerPre outerPre) :
    ∃ r,runFrom RecoveryRawBranch.machine (RecoveryRawBranch.budget x.width)
      (RecoveryRawBranch.cfg x.raw 0 RecoveryRawBranch.machine.start)=some r ∧
      r.final.heads 93=0 ∧ r.final.tapes 93=[RecoveryRawBranch.answer x.raw word k] ∧
      (r.final.tapes 93=[true] → correctedSat x.code=true) := by
  obtain ⟨r,hr,_,hh,ht,hs⟩ := RecoveryRawBranch.accepted_raw_run x.raw word k hx.raw_valid hx.raw_source hx.raw_pos
    hx.raw_eval hx.raw_code hx.raw_tags hx.raw_bound
  exact ⟨r,hr,hh,ht,hs⟩

theorem compact_run (x : State) (limit : Nat) (word : List Bool) (k : Nat)
    (innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word k innerBits outerBits innerPre outerPre) :
    ∃ r,runFrom RecoveryCompactBranch.machine (RecoveryCompactBranch.budget x.width)
      (RecoveryMarkerHandoff.cfg x.marker x.compact RecoveryCompactBranch.machine.start)=some r ∧
      r.final.heads 107=0 ∧ (∃ bit,r.final.tapes 107=[bit]) ∧
      (r.final.tapes 107=[true] → correctedSat x.code=true) := by
  obtain ⟨table,rest,hp⟩ := hx.valuation_parse
  obtain ⟨r,hr,_,hh,ht,hs⟩ := RecoveryCompactBranch.compact_run x.marker x.compact limit word
    innerBits outerBits innerPre outerPre hx.compact_ready hx.limit_bound hx.marker_valid hx.marker_width
    hx.committed_zero hx.count_zero table rest hp
  rw [hx.width_eq] at hr
  rw [hx.code_eq] at hs
  exact ⟨r,hr,hh,ht,hs⟩

end NearCubicWires.RepairOrdinary.RecoveryAllCode
