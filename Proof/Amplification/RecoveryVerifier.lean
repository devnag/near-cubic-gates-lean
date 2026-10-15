import Proof.Amplification.RecoveryReturnScanned

/-! The selected cold verifier executes from the original two inputs and
blank workspace. Acceptance requires both successful cold preparation and
the actual all-code check, including every rejected preparation branch. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdVerifier
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle RecoveryColdAllCode
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body := RecoveryGatedSequence.machine RecoveryColdCompact.coldProgram checkerProgram 277
def bodyBudget (bits word : List Bool) :=
  RecoveryColdCompact.coldBudget bits word+checkerBudget bits+2
def mask (bits : Fin 493→Bool) := bits 277 && bits 127
noncomputable def machine := RecoveryReturnScanned.machine body mask
noncomputable def accepting := RecoveryReturnBit.accepting (RecoveryColdFront.stateCount body)
def budget (bits word : List Bool) := bodyBudget bits word+2

theorem body_run (code : Nat) (word : List Bool) :
    ∃ r,run body (bodyBudget code.bits word) (RecoveryColdCompact.input code.bits word)=some r ∧
      (mask r.final.scanned=true → correctedSat code=true) := by
  obtain ⟨bit,first,hfirst,_,hh,ht,hgood⟩ := RecoveryColdCompact.cold_run code.bits word
  cases hb : bit with
  | false=>
    have hfalse : first.final.tapes 277=[false] := ht.trans (congrArg (fun b=>[b]) hb)
    obtain ⟨r,hr,_,hrh,hrt⟩ := initial_reject RecoveryColdCompact.coldProgram checkerProgram 277
      (RecoveryColdCompact.coldBudget code.bits word) _ first hfirst hh hfalse
    have hle : RecoveryColdCompact.coldBudget code.bits word+1≤bodyBudget code.bits word := by
      unfold bodyBudget
      omega
    have hm := run_moreFuel body (RecoveryColdCompact.coldBudget code.bits word+1)
      (bodyBudget code.bits word-(RecoveryColdCompact.coldBudget code.bits word+1)) _ r hr
    rw [Nat.add_sub_of_le hle] at hm
    refine ⟨r,hm,?_⟩
    intro ha
    have hg : r.final.scanned 277=false := by
      change readTapeBit (r.final.tapes 277) (r.final.heads 277)=false
      rw [hrh,hrt,hh,hfalse]
      rfl
    have hf : mask r.final.scanned=false := by simp only [mask,hg,Bool.false_and]
    exact False.elim (Bool.false_ne_true (hf.symm.trans ha))
  | true=>
    have htrue : first.final.tapes 277=[true] := ht.trans (congrArg (fun b=>[b]) hb)
    obtain ⟨answer,last,hlast,_,hscan,hlh,hlt,hsound⟩ := checker_call code word
      first.final.heads first.final.tapes (hgood hb)
    obtain ⟨r,hr,_,hrh,hrt⟩ := initial_accept RecoveryColdCompact.coldProgram checkerProgram 277
      (RecoveryColdCompact.coldBudget code.bits word) (checkerBudget code.bits)
      _ first last hfirst hh htrue hlast
    refine ⟨r,hr,?_⟩
    intro ha
    apply hsound
    have hs : r.final.scanned=last.final.scanned := by
      funext i
      change readTapeBit (r.final.tapes i) (r.final.heads i)=_
      rw [hrh,hrt]
      rfl
    change (r.final.scanned 277 && r.final.scanned 127)=true at ha
    rw [Bool.and_eq_true] at ha
    have hc : r.final.scanned 127=true := ha.2
    rw [hs,hscan] at hc
    exact hc

theorem cold_run (code : Nat) (word : List Bool) :
    ∃ r,run machine (budget code.bits word) (RecoveryColdCompact.input code.bits word)=some r ∧
      r.steps≤budget code.bits word ∧
      (accepting r.final.control=true → correctedSat code=true) := by
  obtain ⟨first,hfirst,hsound⟩ := body_run code word
  obtain ⟨r,hr,ha⟩ := RecoveryReturnScanned.finish_run body mask (bodyBudget code.bits word)
    (initialConfiguration body (RecoveryColdCompact.input code.bits word)) first hfirst
  refine ⟨r,hr,runFrom_steps_le machine (budget code.bits word) _ r hr,?_⟩
  intro h
  exact hsound (ha.symm.trans h)

end NearCubicWires.RepairOrdinary.RecoveryColdVerifier
