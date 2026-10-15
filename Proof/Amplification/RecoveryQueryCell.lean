import Proof.Amplification.RecoveryCanonicalChoice
import Proof.PCP.PCPPRequestPair

/-! Reuse the actual canonical pair and pair-successor machines for the
fixed legacy query spine.  Both operations include their zero operands. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryCell
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairSlots (i : Fin 38) : Fin 39 := ⟨i.val,by omega⟩
theorem pair_injective : Function.Injective pairSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 39 => k.val) h)
noncomputable def machine (successor : Bool) : Σ s,Machine 39 s :=
  if successor then ⟨_,RecoveryQueryPairSuccessor.machine⟩
  else ⟨_,RecoveryFocus.machine pairSlots PCPPRequestPair.machine⟩
def result (successor : Bool) (a b : Nat) := Nat.pair a b+successor.toNat
def input (a b : Nat) : Fin 39→List Bool := RecoveryQueryPairSuccessor.input a.bits b.bits
def budget (successor : Bool) (a b : Nat) :=
  if successor then RecoveryQueryPairSuccessor.budget a.bits b.bits else PCPPRequestPair.budget a b

theorem run (successor : Bool) (a b : Nat) :
    ∃ out : Fin 39→List Bool,
      ClockJoin.ReadyRun (machine successor).2 (budget successor a b) (input a b) out ∧
      ∃ padding,out 26=frame (result successor a b).bits++List.replicate padding false := by
  cases successor
  · obtain ⟨out,hr,hf,_⟩ := PCPPRequestPair.pair_run a b
    have h := hr.focus pairSlots pair_injective (input a b)
      (by intro j; fin_cases j <;> rfl)
    refine ⟨_,h,?_⟩
    obtain ⟨padding,hfield⟩ := hf
    exact ⟨padding,(install_slot _ pair_injective _ _ 26).trans hfield⟩
  · obtain ⟨out,hr,hf,_⟩ := RecoveryQueryPairSuccessor.pair_successor_run a.bits b.bits
    refine ⟨out,hr,?_⟩
    simpa only [result,Bool.toNat_true,CanonicalPositiveOutput.nat_bits_value] using hf

theorem budget_quadratic (successor : Bool) (a b : Nat) :
    budget successor a b ≤ 4096*(a.bits.length+b.bits.length+1)^2 := by
  have hp := PCPPairCold.budget_quadratic a.bits b.bits
  have hq := PCPPairCanonical.budget_quadratic a.bits b.bits
  have hh : 1 ≤ a.bits.length+b.bits.length+1 := by omega
  cases successor
  · simp only [budget,Bool.false_eq_true,if_false,PCPPRequestPair.budget]
    nlinarith
  · simp only [budget,if_true,RecoveryQueryPairSuccessor.budget,PCPPair.width]
    nlinarith

end NearCubicWires.RepairOrdinary.RecoveryQueryCell
