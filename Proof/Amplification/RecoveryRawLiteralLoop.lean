import Proof.Amplification.RecoveryRawLiteralBoundMeaning

/-! Bounded literal iteration uses the actual supplied unary driver. Its
body rejects only a missing code cell and retains natural-tag invalidity. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteralLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RecoveryRawLiteralBound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def next (x : State) : Bool×State := (decide (code x≠0),output x)
noncomputable def source (x : State) := x.cfg RecoveryRawLiteralBound.machine.start
noncomputable def machine := RepeatMachine.machine RecoveryRawLiteralBound.machine (fun _ scanned=>scanned 28)
def Inv (width : Nat) (x : State) := x.Valid ∧ x.stream.width=width
def bodyBudget (width : Nat) := 2097152*(width+1)^2
def budget (width total : Nat) := total*(bodyBudget width+3)+3

theorem supplier (width : Nat) (x : State) (hx : Inv width x) :
    ∃ r,runFrom RecoveryRawLiteralBound.machine (bodyBudget width) (source x)=some r ∧
      r.steps ≤ bodyBudget width ∧ r.final.scanned 28=(next x).1 ∧
      ((next x).1=true → r.final.heads=(source (next x).2).heads ∧
        r.final.tapes=(source (next x).2).tapes ∧ Inv width (next x).2) := by
  have hrun := RecoveryRawLiteralBound.body_run x hx.1
  obtain ⟨r,hr,hf,hb⟩ := hrun
  have hc : cost x ≤ bodyBudget width := by
    have h := RecoveryRawLiteralBound.cost_bound x hx.1
    rw [hx.2] at h
    exact h
  have hm := runFrom_moreFuel RecoveryRawLiteralBound.machine (cost x) (bodyBudget width-cost x) _ r hr
  rw [Nat.add_sub_of_le hc] at hm
  refine ⟨r,hm,hb.trans hc,?_,?_⟩
  · rw [hf]
    change (output x).stream.data.present=(next x).1
    exact output_present x
  · intro _
    refine ⟨?_,?_,output_valid x hx.1,(output_width x).trans hx.2⟩
    · rw [hf]; rfl
    · rw [hf]; rfl

theorem loop_run (width total : Nat) (x : State) (hx : Inv width x) :
    ∃ r,runFrom machine (budget width total) (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps ≤ budget width total ∧
      RepeatMachine.Result source total (RepeatMachine.iterate next total x) r.final := by
  have h := RepeatMachine.rejecting_repeat_run RecoveryRawLiteralBound.machine (fun _ scanned=>scanned 28)
    source next (Inv width) (bodyBudget width) (fun _ _=>rfl) (supplier width) total x hx
  exact h

theorem budget_bound (width total : Nat) (h : total ≤ 3*(width+1)) :
    budget width total ≤ 8388608*(width+1)^3 := by
  unfold budget bodyBudget
  calc
    _ ≤ 3*(width+1)*(2097152*(width+1)^2+3)+3 := by gcongr
    _ ≤ _ := by nlinarith [show 0<(width+1)^3 by positivity]

end NearCubicWires.RepairOrdinary.RecoveryRawLiteralLoop
