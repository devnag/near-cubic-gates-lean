import Proof.MachineModel.OrdinaryMatrixScorePower
import Proof.MachineModel.UWalkUnary

/-! A paid exponential unary capacity from a raw unary exponent. Reuse the
existing power producer, rewind it, and copy its produced unary template.
This is confined to C.12 recovery, where exponential output is permitted. -/
namespace NearCubicWires.RepairSource.CloseoutCapacity.Power
open LocalBitMultitape RepairOrdinary RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def sourceSlots : Fin 15→Fin 17 := fun i=>i.castAdd 2
def copySlots : Fin 3→Fin 17 := ![13,15,16]
theorem source_injective : Function.Injective sourceSlots := by
  intro a b h
  have hv:=congrArg (fun i : Fin 17=>i.val) h
  exact Fin.ext hv
def source := RecoveryFocus.machine sourceSlots (Rewind.machine MatrixScorePower.machine)
def copy := RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
def machine := Composition.machine source copy
def input (d : Nat) : Fin 17→List Bool := fun i=>if i.val=0 then List.replicate d true else []
def budget (d : Nat) := (2*MatrixScorePower.budget d+2)+1+(2*2^d+6)

theorem template_source (n : Nat) : UWalkUnary.source (n+2) n=UnaryTemplate.tape n := by
  simp [UWalkUnary.source,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem power_run (d : Nat) : ∃ out,
    ClockJoin.ReadyRun machine (budget d) (input d) out ∧
      out 15=List.replicate (2^d) true ∧ out 13=UnaryTemplate.tape (2^d) := by
  obtain ⟨a,ha,_,_,_,hat,_,_,hs⟩:=MatrixScorePower.power_run d
  obtain ⟨r,hr,rt,rh,rs,_⟩:=Rewind.reset_run MatrixScorePower.machine _ _ a ha
  have hp : ClockJoin.ReadyRun (Rewind.machine MatrixScorePower.machine) (2*a.steps+2)
      (Fin.addCases (motive:=fun _ : Fin 15=>List Bool) (MatrixScorePower.input d) (fun _ : Fin 1=>[]))
      r.final.tapes := ⟨r,hr,rfl,rh,rs.le⟩
  have hbig:=ClockJoin.enlarge _ _ _ _ _ hp (by omega : 2*a.steps+2 ≤ 2*MatrixScorePower.budget d+2)
  have hsf:=hbig.focus sourceSlots source_injective (input d) (by
    intro i;fin_cases i <;> rfl)
  let middle:=install sourceSlots (input d) r.final.tapes
  change ClockJoin.ReadyRun source (2*MatrixScorePower.budget d+2) (input d) middle at hsf
  have hm : middle 13=UnaryTemplate.tape (2^d) := by
    change install sourceSlots _ _ (sourceSlots 13)=_
    rw [install_slot _ source_injective]
    exact (rt 13).trans hat
  have hcf:=(UWalkUnary.ready false false (2^d+2) (2^d)).focus copySlots (by decide) middle (by
    intro i;fin_cases i
    · change middle 13=UWalkUnary.source (2^d+2) (2^d)
      rw [template_source]
      exact hm
    all_goals
      dsimp only [middle]
      rw [install_other _ _ _ _ (by
        intro j hj;have h:=congrArg Fin.val hj;have:=j.isLt;dsimp [sourceSlots,copySlots] at h;omega)]
      rfl)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hsf hcf,?_,?_⟩
  · change install copySlots _ _ (copySlots 1)=_
    rw [install_slot _ (by decide)]
    simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead]
  · change install copySlots _ _ (copySlots 0)=_
    rw [install_slot _ (by decide)]
    exact template_source (2^d)

end
end NearCubicWires.RepairSource.CloseoutCapacity.Power
