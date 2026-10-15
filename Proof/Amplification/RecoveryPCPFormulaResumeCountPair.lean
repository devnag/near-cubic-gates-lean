import Proof.Amplification.RecoveryPCPFormulaResumeCountCold

/-! Retain both actual exponential drivers: the final-row split uses
Compare.word (2^R-1), and the cold tautology prefix uses raw unary 2^R. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCountPair
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstSlots (i : Fin 7) : Fin 9 := i.castAdd 2
def copySlots : Fin 3→Fin 9 := ![4,7,8]
theorem first_injective : Function.Injective firstSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 9=>i.val) h)
theorem copy_injective : Function.Injective copySlots := by decide
noncomputable def first := RecoveryFocus.machine firstSlots RecoveryPCPFormulaResumeCountCold.readyMachine
noncomputable def last := RecoveryFocus.machine copySlots (UWalkUnary.machine false true)
noncomputable def machine := Composition.machine first last
def input (R : Nat) (i : Fin 9) : List Bool := if i=0 then CompareMachine.word R else []
def budget (R : Nat) := RecoveryPCPFormulaResumeCountCold.budget R+1+(2*(2^R-1)+6)

theorem counts_ready (R : Nat) : ∃ out,
    ClockJoin.ReadyRun machine (budget R) (input R) out ∧
      out 0=CompareMachine.word R ∧ out 4=CompareMachine.word (2^R-1) ∧
      out 7=List.replicate (2^R) true := by
  obtain ⟨counts,hcounts,c0,c4⟩ := RecoveryPCPFormulaResumeCountCold.count_ready R
  let mid:=install firstSlots (input R) counts
  have hfirst:=hcounts.focus firstSlots first_injective (input R) (by intro i; fin_cases i <;> rfl)
  have hlast:=(UWalkUnary.ready false true 0 (2^R-1)).focus copySlots copy_injective mid (by
    intro i
    fin_cases i
    · change install firstSlots _ _ (firstSlots 4)=UWalkUnary.source 0 (2^R-1)
      rw [install_slot firstSlots first_injective,c4,UWalkUnary.source,ZeroPadding.pad_zero]
    · dsimp only [mid]
      rw [install_other _ _ _ _ (by
        intro j h
        have hv:=congrArg (fun i : Fin 9=>i.val) h
        change j.val=7 at hv
        have hj:=j.isLt; omega)]
      rfl
    · dsimp only [mid]
      rw [install_other _ _ _ _ (by
        intro j h
        have hv:=congrArg (fun i : Fin 9=>i.val) h
        change j.val=8 at hv
        have hj:=j.isLt; omega)]
      rfl)
  let out:=install copySlots mid (UWalkUnary.result false true 0 (2^R-1))
  have whole:=ClockJoin.join first last _ _ _ _ _ hfirst hlast
  refine ⟨out,whole,?_,?_,?_⟩
  · rw [show out 0=mid 0 from install_other copySlots _ _ 0 (by decide)]
    exact (install_slot firstSlots first_injective (input R) counts 0).trans c0
  · have h:=install_slot copySlots copy_injective mid (UWalkUnary.result false true 0 (2^R-1)) 0
    exact h.trans (ZeroPadding.pad_zero _)
  · have h:=install_slot copySlots copy_injective mid (UWalkUnary.result false true 0 (2^R-1)) 1
    change out 7=[]++List.replicate (2^R-1+1) true at h
    have he : 2^R-1+1=2^R := by have hp:=Nat.two_pow_pos R; omega
    simpa only [List.nil_append,he] using h

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCountPair
