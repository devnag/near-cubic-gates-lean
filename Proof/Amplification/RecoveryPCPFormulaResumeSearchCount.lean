import Proof.Amplification.RecoveryPCPFormulaResumeSearchCountFrame

/-! The already executed all-randomness counter stores 2^R-1. Its paid
successor and unary framing yield the literal requested proof length. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearchCount
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots (i : Fin 3) : Fin 4 := i.castAdd 1
def frameSlots : Fin 2→Fin 4 := ![1,3]
theorem copy_injective : Function.Injective copySlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 4=>i.val) h)
theorem frame_injective : Function.Injective frameSlots := by decide
noncomputable def first := RecoveryFocus.machine copySlots (UWalkUnary.machine true true)
noncomputable def last := RecoveryFocus.machine frameSlots frameMachine
noncomputable def machine := Composition.machine first last
def input (n : Nat) : Fin 4→List Bool := ![CompareMachine.word n,[],[],[]]
def budget (n : Nat) := 2*n+6+1+(4*(n+1)+6)

theorem count_ready (n : Nat) : ∃ out,
    ClockJoin.ReadyRun machine (budget n) (input n) out ∧
      out 0=CompareMachine.word n ∧ out 3=frame (List.replicate (n+1) true) := by
  let mid:=install copySlots (input n) (UWalkUnary.result true true 0 n)
  have ha:=(UWalkUnary.ready true true 0 n).focus copySlots copy_injective (input n) (by
    intro i; fin_cases i <;> simp [input,copySlots,UWalkUnary.input,UWalkUnary.source,ZeroPadding.pad_zero])
  have m0 : mid 0=CompareMachine.word n := by
    rw [show mid 0=(UWalkUnary.result true true 0 n) 0 from install_slot copySlots copy_injective _ _ 0]
    simp [UWalkUnary.result,UWalkUnary.source,ZeroPadding.pad_zero]
  have m1 : mid 1=CompareMachine.word (n+1) := by
    rw [show mid 1=(UWalkUnary.result true true 0 n) 1 from install_slot copySlots copy_injective _ _ 1]
    rfl
  have m3 : mid 3=[] := install_other copySlots (input n) _ 3 (by
    intro i h
    have hv:=congrArg (fun i : Fin 4=>i.val) h
    have hi:=i.isLt
    change i.val=3 at hv
    omega)
  have hb:=(frame_ready (n+1)).focus frameSlots frame_injective mid (by
    intro i; fin_cases i
    · exact m1
    · exact m3)
  let out:=install frameSlots mid (frameOutput (n+1))
  refine ⟨out,ClockJoin.join first last _ _ _ _ _ ha hb,?_,?_⟩
  · exact (install_other frameSlots mid _ 0 (by decide)).trans m0
  · exact install_slot frameSlots frame_injective mid (frameOutput (n+1)) 1

theorem proof_count_ready (R : Nat) : ∃ out,
    ClockJoin.ReadyRun machine (budget (2^R-1)) (input (2^R-1)) out ∧
      out 0=CompareMachine.word (2^R-1) ∧ out 3=frame (List.replicate (2^R) true) := by
  have hp : 0<(2 : Nat)^R := Nat.two_pow_pos R
  obtain ⟨out,hr,h0,h3⟩ := count_ready (2^R-1)
  rw [Nat.sub_add_cancel (by omega)] at h3
  exact ⟨out,hr,h0,h3⟩

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearchCount
