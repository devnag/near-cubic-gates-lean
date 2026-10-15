import Proof.MachineModel.OrdinaryMatrixDimensionBinary
import Proof.MachineModel.UWalkUnary
import Proof.PCP.VerifierLookupFieldReaders

/-! The schedule's exact ceiling logarithm from a paid raw unary value.
For v≥2, clear its first cell, reuse the existing unary copy and binary
width machines, and return clog(2,v). All workspace starts blank. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Clog
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clog_eq_width (v : Nat) (hv : 2 ≤ v) : Nat.clog 2 v=natBitLength (v-1) := by
  have hlow:=Nat.pow_log_le_self 2 (show v-1≠0 by omega)
  have hhigh:=Nat.lt_pow_succ_log_self (by decide : 1 < (2 : Nat)) (v-1)
  have hl : Nat.log 2 (v-1) < Nat.clog 2 v :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
  have hh : Nat.clog 2 v ≤ Nat.log 2 (v-1)+1 := Nat.clog_le_of_le_pow (by omega)
  unfold natBitLength
  omega

theorem clear_raw (v : Nat) (hv : 1 ≤ v) : ClockJoin.ReadyRun LookupReadBit.clear 1
    (fun _=>List.replicate v true) (fun _=>CompareMachine.word (v-1)) := by
  let final : Configuration 1 2 := ⟨1,fun _=>0,fun _=>CompareMachine.word (v-1)⟩
  have hs : step LookupReadBit.clear
      (initialConfiguration LookupReadBit.clear (fun _=>List.replicate v true))=some final := by
    have he : v=v-1+1 := by omega
    rw [he,List.replicate_succ]
    simp [step,LookupReadBit.clear,initialConfiguration]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      simp [applyAction,writeTapeBit,final,CompareMachine.word]
  obtain ⟨r,hr,hf,ht⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],ht.le⟩

def clearSlots : Fin 1→Fin 12 := fun _=>0
def copySlots : Fin 3→Fin 12 := ![0,1,2]
def binarySlots : Fin 10→Fin 12 := ![1,3,4,5,6,7,8,9,10,11]
noncomputable def clear := RecoveryFocus.machine clearSlots LookupReadBit.clear
noncomputable def copy := RecoveryFocus.machine copySlots (UWalkUnary.machine false false)
noncomputable def binary := RecoveryFocus.machine binarySlots MatrixDimensionBinary.resetMachine
noncomputable def machine := Composition.machine (Composition.machine clear copy) binary
def input (v : Nat) : Fin 12→List Bool := fun i=>if i=0 then List.replicate v true else []
def marked (v : Nat) : Fin 12→List Bool := fun i=>if i=0 then CompareMachine.word (v-1) else []
noncomputable def middle (v : Nat) := install copySlots (marked v) (UWalkUnary.result false false 0 (v-1))
def budget (v : Nat) := 1+1+(2*(v-1)+6)+1+(16*(v-1)^2+72*(v-1)+32)

theorem clog_run (v : Nat) (hv : 2 ≤ v) : ∃ out,
    ClockJoin.ReadyRun machine (budget v) (input v) out ∧
      out 10=CompareMachine.word (Nat.clog 2 v) := by
  have hm:=(clear_raw v (by omega)).focus clearSlots (by decide) (input v) (by intro i; fin_cases i; rfl)
  have he : install clearSlots (input v) (fun _=>CompareMachine.word (v-1))=marked v := by
    funext i
    by_cases hi : i=0
    · subst i
      change install clearSlots _ _ (clearSlots 0)=_
      rw [install_slot _ (by decide)]
      rfl
    · rw [install_other _ _ _ _ (by intro j hj; exact hi hj.symm)]
      simp [input,marked,hi]
  rw [he] at hm
  have hc:=(UWalkUnary.ready false false 0 (v-1)).focus copySlots (by decide) (marked v) (by
    intro i; fin_cases i
    · simp [marked,copySlots,UWalkUnary.input,UWalkUnary.source,ZeroPadding.pad_zero]
    all_goals rfl)
  change ClockJoin.ReadyRun copy (2*(v-1)+6) (marked v) (middle v) at hc
  obtain ⟨r,hr,_,_,_,_,hw,hh,ht⟩:=MatrixDimensionBinary.reset_run (v-1) (by omega)
  have hb : ClockJoin.ReadyRun MatrixDimensionBinary.resetMachine
      (16*(v-1)^2+72*(v-1)+32) (MatrixDimensionBinary.resetInput (v-1)) r.final.tapes :=
    ⟨r,hr,rfl,hh,ht⟩
  have hbf:=hb.focus binarySlots (by decide) (middle v) (by
    intro i; fin_cases i
    · change install copySlots _ _ (copySlots 1)=_
      rw [install_slot _ (by decide)]
      simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead]
      rfl
    all_goals
      rw [middle,install_other _ _ _ _ (by decide)]
      rfl)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hm hc) hbf,?_⟩
  change install binarySlots _ _ (binarySlots 8)=_
  rw [install_slot _ (by decide),hw,clog_eq_width v hv]

theorem budget_bound (v : Nat) : budget v ≤ 128*(v+1)^2 := by
  have hv : v-1 ≤ v := Nat.sub_le _ _
  have hp : (v-1)^2 ≤ v^2 := Nat.pow_le_pow_left hv 2
  unfold budget
  nlinarith

end NearCubicWires.RepairSource.CloseoutSchedule.Clog
