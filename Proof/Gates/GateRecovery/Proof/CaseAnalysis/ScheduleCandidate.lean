import Proof.Gates.GateRecovery.Bundle
import Proof.CaseAnalysis.ScheduleSourceWord
import Proof.CaseAnalysis.CapacityPower
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleNative
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleWidthBudget

namespace GR

/-! One cold schedule candidate: actual s → word of length 2^s → actual
native q → doubled core width. Testing that width against n implements
m_s ≤ n/2 without a separate division routine. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Candidate
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def nativeTapes (sources : GateEightSources) (_k : Nat) := sources.width.tapes
def tapes (sources : GateEightSources) (k D : Nat) := 18+nativeTapes sources k+Width.tapes D
def powerSlots (sources : GateEightSources) (k D : Nat) (i : Fin 17) : Fin (tapes sources k D) :=
  ⟨i.val,by have:=i.isLt;dsimp [tapes];omega⟩
def frameSlots (sources : GateEightSources) (k D : Nat) (i : Fin 2) : Fin (tapes sources k D) :=
  ⟨if i.val=0 then 13 else 17,by dsimp [tapes];split_ifs <;> omega⟩
def nativeSlots (sources : GateEightSources) (k D : Nat) (i : Fin (nativeTapes sources k)) : Fin (tapes sources k D) :=
  ⟨if i.val=sources.width.inPort.val then 17 else 18+i.val,by have:=i.isLt;dsimp [tapes,nativeTapes] at *;split_ifs <;> omega⟩
theorem native_range (sources : GateEightSources) (k D : Nat) (i : Fin (nativeTapes sources k)) :
    17 ≤ (nativeSlots sources k D i).val ∧ (nativeSlots sources k D i).val < 18+nativeTapes sources k := by
  have:=i.isLt
  dsimp [nativeSlots,nativeTapes] at *
  split_ifs <;> omega
def widthSlots (sources : GateEightSources) (k D : Nat) (i : Fin (Width.tapes D)) : Fin (tapes sources k D) :=
  if i.val=0 then nativeSlots sources k D (nativeRaw sources k)
  else ⟨18+nativeTapes sources k+i.val,by have:=i.isLt;dsimp [tapes];omega⟩
theorem power_injective (sources : GateEightSources) (k D : Nat) : Function.Injective (powerSlots sources k D) := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (tapes sources k D)=>i.val) h)
theorem frame_injective (sources : GateEightSources) (k D : Nat) : Function.Injective (frameSlots sources k D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [frameSlots] at hv ⊢
theorem native_injective (sources : GateEightSources) (k D : Nat) : Function.Injective (nativeSlots sources k D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  dsimp only [nativeSlots] at hv
  split_ifs at hv <;> omega
theorem width_injective (sources : GateEightSources) (k D : Nat) : Function.Injective (widthSlots sources k D) := by
  intro a b h
  have hv:=congrArg Fin.val h
  have hr:=native_range sources k D (nativeRaw sources k)
  apply Fin.ext
  by_cases ha : a.val=0 <;> by_cases hb : b.val=0 <;>
    simp [widthSlots,ha,hb] at hv <;> omega

def power (sources : GateEightSources) (k D : Nat) :=
  RecoveryFocus.machine (powerSlots sources k D) CloseoutCapacity.Power.machine
def word (sources : GateEightSources) (k D : Nat) :=
  RecoveryFocus.machine (frameSlots sources k D) RecoveryPCPFormulaResumeSearchCount.frameMachine
def native (sources : GateEightSources) (k D : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) :=
  RecoveryFocus.machine (nativeSlots sources k D) (nativeMachine sources k clock)
def width (sources : GateEightSources) (k D copies ext : Nat) :=
  RecoveryFocus.machine (widthSlots sources k D) (Width.machine D (2*copies) ext)
def machine (sources : GateEightSources) (k D copies ext : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) :=
  Composition.machine (Composition.machine (Composition.machine (power sources k D) (word sources k D))
    (native sources k D clock)) (width sources k D copies ext)
def input (sources : GateEightSources) (k D s : Nat) : Fin (tapes sources k D)→List Bool :=
  fun i=>if i.val=0 then List.replicate s true else []
def budget (sources : GateEightSources) (k D copies ext : Nat) (clock : OrdinaryClock (fun n=>n^(k+2))) (s : Nat) :=
  CloseoutCapacity.Power.budget s+1+(4*2^s+6)+1+
    nativeBudget sources k clock s+1+
    Width.budget D (2*copies) ext (sources.width.width s)

theorem candidate_run (sources : GateEightSources) (k D copies ext : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (s : Nat) (hD : 1 ≤ D) : ∃ out,
    ClockJoin.ReadyRun (machine sources k D copies ext clock) (budget sources k D copies ext clock s)
      (input sources k D s) out ∧
      out (powerSlots sources k D 13)=UnaryTemplate.tape (2^s) ∧
      out (widthSlots sources k D (Width.outputSlot D))=
        List.replicate (2*CloseoutLanguage.widthAt sources k clock copies ext D s) true := by
  obtain ⟨powerOut,hp,_,ht⟩:=CloseoutCapacity.Power.power_run s
  have hpf:=hp.focus (powerSlots sources k D) (power_injective sources k D) (input sources k D s)
    (by intro i;rfl)
  let a:=install (powerSlots sources k D) (input sources k D s) powerOut
  change ClockJoin.ReadyRun (power sources k D) _ _ a at hpf
  have hwf:=(source_word (2^s)).focus (frameSlots sources k D) (frame_injective sources k D) a (by
    intro i;fin_cases i
    · change install (powerSlots sources k D) _ _ (powerSlots sources k D 13)=_
      rw [install_slot _ (power_injective sources k D)]
      exact ht
    · dsimp only [a]
      rw [install_other _ _ _ _ (by
        intro j hj;have hv:=congrArg Fin.val hj;have:=j.isLt
        dsimp [powerSlots,frameSlots] at hv;omega)]
      rfl)
  let b:=install (frameSlots sources k D) a ![UnaryTemplate.tape (2^s),frame (List.replicate (2^s) true)]
  change ClockJoin.ReadyRun (word sources k D) _ a b at hwf
  obtain ⟨nativeOut,hn,hq⟩:=native_run sources k clock s
  have hnf:=hn.focus (nativeSlots sources k D) (native_injective sources k D) b (by
    intro i
    by_cases hi : i=sources.width.inPort
    · have hv : i.val=sources.width.inPort.val := by rw [hi]
      have he : nativeSlots sources k D i=frameSlots sources k D 1 := by
        apply Fin.ext;simp [nativeSlots,frameSlots,hv]
      change b (nativeSlots sources k D i)=if i=sources.width.inPort then _ else _
      rw [if_pos hi,he]
      exact install_slot _ (frame_injective sources k D) _ _ 1
    · have hv' : i.val≠sources.width.inPort.val := fun h=>hi (Fin.ext h)
      change b (nativeSlots sources k D i)=if i=sources.width.inPort then _ else _
      rw [if_neg hi]
      dsimp only [b,a]
      rw [install_other _ _ _ _ (by
        intro j hj;have hv:=congrArg Fin.val hj
        fin_cases j <;> simp [frameSlots,nativeSlots,hv'] at hv <;> omega)]
      rw [install_other _ _ _ _ (by
        intro j hj;have hv:=congrArg Fin.val hj;have:=j.isLt
        simp only [powerSlots,nativeSlots,hv',if_false] at hv;omega)]
      simp [input,nativeSlots,hv'])
  let c:=install (nativeSlots sources k D) b nativeOut
  change ClockJoin.ReadyRun (native sources k D clock) _ b c at hnf
  obtain ⟨widthOut,hwidth,hm⟩:=Width.width_run D (2*copies) ext _ hD
  have hwidthf:=hwidth.focus (widthSlots sources k D) (width_injective sources k D) c (by
    intro i
    by_cases hi : i.val=0
    · change c (widthSlots sources k D i)=if i.val=0 then _ else _
      rw [if_pos hi]
      simp only [widthSlots,hi,↓reduceIte,c,install_slot _ (native_injective sources k D)]
      exact hq
    · change c (widthSlots sources k D i)=if i.val=0 then _ else _
      rw [if_neg hi]
      dsimp only [c,b,a]
      rw [install_other _ _ _ _ (by
        intro j hj;have hv:=congrArg Fin.val hj;have hr:=native_range sources k D j
        dsimp [widthSlots] at hv;rw [if_neg hi] at hv;dsimp at hv;omega)]
      rw [install_other _ _ _ _ (by
        intro j hj;have hv:=congrArg Fin.val hj
        fin_cases j <;> simp [frameSlots,widthSlots,hi] at hv <;> omega)]
      rw [install_other _ _ _ _ (by
        intro j hj;have hv:=congrArg Fin.val hj;have:=j.isLt
        dsimp [powerSlots,widthSlots] at hv;rw [if_neg hi] at hv;dsimp at hv;omega)]
      simp [input,widthSlots,hi])
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hpf hwf) hnf) hwidthf,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro j hj;have hv:=congrArg Fin.val hj;have hr:=native_range sources k D (nativeRaw sources k)
      by_cases hz : j.val=0 <;> simp [widthSlots,powerSlots,hz] at hv <;> omega)]
    dsimp only [c]
    rw [install_other _ _ _ _ (by
      intro j hj;have hv:=congrArg Fin.val hj;have hr:=native_range sources k D j
      change (nativeSlots sources k D j).val=13 at hv;omega)]
    change install (frameSlots sources k D) _ _ (frameSlots sources k D 0)=_
    exact install_slot _ (frame_injective sources k D) _ _ 0
  · rw [install_slot _ (width_injective sources k D),hm]
    congr 1
    unfold CloseoutLanguage.widthAt CloseoutLanguage.coreWidth
    ring

end
end NearCubicWires.RepairSource.CloseoutSchedule.Candidate

end GR
