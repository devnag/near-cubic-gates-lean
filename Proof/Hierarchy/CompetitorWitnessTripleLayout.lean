import Proof.Amplification.RecoveryFixedUnpair
import Proof.Foundations.SourceCore
import Proof.Circuits.CanonicalWitnessCodec

/-! The actual canonical recovery witness begins with one fixed tagged
triple. Six ordinary cold unpairs extract it on every input word, with fresh
workspace and the original field width. This is the literal parser entry;
no natural-valued decoder is a machine instruction. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessTriple
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 6) (i : Fin 21) : Fin 122 :=
  if i.val=0 then
    if j.val=0 then 1 else ⟨20*(j.val-1)+19,by omega⟩
  else ⟨20*j.val+i.val+1,by omega⟩

theorem slots_injective (j : Fin 6) : Function.Injective (slots j) := by
  intro i k h
  have hv := congrArg Fin.val h
  simp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> simp_all <;> omega

def word (bits : List Bool) : ℕ → List Bool
  | 0 => bits
  | k+1 => RecoveryFixedUnpair.rightWord (word bits k)

theorem word_length (bits : List Bool) (k : ℕ) : (word bits k).length=bits.length := by
  induction k with
  | zero => rfl
  | succ k ih => exact (RecoveryFixedUnpair.word_lengths (word bits k)).2.trans ih

def input (x bits : List Bool) (i : Fin 122) : List Bool :=
  if i.val=0 then frame x else if i.val=1 then frame bits else []
noncomputable def stage (x bits : List Bool) : ℕ → Fin 122 → List Bool
  | 0 => input x bits
  | k+1 => if hk : k<6 then
      install (slots ⟨k,hk⟩) (stage x bits k) (RecoveryFixedUnpair.output3 (word bits k))
    else stage x bits k

theorem stage_blank (x bits : List Bool) (k : ℕ) (i : Fin 122)
    (hi : 20*k+1 < i.val) : stage x bits k i=[] := by
  induction k with
  | zero => simp [stage,input,show i.val≠0 by omega,show i.val≠1 by omega]
  | succ k ih =>
    rw [stage]
    split_ifs with hk
    · rw [install_other]
      · exact ih (by omega)
      · intro j h
        have hv := congrArg Fin.val h
        simp only [slots] at hv
        split_ifs at hv <;> simp_all <;> omega
    · exact ih (by omega)

theorem stage_source (x bits : List Bool) (j : Fin 6) :
    stage x bits j.val (slots j 0)=frame (word bits j.val) := by
  obtain ⟨j,hj⟩ := j
  cases j with
  | zero => rfl
  | succ j =>
    rw [stage,dif_pos (show j<6 by omega)]
    have he : slots ⟨j+1,hj⟩ 0=slots ⟨j,by omega⟩ 18 := by
      apply Fin.ext
      simp [slots]
    rw [he,install_slot _ (slots_injective _)]
    rfl

theorem stage_input (x bits : List Bool) (j : Fin 6) (i : Fin 21) :
    stage x bits j.val (slots j i)=RecoveryFixedUnpair.input (word bits j.val) i := by
  by_cases hi : i.val=0
  · have he : i=0 := Fin.ext hi
    subst i
    exact stage_source x bits j
  · rw [RecoveryFixedUnpair.input,if_neg hi]
    apply stage_blank
    simp [slots,hi]
    omega

noncomputable def program (j : Fin 6) := RecoveryFocus.machine (slots j) RecoveryFixedUnpair.machine

theorem step_ready (x bits : List Bool) (j : Fin 6) :
    ReadyRun (program j) (RecoveryFixedUnpair.time (word bits j.val))
      (stage x bits j.val) (stage x bits (j.val+1)) := by
  have h := (RecoveryFixedUnpair.fixed_unpair_ready (word bits j.val)).focus
    (slots j) (slots_injective j) (stage x bits j.val) (stage_input x bits j)
  simpa only [stage,dif_pos j.isLt,program] using h

end NearCubicWires.RepairOrdinary.CompetitorWitnessTriple
