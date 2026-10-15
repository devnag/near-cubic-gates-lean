import Proof.MachineModel.OrdinaryWilliamsSourceSentinel

/-! Static wiring from the actual padded buffers into a fresh bank for
the supplied Williams machine. Only its two source-input tapes reuse
existing buffers; every source work tape, log and crop output is fresh. -/
namespace NearCubicWires.RepairOrdinary.WilliamsCall
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapeCount (a : WilliamsAlgorithm) := 95+a.tapeCount
def coreSlot (a : WilliamsAlgorithm) (i : Fin (a.tapeCount+1)) : Fin (tapeCount a) :=
  if i.val=0 then ⟨87,by unfold tapeCount; omega⟩
  else if i.val=1 then ⟨89,by unfold tapeCount; omega⟩
  else ⟨93+i.val,by unfold tapeCount; omega⟩
def extraSlot (a : WilliamsAlgorithm) : Fin 6 → Fin (tapeCount a) :=
  ![⟨5,by unfold tapeCount; omega⟩,⟨94+a.tapeCount,by unfold tapeCount; omega⟩,
    ⟨51,by unfold tapeCount; omega⟩,⟨12,by unfold tapeCount; omega⟩,
    ⟨81,by unfold tapeCount; omega⟩,⟨85,by unfold tapeCount; omega⟩]
def slots (a : WilliamsAlgorithm) : Fin (WilliamsSourceCrop.tapeCount a) → Fin (tapeCount a) :=
  Fin.addCases (coreSlot a) (extraSlot a)
def outputTape (a : WilliamsAlgorithm) : Fin (tapeCount a) := extraSlot a 1

theorem core_injective (a : WilliamsAlgorithm) : Function.Injective (coreSlot a) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [coreSlot] at hv
  split_ifs at hv <;> apply Fin.ext <;> simp_all <;> omega

theorem extra_injective (a : WilliamsAlgorithm) : Function.Injective (extraSlot a) := by
  intro i j h
  have hv := congrArg Fin.val h
  have ht := a.threeTapes
  fin_cases i <;> fin_cases j <;> simp [extraSlot] at hv ⊢ <;> omega

theorem core_extra_ne (a : WilliamsAlgorithm) (i : Fin (a.tapeCount+1)) (j : Fin 6) :
    coreSlot a i ≠ extraSlot a j := by
  intro h
  have hv := congrArg Fin.val h
  have ht := a.threeTapes
  fin_cases j <;> simp only [coreSlot] at hv <;> split_ifs at hv <;>
    simp [extraSlot] at hv <;> omega

theorem slots_injective (a : WilliamsAlgorithm) : Function.Injective (slots a) := by
  intro i
  refine Fin.addCases (m := a.tapeCount+1) (n := 6) (fun i => ?_) (fun i => ?_) i
  · intro j
    refine Fin.addCases (m := a.tapeCount+1) (n := 6) (fun j => ?_) (fun j => ?_) j
    · intro h
      have he : coreSlot a i=coreSlot a j := by simpa only [slots,Fin.addCases_left] using h
      have hij := core_injective a he
      subst j
      rfl
    · intro h
      have he : coreSlot a i=extraSlot a j := by simpa only [slots,Fin.addCases_left,Fin.addCases_right] using h
      exact False.elim (core_extra_ne a i j he)
  · intro j
    refine Fin.addCases (m := a.tapeCount+1) (n := 6) (fun j => ?_) (fun j => ?_) j
    · intro h
      have he : extraSlot a i=coreSlot a j := by simpa only [slots,Fin.addCases_left,Fin.addCases_right] using h
      exact False.elim (core_extra_ne a j i he.symm)
    · intro h
      have he : extraSlot a i=extraSlot a j := by simpa only [slots,Fin.addCases_right] using h
      have hij := extra_injective a he
      subst j
      rfl

theorem slots_core (a : WilliamsAlgorithm) (i : Fin (a.tapeCount+1)) :
    slots a (i.castAdd 6)=coreSlot a i := by simp [slots]
theorem slots_extra (a : WilliamsAlgorithm) (i : Fin 6) :
    slots a (WilliamsSourceCrop.extra a i)=extraSlot a i := by
  simp only [slots,WilliamsSourceCrop.extra,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.WilliamsCall
