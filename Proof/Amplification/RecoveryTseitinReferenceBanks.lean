import Proof.Amplification.RecoveryTseitinReferenceSums

/-! Four disjoint physical reference calls share the retained scalar bank.
Their canonical outputs occupy fields10–13; all arithmetic work stays in
separate fixed blocks, so no caller head or tape transport is implicit. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countSlot : Fin 4→Fin 1062 := ![4,2,6,8]
def referenceSlot (k : Fin 4) : Fin 1062 := ⟨10+k.val,by have hk:=k.isLt; omega⟩
def bankSlots (k : Fin 4) (j : Fin 262) : Fin 1062 :=
  if j=0 then referenceSlot k else if j=242 then countSlot k else
  ⟨14+262*k.val+j.val,by have hk:=k.isLt; have hj:=j.isLt; omega⟩
theorem count_small (k : Fin 4) : (countSlot k).val<9 := by fin_cases k <;> decide
theorem bank_injective (k : Fin 4) : Function.Injective (bankSlots k) := by
  intro i j he
  have h:=congrArg Fin.val he
  have hi:=i.isLt
  have hj:=j.isLt
  apply Fin.ext
  fin_cases k <;>
    dsimp only [bankSlots,referenceSlot,countSlot] at h <;>
    split_ifs at h <;> dsimp at h <;> omega
theorem disjoint (k l : Fin 4) (hk : k≠l) : ∀ i j,bankSlots k i≠bankSlots l j := by
  intro i j he
  have h:=congrArg Fin.val he
  have hi:=i.isLt
  have hj:=j.isLt
  fin_cases k <;> fin_cases l <;> first
    | exact hk rfl
    | (dsimp only [bankSlots,referenceSlot,countSlot] at h; split_ifs at h <;> dsimp at h <;> omega)

noncomputable def referencePart (k : Fin 4) := RecoveryFocus.machine (bankSlots k) RecoveryTseitinTautology.Cold.machine

theorem part_run {z : Nat} (k : Fin 4) (count : Nat) (ambient : Configuration 1062 z)
    (hh : ∀ j,ambient.heads (bankSlots k j)=0)
    (ht : ∀ j,ambient.tapes (bankSlots k j)=RecoveryTseitinTautology.Cold.driversInput count j) :
    ∃ r,runFrom (referencePart k) (RecoveryTseitinTautology.Cold.budget count)
      (Composition.restart ambient (referencePart k).start)=some r ∧
      r.final.tapes (referenceSlot k)=ZeroPadding.pad (RecoveryTseitinTautology.Cold.driverCapacity count)
        (RepairOrdinary.frame count.bits) ∧ r.final.heads (referenceSlot k)=0 ∧
      r.steps≤RecoveryTseitinTautology.Cold.budget count ∧
      (∀ l,k≠l → ∀ j,r.final.tapes (bankSlots l j)=ambient.tapes (bankSlots l j) ∧
        r.final.heads (bankSlots l j)=ambient.heads (bankSlots l j)) := by
  obtain ⟨base,hb,bt,bh,bs⟩ := RecoveryTseitinTautology.Cold.reference_run count
  obtain ⟨r,hr,_rc,rs,rh,rt,ro⟩ := RecoveryFocus.dock (bankSlots k) (bank_injective k)
    RecoveryTseitinTautology.Cold.machine _ ambient.heads ambient.tapes _ hh ht base hb
  refine ⟨r,hr,(rt 0).trans bt,(rh 0).trans bh,rs.le.trans bs,?_⟩
  intro l hkl j
  have h:=ro (bankSlots l j) (by intro a; exact disjoint k l hkl a j)
  exact ⟨h.2,h.1⟩

end NearCubicWires.RepairSource.RecoveryTseitinReferences
