import Proof.CaseAnalysis.RecoveryCapacityDriversPowers
import Proof.CaseAnalysis.RecoveryCapacityDriversOffset

/-! The original count compiler's actual cold capacity drivers. One paid W
word supplies C and the common backing B; all work and reset logs are allocated. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCapacityDrivers
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 43) : Fin 49:=i.castAdd 6
def offsetSlots : Fin 7→Fin 49:=![32,43,44,45,46,47,48]
theorem old_injective : Function.Injective old:=by
  intro i j he;exact Fin.ext (congrArg (fun k : Fin 49=>k.val) he)
theorem offset_injective : Function.Injective offsetSlots:=by decide
def input (W : ℕ) (i : Fin 49):=if i.val=0 then List.replicate W true else []
def first (C B : ℕ):=RecoveryFocus.machine old (Powers.machine C B)
def last (J : ℕ):=RecoveryFocus.machine offsetSlots (Offset.machine J)
def program (C B J : ℕ):=Composition.machine (first C B) (last J)
def genericBudget (C B J W : ℕ):=Powers.budget C B W+1+Offset.budget J (B*(W+1)^6)

theorem generic_run (C B J W : ℕ) : ∃ out,
    ClockJoin.ReadyRun (program C B J) (genericBudget C B J W) (input W) out ∧
    out 0=List.replicate W true ∧ out 7=List.replicate (C*(W+1)^2) true ∧
    out 45=List.replicate (B*(W+1)^6+J) true ∧
    out 47=List.replicate (B*(W+1)^6+J) false ∧
    out 48=List.replicate (B*(W+1)^6+J+1) false:=by
  obtain ⟨powers,hp,hW,hC,hB⟩:=Powers.run C B W
  have hfirst:=hp.focus old old_injective (input W) (by intro j;rfl)
  let middle:=install old (input W) powers
  obtain ⟨offset,ho,_hinput,hb,hscratch,hlog⟩:=Offset.run J (B*(W+1)^6)
  have hlast:=ho.focus offsetSlots offset_injective middle (by
    intro j
    fin_cases j
    · exact (install_slot old old_injective (input W) powers 32).trans hB
    all_goals
      rw [show middle _=input W _ from install_other old (input W) powers _ (by
        intro i he
        have hi:=i.isLt
        have hv:=congrArg Fin.val he
        simp only [old,Fin.val_castAdd] at hv
        norm_num [offsetSlots] at hv
        omega)]
      rfl)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hfirst hlast,?_,?_,?_,?_,?_⟩
  · exact (install_other offsetSlots middle offset 0 (by decide)).trans
      ((install_slot old old_injective (input W) powers 0).trans hW)
  · exact (install_other offsetSlots middle offset 7 (by decide)).trans
      ((install_slot old old_injective (input W) powers 7).trans hC)
  · exact (install_slot offsetSlots offset_injective middle offset 3).trans hb
  · exact (install_slot offsetSlots offset_injective middle offset 5).trans hscratch
  · exact (install_slot offsetSlots offset_injective middle offset 6).trans hlog

def capacityC (W : ℕ):=16384*(W+1)^2
def capacityB (W : ℕ):=(33*10000000000)*(W+1)^6+64
def cSlot : Fin 49:=7
def bSlot : Fin 49:=45
def scratchSlot : Fin 49:=47
def logSlot : Fin 49:=48
def machine:=program 16384 (33*10000000000) 64
def budget (W : ℕ):=genericBudget 16384 (33*10000000000) 64 W

theorem run (W : ℕ) : ∃ out,ClockJoin.ReadyRun machine (budget W) (input W) out ∧
    out 0=List.replicate W true ∧ out cSlot=List.replicate (capacityC W) true ∧
    out bSlot=List.replicate (capacityB W) true ∧
    out scratchSlot=List.replicate (capacityB W) false ∧
    out logSlot=List.replicate (capacityB W+1) false:=
  generic_run 16384 (33*10000000000) 64 W

end
end NearCubicWires.RepairOrdinary.RecoveryCapacityDrivers
