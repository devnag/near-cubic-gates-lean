import Proof.PCP.PCPSerializerCapacityPower

/-! Two fixed polynomial drivers share the retained raw W input and have
disjoint paid scratch. The actual consumer needs no separate D/L drivers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCapacityDrivers.Powers
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def cSlots (j : Fin (DimensionPolynomial.tapes 2)) : Fin 43:=j.castAdd 25
def bSlots (j : Fin (DimensionPolynomial.tapes 6)) : Fin 43:=
  if j.val=0 then 0 else ⟨j.val+17,by have hj:=j.isLt;dsimp [DimensionPolynomial.tapes] at hj;omega⟩
theorem c_injective : Function.Injective cSlots:=by
  intro i j he;exact Fin.ext (congrArg (fun k : Fin 43=>k.val) he)
theorem b_injective : Function.Injective bSlots:=by
  intro i j he
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [bSlots] at hv
  split_ifs at hv <;>dsimp at hv <;>omega
def input (W : ℕ) (j : Fin 43):=if j.val=0 then List.replicate W true else []
def first (C : ℕ):=RecoveryFocus.machine cSlots (PCPSerializerCapacity.Power.machine 2 C)
def last (B : ℕ):=RecoveryFocus.machine bSlots (PCPSerializerCapacity.Power.machine 6 B)
def machine (C B : ℕ):=Composition.machine (first C) (last B)
def budget (C B W : ℕ):=PCPSerializerCapacity.Power.budget 2 C W+1+
  PCPSerializerCapacity.Power.budget 6 B W

theorem second_input (W : ℕ) (out : Fin (DimensionPolynomial.tapes 2)→List Bool)
    (h0 : out ⟨0,by decide⟩=List.replicate W true)
    (j : Fin (DimensionPolynomial.tapes 6)) :
    install cSlots (input W) out (bSlots j)=DimensionPolynomial.input 6 W j:=by
  by_cases hj : j.val=0
  · rw [bSlots,if_pos hj]
    exact (install_slot cSlots c_injective (input W) out ⟨0,by decide⟩).trans
      (h0.trans (by simp only [DimensionPolynomial.input,hj,↓reduceIte]))
  · rw [install_other cSlots _ _ _ (by
      intro i he
      have hv:=congrArg Fin.val he
      have hi:=i.isLt
      dsimp only [cSlots,Fin.val_castAdd] at hv
      rw [bSlots,if_neg hj] at hv
      dsimp only [Fin.val_mk] at hv
      dsimp only [DimensionPolynomial.tapes] at hi
      omega)]
    simp only [bSlots,if_neg hj,input,Fin.val_mk,DimensionPolynomial.input]
    rw [if_neg (by omega)]

theorem run (C B W : ℕ) : ∃ out,ClockJoin.ReadyRun (machine C B) (budget C B W) (input W) out ∧
    out 0=List.replicate W true ∧ out 7=List.replicate (C*(W+1)^2) true ∧
      out 32=List.replicate (B*(W+1)^6) true:=by
  obtain ⟨c,hc,hW,hC⟩:=PCPSerializerCapacity.Power.capacity_run 2 C W
  have firstReady:=hc.focus cSlots c_injective (input W) (by intro j;rfl)
  let middle:=install cSlots (input W) c
  obtain ⟨b,hb,hW',hB⟩:=PCPSerializerCapacity.Power.capacity_run 6 B W
  have lastReady:=hb.focus bSlots b_injective middle (second_input W c hW)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ firstReady lastReady,?_,?_,?_⟩
  · exact (install_slot bSlots b_injective middle b ⟨0,by decide⟩).trans hW'
  · have outside : ∀ j,bSlots j≠7:=by
      intro j he
      have hv:=congrArg Fin.val he
      dsimp only [bSlots] at hv
      split_ifs at hv <;>dsimp at hv <;>omega
    exact (install_other bSlots middle b 7 outside).trans
      ((install_slot cSlots c_injective (input W) c (PCPSerializerCapacity.Power.outputSlot 2)).trans hC)
  · exact (install_slot bSlots b_injective middle b (PCPSerializerCapacity.Power.outputSlot 6)).trans hB

end
end NearCubicWires.RepairOrdinary.RecoveryCapacityDrivers.Powers
