import Proof.Amplification.RecoveryProjectionDimensionUnary
import Proof.Amplification.RecoveryProjectionNormalizedRows

/-! Physical capacity generation from the normalized width's original
binary field. The existing dimension parser produces both unary conventions;
the existing fixed fourth-power program produces the actual capacity tape. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionCapacity
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (i : Fin 7) : Fin 28 := i.castAdd 21
def powerSlots (i : Fin (DimensionPolynomial.tapes 4)) : Fin 28 :=
  if h : i.val=0 then 5 else ⟨i.val+6,by have hi:=i.isLt; dsimp [DimensionPolynomial.tapes] at hi; omega⟩
theorem native_injective : Function.Injective nativeSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 28=>i.val) h)
theorem power_injective : Function.Injective powerSlots := by
  intro a b h; apply Fin.ext
  have hv:=congrArg Fin.val h
  simp only [powerSlots] at hv
  split at hv <;> split at hv <;> dsimp at hv <;> omega

def input (bits : List Bool) (i : Fin 28) := if i=0 then RepairOrdinary.frame bits else []
noncomputable def parsed (bits : List Bool) (out : Fin 7→List Bool) := install nativeSlots (input bits) out
noncomputable def firstMachine := RecoveryFocus.machine nativeSlots RecoveryProjectionDimension.machine
noncomputable def powerMachine (C : Nat) := RecoveryFocus.machine powerSlots (PCPSerializerCapacity.Power.machine 4 C)
noncomputable def machine (C : Nat) := Composition.machine firstMachine (powerMachine C)
def budget (C : Nat) (bits : List Bool) :=
  RecoveryProjectionDimension.budget bits+1+PCPSerializerCapacity.Power.budget 4 C (value bits)

theorem parsed_power (bits : List Bool) (out : Fin 7→List Bool)
    (hr : out 5=List.replicate (value bits) true) (i : Fin (DimensionPolynomial.tapes 4)) :
    parsed bits out (powerSlots i)=DimensionPolynomial.input 4 (value bits) i := by
  classical
  by_cases hi : i.val=0
  · have he : i=⟨0,by decide⟩ := Fin.ext hi
    subst i
    change install nativeSlots _ _ (nativeSlots 5)=_
    rw [install_slot _ native_injective,hr]
    rfl
  · have hn : ∀ j,nativeSlots j≠powerSlots i := by
      intro j h; have hv:=congrArg Fin.val h; have hj:=j.isLt
      simp only [nativeSlots,powerSlots,hi,↓reduceDIte,Fin.val_castAdd] at hv
      omega
    rw [parsed,install_other _ _ _ _ hn]
    have hz : powerSlots i≠0 := by
      intro h; have hv:=congrArg Fin.val h
      simp only [powerSlots,hi,↓reduceDIte] at hv
      omega
    simp only [input,hz,ite_false,DimensionPolynomial.input,hi,ite_false]

theorem capacity_ready (C : Nat) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (machine C) (budget C bits) (input bits) out ∧
      out 3=VerifierDecoding.CompareMachine.word (value bits) ∧
      out 5=List.replicate (value bits) true ∧ out 17=List.replicate (C*(value bits+1)^4) true := by
  obtain ⟨dim,hparsed,hcount,hraw⟩ := RecoveryProjectionDimension.unary_ready bits
  have first := hparsed.focus nativeSlots native_injective (input bits)
    (by intro j; fin_cases j <;> rfl)
  obtain ⟨power,hpower,hsource,hcapacity⟩ := PCPSerializerCapacity.Power.capacity_run 4 C (value bits)
  have second := hpower.focus powerSlots power_injective (parsed bits dim) (parsed_power bits dim hraw)
  have hall := ClockJoin.join _ _ _ _ _ _ _ first second
  refine ⟨_,hall,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro i h; have hv:=congrArg Fin.val h
      simp only [powerSlots] at hv
      split at hv <;> dsimp at hv <;> omega)]
    change install nativeSlots _ _ (nativeSlots 3)=_
    rw [install_slot _ native_injective,hcount]
  · change install powerSlots _ _ (powerSlots ⟨0,by decide⟩)=_
    rw [install_slot _ power_injective]
    exact hsource
  · change install powerSlots _ _ (powerSlots (PCPSerializerCapacity.Power.outputSlot 4))=_
    rw [install_slot _ power_injective]
    exact hcapacity

end NearCubicWires.RepairSource.RecoveryProjectionCapacity
