import Proof.Amplification.RecoveryPrefixMeasureWhole
import Proof.Amplification.RecoveryPrefixInitialize
import Proof.PCP.PCPSerializerCapacityPower

/-! Whole physical preparation from the two serialized search fields. The
measured mass drives the accepted fixed polynomial producer directly into
native capacity tape3; no capacity copy is needed. The actual sentinel total
is retained on tape360 for the bounded oracle repeater. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixColdPrepare
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryPrefixMeasure RecoveryPrefixBody RecoveryPrefix
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def measureSlots : Fin 4→Fin 380 := ![0,361,360,362]
def powerSlots (i : Fin (DimensionPolynomial.tapes 2)) : Fin 380 :=
  ⟨if i.val=0 then 361 else if i.val=7 then 3 else i.val+362,
    by have hi:=i.isLt; dsimp [DimensionPolynomial.tapes] at hi; split_ifs <;> omega⟩
def nativeSlots (i : Fin 360) : Fin 380 := ⟨i.val,by have h:=i.isLt; omega⟩
theorem measure_injective : Function.Injective measureSlots := by decide
theorem power_injective : Function.Injective powerSlots := by
  intro a b h
  apply Fin.ext
  have hv := congrArg (fun i : Fin 380=>i.val) h
  dsimp only [powerSlots] at hv
  split_ifs at hv <;> have ha:=a.isLt <;> have hb:=b.isLt <;>
    dsimp [DimensionPolynomial.tapes] at ha hb <;> omega
theorem native_injective : Function.Injective nativeSlots := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 380=>i.val) h)

def cold (payload total : Nat) : Fin 380→List Bool :=
  fun i=>if i.val=0 then request payload total else []
noncomputable def measured (payload total : Nat) := install measureSlots (cold payload total)
  ![request payload total,List.replicate (mass payload total) true,
    VerifierDecoding.CompareMachine.word total,List.replicate (rawBudget payload total) false]
noncomputable def measureMachine := RecoveryFocus.machine measureSlots RecoveryPrefixMeasure.machine
noncomputable def powerMachine (C : Nat) := RecoveryFocus.machine powerSlots (PCPSerializerCapacity.Power.machine 2 C)
noncomputable def initializeMachine := RecoveryFocus.machine nativeSlots RecoveryPrefixInitialize.machine
noncomputable def machine (C : Nat) := Composition.machine (Composition.machine measureMachine (powerMachine C)) initializeMachine

def capacity (C payload total : Nat) := C*(mass payload total+1)^2

def budget (C payload total : Nat) := RecoveryPrefixMeasure.budget payload total+1+
  PCPSerializerCapacity.Power.budget 2 C (mass payload total)+1+
  (2*capacity C payload total+26)

theorem measure_ready (payload total : Nat) :
    ClockJoin.ReadyRun measureMachine (RecoveryPrefixMeasure.budget payload total)
      (cold payload total) (measured payload total) :=
  (RecoveryPrefixMeasure.measure_ready payload total).focus measureSlots measure_injective
    (cold payload total) (by intro i; fin_cases i <;> rfl)

theorem measured_power (payload total : Nat) (i : Fin (DimensionPolynomial.tapes 2)) :
    measured payload total (powerSlots i)=DimensionPolynomial.input 2 (mass payload total) i := by
  classical
  by_cases hi : i.val=0
  · have he : i=⟨0,by decide⟩ := Fin.ext hi
    subst i
    change install measureSlots _ _ (measureSlots 1)=_
    rw [install_slot _ measure_injective]
    rfl
  · rw [measured,install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg (fun k : Fin 380=>k.val) he
      fin_cases j <;> dsimp [measureSlots,powerSlots] at hv <;> split_ifs at hv <;> omega)]
    simp only [DimensionPolynomial.input,hi,↓reduceIte,cold]
    have hz : (powerSlots i).val≠0 := by
      change (if i.val=0 then 361 else if i.val=7 then 3 else i.val+362)≠0
      split_ifs <;> omega
    rw [if_neg hz]

theorem measured_native (payload total : Nat) (i : Fin 360) :
    measured payload total (nativeSlots i)=if i.val=0 then request payload total else [] := by
  classical
  by_cases hi : i.val=0
  · have he : i=0 := Fin.ext hi
    subst i
    change install measureSlots _ _ (measureSlots 0)=_
    rw [install_slot _ measure_injective]
    rfl
  · rw [measured,install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg (fun k : Fin 380=>k.val) he
      have hlt:=i.isLt
      fin_cases j <;> dsimp [measureSlots,nativeSlots] at hv <;> omega)]
    simp [cold,nativeSlots,hi]

theorem powered_native (C payload total : Nat) (powerOut : Fin (DimensionPolynomial.tapes 2)→List Bool)
    (hv : powerOut (PCPSerializerCapacity.Power.outputSlot 2)=
      List.replicate (capacity C payload total) true) :
    (install powerSlots (measured payload total) powerOut) ∘ nativeSlots=
      RecoveryPrefixInitialize.cold (capacity C payload total) payload (frame (List.replicate total true)) := by
  classical
  funext i
  by_cases hi : i.val=3
  · have he : i=3 := Fin.ext hi
    subst i
    change install powerSlots _ _ (powerSlots (PCPSerializerCapacity.Power.outputSlot 2))=_
    rw [install_slot _ power_injective,hv]
    rfl
  · rw [Function.comp_apply,install_other _ _ _ _ (by
      intro j he
      have hj:=j.isLt
      have hn:=i.isLt
      have hx:=congrArg (fun k : Fin 380=>k.val) he
      dsimp [powerSlots,nativeSlots] at hx
      split_ifs at hx <;> omega),measured_native]
    simp [RecoveryPrefixInitialize.cold,hi,request]

theorem powered_driver (payload total : Nat) (powerOut : Fin (DimensionPolynomial.tapes 2)→List Bool) :
    install powerSlots (measured payload total) powerOut 360=VerifierDecoding.CompareMachine.word total := by
  classical
  rw [install_other _ _ _ _ (by
    intro i he
    have hv:=congrArg (fun k : Fin 380=>k.val) he
    dsimp [powerSlots] at hv
    split_ifs at hv <;> omega)]
  change install measureSlots _ _ (measureSlots 2)=_
  rw [install_slot _ measure_injective]
  rfl

theorem prepare (C payload total : Nat) (hc : 5≤capacity C payload total) : ∃ out : Fin 380→List Bool,
    ClockJoin.ReadyRun (machine C) (budget C payload total) (cold payload total) out ∧
    Inv (capacity C payload total) payload (capacity C payload total+1) [] false
      (frame (List.replicate total true)) (out ∘ nativeSlots) ∧
    out 360=VerifierDecoding.CompareMachine.word total := by
  classical
  obtain ⟨powerOut,hpower,_,hvalue⟩ := PCPSerializerCapacity.Power.capacity_run 2 C (mass payload total)
  have hp := hpower.focus powerSlots power_injective (measured payload total) (measured_power payload total)
  let afterPower := install powerSlots (measured payload total) powerOut
  have hn := powered_native C payload total powerOut hvalue
  have hi := (RecoveryPrefixInitialize.initialize_ready (capacity C payload total) payload
    (frame (List.replicate total true)) hc).focus nativeSlots native_injective afterPower
    (fun i=>congrFun hn i)
  have whole := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (measure_ready payload total) hp) hi
  refine ⟨_,whole,?_,?_⟩
  · have he : (install nativeSlots afterPower
        (RecoveryPrefixInitialize.output (capacity C payload total) payload (frame (List.replicate total true)))) ∘ nativeSlots=
        RecoveryPrefixInitialize.output (capacity C payload total) payload (frame (List.replicate total true)) := by
      funext i
      exact install_slot nativeSlots native_injective _ _ i
    rw [he]
    exact RecoveryPrefixInitialize.output_inv _ _ _ hc
  · rw [install_other _ _ _ _ (by
      intro i he
      have hv:=congrArg (fun k : Fin 380=>k.val) he
      change i.val=360 at hv
      have hlt:=i.isLt
      omega)]
    exact powered_driver payload total powerOut

end NearCubicWires.RepairSource.RecoveryPrefixColdPrepare
