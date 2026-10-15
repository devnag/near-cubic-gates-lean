import Proof.Amplification.RecoveryProjectionCapacity

/-! Execute the two supplied scalar fields directly. The R parser produces
both physical row-width and capacity drivers; the Q parser produces the
outer query driver. Every source query byte is retained. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionScalar
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rSlots (i : Fin 28) : Fin 69 :=
  if i.val=3 then 34 else if i.val=17 then 32 else ⟨i.val+36,by have hi:=i.isLt; omega⟩
def qSlots (i : Fin 5) : Fin 69 :=
  if i.val=3 then 35 else ⟨i.val+64,by have hi:=i.isLt; omega⟩
theorem r_injective : Function.Injective rSlots := by
  intro a b h; apply Fin.ext
  have hv:=congrArg Fin.val h
  dsimp only [rSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
theorem q_injective : Function.Injective qSlots := by
  intro a b h; apply Fin.ext
  have hv:=congrArg Fin.val h
  dsimp only [qSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (rBits qBits source : List Bool) (i : Fin 69) :=
  if i.val=28 then source else if i.val=36 then RepairOrdinary.frame rBits
  else if i.val=64 then RepairOrdinary.frame qBits else []
noncomputable def middle (rBits qBits source : List Bool) (rData : Fin 28→List Bool) :=
  install rSlots (input rBits qBits source) rData
noncomputable def rMachine (C : Nat) := RecoveryFocus.machine rSlots (RecoveryProjectionCapacity.machine C)
noncomputable def qMachine := RecoveryFocus.machine qSlots RecoveryProjectionDimension.parsedMachine
noncomputable def machine (C : Nat) := Composition.machine (rMachine C) qMachine
def budget (C : Nat) (rBits qBits : List Bool) :=
  RecoveryProjectionCapacity.budget C rBits+1+ProjectionNormalization.Unary.budget qBits+2

theorem r_input (rBits qBits source : List Bool) (i : Fin 28) :
    input rBits qBits source (rSlots i)=RecoveryProjectionCapacity.input rBits i := by
  by_cases h3 : i.val=3
  · have he : i=3 := Fin.ext h3
    subst i; rfl
  by_cases h17 : i.val=17
  · have he : i=17 := Fin.ext h17
    subst i; rfl
  have hi:=i.isLt
  simp only [rSlots,h3,h17,ite_false,input,RecoveryProjectionCapacity.input]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem disjoint (i : Fin 28) (j : Fin 5) : rSlots i≠qSlots j := by
  intro h; have hv:=congrArg Fin.val h; have hi:=i.isLt; have hj:=j.isLt
  dsimp only [rSlots,qSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem q_input (rBits qBits source : List Bool) (rData : Fin 28→List Bool) (i : Fin 5) :
    middle rBits qBits source rData (qSlots i)=ProjectionNormalization.Unary.input qBits i := by
  rw [middle,install_other _ _ _ _ (fun j=>disjoint j i)]
  fin_cases i <;> rfl

theorem dimensions_ready (C : Nat) (rBits qBits source : List Bool) : ∃ out,
    ClockJoin.ReadyRun (machine C) (budget C rBits qBits) (input rBits qBits source) out ∧
      out 28=source ∧ out 32=List.replicate (C*(value rBits+1)^4) true ∧
      out 34=VerifierDecoding.CompareMachine.word (value rBits) ∧
      out 35=VerifierDecoding.CompareMachine.word (value qBits) ∧
      (∀ i : Fin 32,i.val ≠ 28 → out (i.castAdd 37)=[]) ∧ out 33=[] := by
  obtain ⟨rData,hrData,hR,_hRaw,hCap⟩ := RecoveryProjectionCapacity.capacity_ready C rBits
  have first := hrData.focus rSlots r_injective (input rBits qBits source) (r_input rBits qBits source)
  obtain ⟨qData,hqData,hQ⟩ := RecoveryProjectionDimension.parsed_ready qBits
  have second := hqData.focus qSlots q_injective (middle rBits qBits source rData)
    (q_input rBits qBits source rData)
  have hall := ClockJoin.join _ _ _ _ _ _ _ first second
  have htime : RecoveryProjectionCapacity.budget C rBits+1+(ProjectionNormalization.Unary.budget qBits+2)=
      budget C rBits qBits := by unfold budget; omega
  rw [htime] at hall
  refine ⟨_,hall,?_,?_,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
    rw [middle,install_other _ _ _ _ (by
      intro j h; have hv:=congrArg Fin.val h
      dsimp only [rSlots] at hv
      split_ifs at hv <;> dsimp at hv <;> omega)]
    rfl
  · rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
    change install rSlots _ _ (rSlots 17)=_
    rw [install_slot _ r_injective]
    exact hCap
  · rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
    change install rSlots _ _ (rSlots 3)=_
    rw [install_slot _ r_injective]
    exact hR
  · change install qSlots _ _ (qSlots 3)=_
    rw [install_slot _ q_injective]
    exact hQ
  · intro i hi
    rw [install_other _ _ _ _ (by
      intro j h; have hv:=congrArg Fin.val h; have hj:=j.isLt; have ht:=i.isLt
      dsimp only [qSlots,Fin.val_castAdd] at hv
      split_ifs at hv <;> dsimp at hv <;> omega)]
    rw [middle,install_other _ _ _ _ (by
      intro j h; have hv:=congrArg Fin.val h; have hj:=j.isLt; have ht:=i.isLt
      dsimp only [rSlots,Fin.val_castAdd] at hv
      split_ifs at hv <;> dsimp at hv <;> omega)]
    have ht:=i.isLt
    simp only [input,Fin.val_castAdd,hi,ite_false]
    split_ifs <;> first | rfl | omega
  · rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
    rw [middle,install_other _ _ _ _ (by
      intro j h; have hv:=congrArg Fin.val h
      dsimp only [rSlots] at hv
      split_ifs at hv <;> dsimp at hv <;> omega)]
    rfl

end NearCubicWires.RepairSource.RecoveryProjectionScalar
