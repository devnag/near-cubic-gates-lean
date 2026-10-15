import Proof.CaseAnalysis.WitnessTermMultiply

/-! Actual q0 and actual source clause bits produce the complete family
term cap. The source count is paid once; constant coefficient mass remains
a separate guard and is not multiplied by this term count. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermPolicy
open LocalBitMultitape RecoveryRootRound RepairSource CloseoutWitnessPolicy RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def ceilSlots (i : Fin 16) : Fin 44:=i.castAdd 28
def multiplySlots (i : Fin 27) : Fin 44:=
  ⟨if i.val=0 then 16 else if i.val=17 then 14 else 17+i.val,by split_ifs <;> omega⟩
def first (delta : ℚ) (copies : ℕ):=RecoveryFocus.machine ceilSlots
  (TermCeil.machine (termNumerator delta copies) (termDenominator delta copies))
def second:=RecoveryFocus.machine multiplySlots TermMultiply.machine
def machine (delta : ℚ) (copies : ℕ):=Composition.machine (first delta copies) second
def input (q0 cb : ℕ) (i : Fin 44):=
  if i.val=0 then List.replicate q0 true else if i.val=16 then List.replicate cb true else []
def budget (delta : ℚ) (copies q0 cb : ℕ):=
  TermCeil.budget (termNumerator delta copies) (termDenominator delta copies) q0+1+
    TermMultiply.budget cb (xorTermBound delta q0 copies)

theorem ceil_injective : Function.Injective ceilSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 44=>k.val) h)
theorem multiply_injective : Function.Injective multiplySlots:=by
  intro i j h
  have hv:=congrArg (fun k : Fin 44=>k.val) h
  dsimp only [multiplySlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem policy_run (delta : ℚ) (copies q0 cb : ℕ) : ∃ output,
    ClockJoin.ReadyRun (machine delta copies) (budget delta copies q0 cb) (input q0 cb) output ∧
      output 0=List.replicate q0 true ∧ output 14=List.replicate (xorTermBound delta q0 copies) true ∧
      output 42=List.replicate ((2*2^cb)*xorTermBound delta q0 copies) true:=by
  obtain ⟨c,hc,c0,_,cv⟩:=TermCeil.policy_run delta copies q0
  have hcf:=hc.focus ceilSlots ceil_injective (input q0 cb) (by
    intro i
    have hi:=i.isLt
    simp only [input,ceilSlots,Fin.val_castAdd,TermCeil.input,Fin.ext_iff,Fin.val_zero]
    split_ifs <;> first | rfl | omega)
  let bank:=install ceilSlots (input q0 cb) c
  have old (i : Fin 16) : bank (ceilSlots i)=c i:=install_slot _ ceil_injective _ _ _
  have fresh (i : Fin 44) (hi : 16 ≤ i.val) : bank i=input q0 cb i:=by
    apply install_other
    intro j h
    have hv:=congrArg (fun k : Fin 44=>k.val) h
    change j.val=i.val at hv
    omega
  obtain ⟨m,hm,mj,_,mv⟩:=TermMultiply.multiply_run cb (xorTermBound delta q0 copies)
  have hmf:=hm.focus multiplySlots multiply_injective bank (by
    intro i
    by_cases h0:i.val=0
    · have he:i=0:=Fin.ext h0
      rw [he];exact fresh 16 (by decide)
    by_cases h17:i.val=17
    · have he:i=17:=Fin.ext h17
      rw [he];exact (old 14).trans cv
    rw [TermMultiply.input,if_neg h0,if_neg h17]
    rw [fresh _ (by simp only [multiplySlots,if_neg h0,if_neg h17];omega)]
    simp only [input,multiplySlots,if_neg h0,if_neg h17,
      if_neg (show 17+i.val≠0 by omega),if_neg (show 17+i.val≠16 by omega)])
  refine ⟨_,ClockJoin.join (first delta copies) second _ _ _ _ _ hcf hmf,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro i h
      have hv:=congrArg (fun k : Fin 44=>k.val) h
      dsimp only [multiplySlots,Fin.val_zero] at hv
      split_ifs at hv;omega)]
    exact (old 0).trans c0
  · change install multiplySlots _ _ (multiplySlots 17)=_
    rw [install_slot _ multiply_injective];exact mj
  · change install multiplySlots _ _ (multiplySlots 25)=_
    rw [install_slot _ multiply_injective];exact mv

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermPolicy
