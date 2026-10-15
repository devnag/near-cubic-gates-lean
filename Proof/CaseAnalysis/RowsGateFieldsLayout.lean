import Proof.CaseAnalysis.CloseoutRowsIntegerColdReady
import Proof.CaseAnalysis.RowsGateHeader
import Proof.CaseAnalysis.RowsBooleanVector

/-! The supported-gate decoder consumes its three retained header fields
directly. Each decoder has disjoint fresh work, and its source is an alias. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateFields
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots (i : Fin 148) : Fin 998:=i.castAdd 850
def weightsSlots (i : Fin 460) : Fin 998:=if i.val=221 then 38 else ⟨148+i.val,by omega⟩
def thresholdSlots (i : Fin 212) : Fin 998:=if i.val=0 then 78 else ⟨608+i.val,by omega⟩
def supportSlots (i : Fin 178) : Fin 998:=if i.val=0 then 118 else ⟨820+i.val,by omega⟩
theorem weights_val (i : Fin 460) : (weightsSlots i).val=if i.val=221 then 38 else 148+i.val:=by
  unfold weightsSlots
  split_ifs <;> rfl
theorem threshold_val (i : Fin 212) : (thresholdSlots i).val=if i.val=0 then 78 else 608+i.val:=by
  unfold thresholdSlots
  split_ifs <;> rfl
theorem support_val (i : Fin 178) : (supportSlots i).val=if i.val=0 then 118 else 820+i.val:=by
  unfold supportSlots
  split_ifs <;> rfl
theorem header_injective : Function.Injective headerSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 998=>k.val) h)
theorem weights_injective : Function.Injective weightsSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [weights_val,weights_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem threshold_injective : Function.Injective thresholdSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [threshold_val,threshold_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem support_injective : Function.Injective supportSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [support_val,support_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

def input (bits : List Bool) (i : Fin 998):=if i.val=1 then frame bits else []
def booted (bits : List Bool):=Function.update (input bits) 0 [false]
noncomputable def headerDone (bits : List Bool):=
  install headerSlots (booted bits) (CloseoutRowsGateHeader.output bits)
noncomputable def weightsDone (bits : List Bool) (out : Fin 460→List Bool):=
  install weightsSlots (headerDone bits) out
noncomputable def thresholdDone (bits : List Bool) (w : Fin 460→List Bool) (out : Fin 212→List Bool):=
  install thresholdSlots (weightsDone bits w) out

theorem header_input (bits : List Bool) (i : Fin 148) :
    booted bits (headerSlots i)=CompetitorWitnessHeader.input [] bits i:=by
  rw [CompetitorWitnessHeader.input_eq]
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    rfl
  · have hn:headerSlots i≠0:=by intro h;exact hi (congrArg Fin.val h)
    rw [booted,Function.update_of_ne hn,if_neg hi]
    rfl
theorem header_field (bits : List Bool) (i : Fin 3) :
    headerDone bits (headerSlots (CloseoutRowsGateHeader.port i))=frame (CloseoutRowsGateHeader.codeWord bits i):=by
  rw [headerDone,install_slot _ header_injective]
  exact (CloseoutRowsGateHeader.header_run bits).2.2 i
theorem header_fresh (bits : List Bool) (i : Fin 998) (hi : 148 ≤ i.val) : headerDone bits i=[]:=by
  rw [headerDone,install_other _ _ _ _ (by
    intro j h
    have hv:=congrArg Fin.val h
    change j.val=i.val at hv
    omega)]
  have hn:i≠0:=by intro h;have hv:=congrArg Fin.val h;omega
  simp only [booted,Function.update_of_ne hn,input,if_neg (show i.val≠1 by omega)]
theorem weights_header (bits : List Bool) (out : Fin 460→List Bool) (i : Fin 148) (hi : i.val≠38) :
    weightsDone bits out (headerSlots i)=headerDone bits (headerSlots i):=by
  apply install_other
  intro j h
  have hv:=congrArg Fin.val h
  rw [weights_val] at hv
  change (if j.val=221 then 38 else 148+j.val)=i.val at hv
  split_ifs at hv <;> omega
theorem weights_fresh (bits : List Bool) (out : Fin 460→List Bool) (i : Fin 998) (hi : 608 ≤ i.val) :
    weightsDone bits out i=[]:=by
  rw [weightsDone,install_other _ _ _ _ (by
    intro j h
    have hv:=congrArg Fin.val h
    rw [weights_val] at hv
    split_ifs at hv <;> omega)]
  exact header_fresh bits i (by omega)
theorem threshold_fresh (bits : List Bool) (w : Fin 460→List Bool) (out : Fin 212→List Bool)
    (i : Fin 998) (hi : 820 ≤ i.val) : thresholdDone bits w out i=[]:=by
  rw [thresholdDone,install_other _ _ _ _ (by
    intro j h
    have hv:=congrArg Fin.val h
    rw [threshold_val] at hv
    split_ifs at hv <;> omega)]
  exact weights_fresh bits w i (by omega)

theorem weights_input (bits : List Bool) (i : Fin 460) :
    headerDone bits (weightsSlots i)=CloseoutRowsIntegerCold.readyInput (CloseoutRowsGateHeader.codeWord bits 0) i:=by
  have raw (word : List Bool) (j : Fin 460) : CloseoutRowsIntegerCold.readyInput word j=
      if j.val=221 then frame word else []:=by
    refine Fin.addCases (m:=459) (n:=1) ?_ ?_ j
    · intro k
      simp only [CloseoutRowsIntegerCold.readyInput,Fin.addCases_left,CloseoutRowsIntegerCold.input,
        Fin.ext_iff,Fin.val_castAdd]
      rfl
    · intro k
      have hk:k=0:=Fin.eq_zero k
      subst k
      rfl
  rw [raw]
  by_cases hi:i.val=221
  · have he:i=221:=Fin.ext hi
    subst i
    exact header_field bits 0
  · rw [if_neg hi]
    apply header_fresh
    rw [weights_val,if_neg hi]
    omega

theorem threshold_input (bits : List Bool) (out : Fin 460→List Bool) (i : Fin 212) :
    weightsDone bits out (thresholdSlots i)=CloseoutRowsIntegerGuard.input (CloseoutRowsGateHeader.codeWord bits 1) i:=by
  rw [CloseoutRowsIntegerReady.guard_input]
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    exact (weights_header bits out 78 (by decide)).trans (header_field bits 1)
  · rw [if_neg hi]
    apply weights_fresh
    rw [threshold_val,if_neg hi]
    omega

theorem support_input (bits : List Bool) (w : Fin 460→List Bool) (out : Fin 212→List Bool) (i : Fin 178) :
    thresholdDone bits w out (supportSlots i)=NatCold.input (CloseoutRowsGateHeader.codeWord bits 2) i:=by
  have raw (word : List Bool) (j : Fin 178) : NatCold.input word j=if j.val=0 then frame word else []:=by
    refine Fin.addCases (m:=174) (n:=4) ?_ ?_ j
    · intro k
      simp only [NatCold.input,Fin.addCases_left,CanonicalTest.input,Fin.val_castAdd]
      rfl
    · intro k
      rw [NatCold.input,Fin.addCases_right]
      have hn:(k.natAdd 174).val≠0:=by simp only [Fin.val_natAdd];omega
      rw [if_neg hn]
  rw [raw]
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    change install thresholdSlots (weightsDone bits w) out 118=_
    rw [install_other _ _ _ _ (by
      intro j h
      have hv:=congrArg Fin.val h
      rw [threshold_val] at hv
      split_ifs at hv <;> omega)]
    exact (weights_header bits w 118 (by decide)).trans (header_field bits 2)
  · rw [if_neg hi]
    apply threshold_fresh
    rw [support_val,if_neg hi]
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsGateFields
