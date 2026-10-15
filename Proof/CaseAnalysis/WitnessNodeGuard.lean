import Proof.CaseAnalysis.WitnessNodeGuardDecision

/-! One raw node code now executes through the cold canonical field reader,
binary type/topology guards, and the exact canonical decoder decision. The
native words are physically retained, ready for the descriptor append calls. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeGuard
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w : ℕ) (left right bits : List Bool):=base (NodeFields.input bits) w left right
noncomputable def fieldMachine:=RecoveryFocus.machine fieldSlots NodeFields.machine
noncomputable def scalarPrefix:=Composition.machine fieldMachine scalarMachine
noncomputable def kindPrefix:=Composition.machine scalarPrefix kindMachine
noncomputable def machine:=Composition.machine kindPrefix finish
def budget (w : ℕ) (bits : List Bool):=NodeFields.budget bits+36*w+80*bits.length+320

theorem install_fields (old fresh : Fin 668 → List Bool) (w : ℕ) (left right : List Bool) :
    install fieldSlots (base old w left right) fresh=base fresh w left right:=by
  funext i
  refine Fin.addCases (m:=668) (n:=78) ?_ ?_ i
  · intro j
    change install fieldSlots _ fresh (fieldSlots j)=_
    rw [install_slot _ field_injective]
    exact (base_field fresh w left right j).symm
  · intro j
    rw [install_other _ _ _ _ (by
      intro k h
      have hv:=congrArg Fin.val h
      change k.val=668+j.val at hv
      omega)]
    simp only [base,Fin.addCases_right]

theorem payload_bound (bits : List Bool) (j : Fin 3) :
    (BitFields.payload (NodeMeaning.codeWord bits j)).length ≤ bits.length+1:=by
  have h:=Reencode.count_bound (NodeMeaning.codeWord bits j)
  simpa only [BitFields.payload,Reencode.fields,List.length_map,TraversalCounted.count,NodeFields.codeWord_length] using h

theorem before_native (fields : Fin 668 → List Bool) (w : ℕ) (left right bits : List Bool)
    (out : Fin 3 → Fin 21 → List Bool) (j : Fin 3) :
    beforeDecision fields w left right bits out (fieldSlots (NodeFields.slots j 180))=
      fields (NodeFields.slots j 180):=by
  exact before_retained _ _ _ _ _ _ _ (by fin_cases j <;> decide) (by fin_cases j <;> decide)

theorem finished_native (fields : Fin 668 → List Bool) (w : ℕ) (left right bits : List Bool)
    (out : Fin 3 → Fin 21 → List Bool) (j : Fin 3) :
    finished (beforeDecision fields w left right bits out) (fieldSlots (NodeFields.slots j 180))=
      fields (NodeFields.slots j 180):=by
  rw [finished,Function.update_of_ne (by fin_cases j <;> decide),before_native]

theorem node_run (w : ℕ) (left right bits : List Bool)
    (hl : left.length=w) (hr : right.length=w) (hw : bits.length+1 ≤ w) : ∃ output,
    ClockJoin.ReadyRun machine (budget w bits) (input w left right bits) output ∧
      (readTapeBit (output 745) 0=true ↔ NodeMeaning.valid (value left) (value right) bits) ∧
      (∀ j,output (fieldSlots (NodeFields.slots j 180))=
        NativeWord.word (BitFields.payload (NodeMeaning.codeWord bits j))) ∧
      (∀ j n,CanonicalBinary.decodeNat (value (NodeMeaning.codeWord bits j))=some n →
        output (fieldSlots (NodeFields.slots j 180))=RepairRepresentation.natWord n) ∧
      (∀ i,output (common i)=shared w left right i):=by
  obtain ⟨fields,hfields,hword,hn,hdecode,hheaders,hpayload⟩:=NodeFields.fields_run_full bits
  have hfield:=bounded_focus fieldSlots field_injective _ _ _ hfields (input w left right bits)
    (base_field (NodeFields.input bits) w left right)
  rw [input,install_fields] at hfield
  obtain ⟨out,hs,hshared,_,hfit,hsmall,hleft,hright⟩:=scalar_run fields w left right
    (fun j=>BitFields.payload (NodeMeaning.codeWord bits j)) hpayload hl hr
    (fun j=>(payload_bound bits j).trans hw)
  have hsall:=ClockJoin.join fieldMachine scalarMachine _ _ _ _ _ hfield hs
  obtain ⟨kr,hk,kt,kh,ks⟩:=kind_run (scalarStage (base fields w left right) out 3) bits
    (kind_initial_input fields w left right bits out (fields_kind_values bits fields hheaders))
  have hkready : ClockJoin.ReadyRun kindMachine (80*bits.length+140)
      (scalarStage (base fields w left right) out 3) (beforeDecision fields w left right bits out):=
    ⟨kr,hk,kt,kh,ks.le⟩
  have hkall:=ClockJoin.join scalarPrefix kindMachine _ _ _ _ _ hsall hkready
  have hf:=finish_run (beforeDecision fields w left right bits out) (before_blank _ _ _ _ _ _)
  have h:=ClockJoin.join kindPrefix finish _ _ _ _ _ hkall hf
  have ht:((NodeFields.budget bits+1+(36*w+176))+1+(80*bits.length+140))+1+1=budget w bits:=by
    unfold budget;omega
  rw [ht] at h
  refine ⟨_,h,?_,?_,?_,?_⟩
  · rw [finished,Function.update_self]
    exact decision_exact fields w left right bits out hn hfit hsmall hleft hright
  · intro j
    rw [finished_native,hword]
  · intro j n hd
    rw [finished_native]
    exact hdecode j n hd
  · intro i
    rw [finished,Function.update_of_ne (by fin_cases i <;> decide),beforeDecision,
      kind_stage_other _ _ _ _ (by fin_cases i <;> decide)]
    exact scalar_stage_common _ _ _ (base_common fields w left right) hshared 3 i

theorem typed_output (left right bits : List Bool) (output : Fin 746 → List Bool)
    (hflag : readTapeBit (output 745) 0=true ↔ NodeMeaning.valid (value left) (value right) bits)
    (hnative : ∀ j n,CanonicalBinary.decodeNat (value (NodeMeaning.codeWord bits j))=some n →
      output (fieldSlots (NodeFields.slots j 180))=RepairRepresentation.natWord n)
    (hp : readTapeBit (output 745) 0=true) :
    ∃ node : BooleanNode (value left),node.WellFormedAt (value right) ∧
      CanonicalWitnessCodec.decodeBooleanNode (value left) (value bits)=some node ∧
      PCPPRequestNodeSchema.native node=
        (List.ofFn (fun j=>output (fieldSlots (NodeFields.slots j 180)))).flatten:=by
  have hv:=hflag.mp hp
  obtain ⟨node,hw,hcode,hn⟩:=NodeMeaning.node_of_valid (value left) (value right) bits hv
  refine ⟨node,hw,?_,?_⟩
  · rw [←hcode,CanonicalWitnessCodec.decodeBooleanNode_encode]
  · rw [hn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    exact (hnative j _ (BitFields.decode_of_passes _ (hv.1 j))).symm

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeGuard
