import Proof.CaseAnalysis.WitnessNodeBank

/-! One cold circuit traversal retains its exact node stream, literal count,
output payload and canonical flags. Each balanced re-encoding call is paid;
the node and output subwords are the original fixed-width projections. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DAGFields
open LocalBitMultitape RecoveryRootRound RadixSemantics
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots (i : Fin 138) : Fin 488:=i.castAdd 350
def listSlots (i : Fin 174) : Fin 488:=if i.val=0 then 38 else ⟨137+i.val,by omega⟩
def outputSlots (i : Fin 178) : Fin 488:=if i.val=0 then 78 else ⟨310+i.val,by omega⟩
theorem header_injective : Function.Injective headerSlots:=by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 488=>i.val) h)
theorem list_val (i : Fin 174) : (listSlots i).val=if i.val=0 then 38 else 137+i.val:=by
  unfold listSlots
  split_ifs <;> rfl
theorem output_val (i : Fin 178) : (outputSlots i).val=if i.val=0 then 78 else 310+i.val:=by
  unfold outputSlots
  split_ifs <;> rfl
theorem list_injective : Function.Injective listSlots:=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [list_val,list_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem output_injective : Function.Injective outputSlots:=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [output_val,output_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem list_outside (i : Fin 488) (h38 : i.val≠38) (hb : i.val<138 ∨ 311 ≤ i.val) :
    ∀ j,listSlots j≠i:=by
  intro j h
  have hv:=congrArg Fin.val h
  rw [list_val] at hv
  split_ifs at hv <;> rcases hb with hb|hb <;> omega
theorem output_outside (i : Fin 488) (h78 : i.val≠78) (hb : i.val<311) :
    ∀ j,outputSlots j≠i:=by
  intro j h
  have hv:=congrArg Fin.val h
  rw [output_val] at hv
  split_ifs at hv <;> omega

def input (x bits : List Bool) : Fin 488→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (138+350)=>List Bool)
    (PCPPNativeCanonicalGuard.input x bits) (fun _=>[])
noncomputable def header:=RecoveryFocus.machine headerSlots PCPPNativeCanonicalGuard.machine
noncomputable def list:=RecoveryFocus.machine listSlots CanonicalTest.machine
noncomputable def output:=RecoveryFocus.machine outputSlots NatCold.machine
noncomputable def first:=Composition.machine header list
noncomputable def machine:=Composition.machine first output
def budget (bits : List Bool):=34000000000000000000*(bits.length+1)^24

theorem header_fresh (x bits : List Bool) (out : Fin 138→List Bool) (i : Fin 488) (hi : 138 ≤ i.val) :
    install headerSlots (input x bits) out i=[]:=by
  rw [install_other _ _ _ _ (by
    intro j h
    have hv:=congrArg Fin.val h
    simp only [headerSlots,Fin.val_castAdd] at hv
    omega)]
  simp [input,Fin.addCases,show ¬i.val<138 by omega]

theorem list_input (x bits : List Bool) (out : Fin 138→List Bool)
    (hn : out 38=frame (PCPPNativeCanonical.nodeWord bits)) :
    ∀ i,install headerSlots (input x bits) out (listSlots i)=
      CanonicalTest.input (PCPPNativeCanonical.nodeWord bits) i:=by
  intro i
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    change install headerSlots _ out (headerSlots 38)=_
    rw [install_slot _ header_injective]
    exact hn
  · rw [header_fresh _ _ _ _ (by rw [list_val,if_neg hi];omega)]
    simp [CanonicalTest.input,hi]

theorem natural_input (bits : List Bool) (i : Fin 178) :
    NatCold.input bits i=if i.val=0 then frame bits else []:=by
  refine Fin.addCases (m:=174) (n:=4) ?_ ?_ i
  · intro j
    simp only [NatCold.input,Fin.addCases_left,CanonicalTest.input,Fin.val_castAdd]
    rfl
  · intro j
    simp [NatCold.input]

theorem output_input (x bits : List Bool) (hout : Fin 138→List Bool) (lout : Fin 174→List Bool)
    (hn : hout 78=frame (PCPPNativeCanonical.outputWord bits)) :
    ∀ i,install listSlots (install headerSlots (input x bits) hout) lout (outputSlots i)=
      NatCold.input (PCPPNativeCanonical.outputWord bits) i:=by
  intro i
  rw [natural_input]
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    change install listSlots _ lout 78=frame (PCPPNativeCanonical.outputWord bits)
    rw [install_other _ _ _ _ (list_outside 78 (by decide) (Or.inl (by decide)))]
    change install headerSlots _ hout (headerSlots 78)=_
    rw [install_slot _ header_injective]
    exact hn
  · have hv:(outputSlots i).val=310+i.val:=by rw [output_val,if_neg hi]
    rw [if_neg hi,install_other _ _ _ _ (list_outside _ (by omega) (Or.inr (by omega))),
      header_fresh _ _ _ _ (by omega)]

theorem output_word_length (bits : List Bool) :
    (PCPPNativeCanonical.outputWord bits).length=bits.length:=
  (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits 3)

theorem time_bound (bits : List Bool) :
    PCPPNativeCanonicalGuard.budget bits+1+CanonicalTest.budget (PCPPNativeCanonical.nodeWord bits)+1+
      NatCold.budget (PCPPNativeCanonical.outputWord bits)≤budget bits:=by
  have hp:(bits.length+1)^2≤(bits.length+1)^24:=Nat.pow_le_pow_right (by omega) (by decide)
  have hpos:1≤(bits.length+1)^24:=Nat.one_le_pow _ _ (by omega)
  unfold PCPPNativeCanonicalGuard.budget CanonicalTest.budget Reencode.polynomialBudget NatCold.budget budget
  rw [DAGBounds.node_word_length,output_word_length]
  omega

theorem fields_run (x bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget bits) (input x bits) out ∧
      out 167=FieldList.stream (DAGChecks.words bits) ∧
      out 178=RepairSource.VerifierDecoding.CompareMachine.word (DAGChecks.words bits).length ∧
      out 484=frame (BitFields.payload (PCPPNativeCanonical.outputWord bits)) ∧
      out 351=RepairSource.VerifierDecoding.CompareMachine.word (BitFields.payload (PCPPNativeCanonical.outputWord bits)).length ∧
      (readTapeBit (out 137) 0=true ↔ PCPPNativeCanonical.headerValid bits) ∧
      (readTapeBit (out 309) 0=true ↔ ∃ values,CanonicalBinary.encodeBalancedList values=value (PCPPNativeCanonical.nodeWord bits)) ∧
      (readTapeBit (out 485) 0=true ↔ (CanonicalBinary.decodeNat (value (PCPPNativeCanonical.outputWord bits))).isSome):=by
  obtain ⟨h,hh,ht,heads,hflag,hn,hi⟩:=PCPPNativeCanonicalGuard.header_run x bits
  have hready:ClockJoin.ReadyRun PCPPNativeCanonicalGuard.machine (PCPPNativeCanonicalGuard.budget bits)
      (PCPPNativeCanonicalGuard.input x bits) h.final.tapes:=⟨h,hh,rfl,heads,ht⟩
  have h0:=hready.focus headerSlots header_injective (input x bits)
    (by intro i;simp only [input,headerSlots,Fin.addCases_left])
  obtain ⟨l,hl,ls,lc,lf⟩:=CanonicalTest.fields_run (PCPPNativeCanonical.nodeWord bits)
  have h1:=hl.focus listSlots list_injective (install headerSlots (input x bits) h.final.tapes)
    (list_input x bits _ hn)
  have hp:=ClockJoin.join header list _ _ _ _ _ h0 h1
  obtain ⟨n,hnat,np,nc,nf,_⟩:=NatCold.nat_run (PCPPNativeCanonical.outputWord bits)
  have h2:=hnat.focus outputSlots output_injective
    (install listSlots (install headerSlots (input x bits) h.final.tapes) l) (output_input x bits _ l hi)
  have whole:=ClockJoin.join first output _ _ _ _ _ hp h2
  refine ⟨_,ClockJoin.enlarge machine _ (budget bits) _ _ whole (time_bound bits),?_,?_,?_,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (output_outside _ (by decide) (by decide))]
    change install listSlots _ l (listSlots 30)=_
    rw [install_slot _ list_injective,ls]
    exact (Reencode.fields_stream _).symm
  · rw [install_other _ _ _ _ (output_outside _ (by decide) (by decide))]
    change install listSlots _ l (listSlots 41)=_
    rw [install_slot _ list_injective,lc]
    simp only [DAGChecks.words,Reencode.fields,List.length_map]
  · change install outputSlots _ n (outputSlots 174)=_
    rw [install_slot _ output_injective,np]
  · change install outputSlots _ n (outputSlots 41)=_
    rw [install_slot _ output_injective,nc]
  · rw [install_other _ _ _ _ (output_outside _ (by decide) (by decide)),
      install_other _ _ _ _ (list_outside _ (by decide) (Or.inl (by decide)))]
    change readTapeBit (install headerSlots _ _ (headerSlots 137)) 0=true ↔_
    rw [install_slot _ header_injective]
    exact hflag
  · rw [install_other _ _ _ _ (output_outside _ (by decide) (by decide))]
    change readTapeBit (install listSlots _ _ (listSlots 172)) 0=true ↔_
    rw [install_slot _ list_injective]
    exact lf
  · change readTapeBit (install outputSlots _ _ (outputSlots 175)) 0=true ↔_
    rw [install_slot _ output_injective]
    exact nf

end NearCubicWires.RepairOrdinary.CloseoutWitness.DAGFields
