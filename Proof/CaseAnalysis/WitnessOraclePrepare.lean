import Proof.CaseAnalysis.WitnessOracleLayout

/-! Cold input-length allocation and canonical oracle traversal share their
produced driver and fields directly. The only initialized validity bit is
written by a paid finite transition. All later decoder scratch is blank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

local instance : NeZero (InputPower.tapes 24):=⟨by decide⟩

theorem power_outside (i : Fin tapes) (h0 : i.val≠0) (hi : i.val<4 ∨ 66 ≤ i.val) :
    ∀ j,powerSlots j≠i:=by
  intro j h
  have hv:=congrArg Fin.val h
  rw [power_val] at hv
  have hj:j.val<63:=j.isLt
  split_ifs at hv <;> rcases hi with hi|hi <;> omega

theorem field_outside (i : Fin tapes) (h0 : i.val≠0) (h1 : i.val≠1)
    (hi : i.val<66 ∨ 552 ≤ i.val) : ∀ j,fieldSlots j≠i:=by
  intro j h
  have hv:=congrArg Fin.val h
  rw [field_val] at hv
  split_ifs at hv <;> rcases hi with hi|hi <;> omega

theorem power_input (x bits arityBits : List Bool) :
    ∀ i,input x bits arityBits (powerSlots i)=InputPower.input 24 x i:=by
  intro i
  rw [power_input_shape]
  by_cases hi:i.val=0
  · simp [powerSlots,input,hi]
  · have hv:(powerSlots i).val=3+i.val:=by rw [power_val,if_neg hi]
    simp only [if_neg hi,input,hv]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]

theorem field_input (x bits arityBits : List Bool) (out : Fin (InputPower.tapes 24)→List Bool)
    (h0 : out 0=frame x) : ∀ i,
    install powerSlots (input x bits arityBits) out (fieldSlots i)=DAGFields.input x bits i:=by
  intro i
  rw [field_input_shape]
  by_cases hzero:i.val=0
  · have he:i=0:=Fin.ext hzero
    subst i
    change install powerSlots _ out (powerSlots 0)=_
    rw [install_slot _ power_injective]
    exact h0
  by_cases hone:i.val=1
  · have he:i=1:=Fin.ext hone
    subst i
    change install powerSlots _ out 1=frame bits
    rw [install_other _ _ _ _ (power_outside 1 (by decide) (Or.inl (by decide)))]
    rfl
  · have hv:(fieldSlots i).val=64+i.val:=by rw [field_val,if_neg hzero,if_neg hone]
    rw [install_other _ _ _ _ (power_outside _ (by omega) (Or.inr (by omega))),
      if_neg hzero,if_neg hone]
    simp only [input,hv]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]

def prime : Machine tapes 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun _ _=>some ⟨1,fun i=>if i=1306 then some true else none,fun _=>.stay⟩

theorem prime_run (ts : Fin tapes→List Bool) (hf : ts 1306=[]) :
    ClockJoin.ReadyRun prime 1 ts (Function.update ts 1306 [true]):=by
  have hs:step prime (initialConfiguration prime ts)=
      some (⟨1,fun _=>0,Function.update ts 1306 [true]⟩ : Configuration tapes 2):=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=1306
      · subst i
        simp [applyAction,prime,initialConfiguration,hf,writeTapeBit]
      · simp [applyAction,prime,initialConfiguration,hi]
  obtain ⟨r,hr,hout,ht⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hout],by intro i;rw [hout],ht.le⟩

noncomputable def prepareFirst:=Composition.machine power fields
noncomputable def prepare:=Composition.machine prepareFirst prime
def prepareBudget (x bits : List Bool):=InputPower.budget 24 coefficient 1 x+1+DAGFields.budget bits+1+1

structure Prepared (x bits arityBits : List Bool) (out : Fin tapes→List Bool) : Prop where
  capacity : out 63=List.replicate (NodeReady.capacity (x.length+1)) true
  width : out 11=List.replicate (x.length+1) true
  arity : out 2=frame arityBits
  rawArity : out 3=List.replicate (value arityBits) true
  stream : out 231=FieldList.stream (DAGChecks.words bits)
  count : out 242=CompareMachine.word (DAGChecks.words bits).length
  payload : out 548=frame (BitFields.payload (PCPPNativeCanonical.outputWord bits))
  payloadCount : out 415=CompareMachine.word (BitFields.payload (PCPPNativeCanonical.outputWord bits)).length
  header : readTapeBit (out 201) 0=true ↔ PCPPNativeCanonical.headerValid bits
  list : readTapeBit (out 373) 0=true ↔ ∃ values,CanonicalBinary.encodeBalancedList values=value (PCPPNativeCanonical.nodeWord bits)
  natural : readTapeBit (out 549) 0=true ↔ (CanonicalBinary.decodeNat (value (PCPPNativeCanonical.outputWord bits))).isSome
  flag : out 1306=[true]
  fresh : ∀ i,552 ≤ i.val → i≠1306 → out i=[]

theorem prepare_run (x bits arityBits : List Bool) : ∃ out,
    ClockJoin.ReadyRun prepare (prepareBudget x bits) (input x bits arityBits) out ∧
      Prepared x bits arityBits out:=by
  obtain ⟨p,hp,hcap,_,hw,hx⟩:=InputPower.input_power_retained 24 coefficient 1 x
  have h0:=hp.focus powerSlots power_injective (input x bits arityBits) (power_input x bits arityBits)
  obtain ⟨f,hf,fs,fc,fp,fpc,fh,fl,fnat⟩:=DAGFields.fields_run x bits
  have h1:=hf.focus fieldSlots field_injective (install powerSlots (input x bits arityBits) p)
    (field_input x bits arityBits p hx)
  have first:=ClockJoin.join power fields _ _ _ _ _ h0 h1
  let before:=install fieldSlots (install powerSlots (input x bits arityBits) p) f
  have fresh : ∀ i : Fin tapes,552 ≤ i.val → before i=[]:=by
    intro i hi
    rw [show before i=install fieldSlots _ f i by rfl,
      install_other _ _ _ _ (field_outside i (by omega) (by omega) (Or.inr hi)),
      install_other _ _ _ _ (power_outside i (by omega) (Or.inr (by omega)))]
    simp only [input]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  have last:=prime_run before (fresh 1306 (by decide))
  have hall:=ClockJoin.join prepareFirst prime _ _ _ _ _ first last
  refine ⟨_,hall,?_⟩
  constructor
  · rw [Function.update_of_ne (by decide)]
    change install fieldSlots _ f 63=_
    rw [install_other _ _ _ _ (field_outside 63 (by decide) (by decide) (Or.inl (by decide)))]
    change install powerSlots _ p (powerSlots 60)=_
    rw [install_slot _ power_injective]
    exact hcap
  · rw [Function.update_of_ne (by decide)]
    change install fieldSlots _ f 11=_
    rw [install_other _ _ _ _ (field_outside 11 (by decide) (by decide) (Or.inl (by decide)))]
    change install powerSlots _ p (powerSlots 8)=_
    rw [install_slot _ power_injective]
    exact hw
  · rw [Function.update_of_ne (by decide)]
    change install fieldSlots _ f 2=_
    rw [install_other _ _ _ _ (field_outside 2 (by decide) (by decide) (Or.inl (by decide))),
      install_other _ _ _ _ (power_outside 2 (by decide) (Or.inl (by decide)))]
    rfl
  · rw [Function.update_of_ne (by decide)]
    change install fieldSlots _ f 3=_
    rw [install_other _ _ _ _ (field_outside 3 (by decide) (by decide) (Or.inl (by decide))),
      install_other _ _ _ _ (power_outside 3 (by decide) (Or.inl (by decide)))]
    rfl
  · rw [Function.update_of_ne (by decide)]
    change install fieldSlots _ f (fieldSlots 167)=_
    rw [install_slot _ field_injective,fs]
  · rw [Function.update_of_ne (by decide)]
    change install fieldSlots _ f (fieldSlots 178)=_
    rw [install_slot _ field_injective,fc]
  · rw [Function.update_of_ne (by decide)]
    change install fieldSlots _ f (fieldSlots 484)=_
    rw [install_slot _ field_injective,fp]
  · rw [Function.update_of_ne (by decide)]
    change install fieldSlots _ f (fieldSlots 351)=_
    rw [install_slot _ field_injective,fpc]
  · rw [Function.update_of_ne (by decide)]
    change readTapeBit (install fieldSlots _ f (fieldSlots 137)) 0=true ↔_
    rw [install_slot _ field_injective]
    exact fh
  · rw [Function.update_of_ne (by decide)]
    change readTapeBit (install fieldSlots _ f (fieldSlots 309)) 0=true ↔_
    rw [install_slot _ field_injective]
    exact fl
  · rw [Function.update_of_ne (by decide)]
    change readTapeBit (install fieldSlots _ f (fieldSlots 485)) 0=true ↔_
    rw [install_slot _ field_injective]
    exact fnat
  · exact Function.update_self _ _ _
  · intro i hi hn
    rw [Function.update_of_ne hn]
    exact fresh i hi

end NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
