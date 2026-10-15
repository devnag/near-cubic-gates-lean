import Proof.CaseAnalysis.RowsCountWord

/-! One cold bottom-list traversal, canonical declared-count decoding and
binary equality. The actual list count supplies the retained top domain. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCount
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics CloseoutWitness
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (bottom declared : List Bool) (i : Fin 368) : List Bool:=
  if i.val=0 then frame bottom else if i.val=174 then frame declared else []
def canonSlots (i : Fin 174) : Fin 368:=i.castAdd 194
def natSlots (i : Fin 178) : Fin 368:=⟨174+i.val,by omega⟩
def countSlots (i : Fin 14) : Fin 368:=if i=0 then 41 else ⟨351+i.val,by omega⟩
def equalSlots : Fin 4→Fin 368:=![348,360,365,366]
def flagSlots : Fin 4→Fin 368:=![172,349,365,367]
def count (bottom : List Bool):=(tree (value bottom)).atoms.length
def prime : Machine 1 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>some true,fun _=>.stay⟩ else none
def fold : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bs=>if q.val=0 then
    some ⟨1,![none,none,none,some (bs 0 && bs 1 && bs 2)],fun _=>.stay⟩ else none
noncomputable def canonical:=RecoveryFocus.machine canonSlots CanonicalTest.machine
noncomputable def natural:=RecoveryFocus.machine natSlots NatCold.machine
noncomputable def counter:=RecoveryFocus.machine countSlots CloseoutRowsCountWord.machine
noncomputable def primer:=RecoveryFocus.machine (fun _ : Fin 1=>(365 : Fin 368)) prime
noncomputable def equality:=RecoveryFocus.machine equalSlots NumericEquality.readyMachine
noncomputable def finish:=RecoveryFocus.machine flagSlots fold
noncomputable def phase1:=Composition.machine canonical natural
noncomputable def phase2:=Composition.machine phase1 counter
noncomputable def phase3:=Composition.machine phase2 primer
noncomputable def phase4:=Composition.machine phase3 equality
noncomputable def machine:=Composition.machine phase4 finish
def time (bottom declared : List Bool):=CanonicalTest.budget bottom+NatCold.budget declared+
  CloseoutRowsCountWord.budget (count bottom)+
  4*max (BitFields.payload declared).length (CloseoutRowsCountBinary.bits (count bottom)).length+11

theorem canon_injective : Function.Injective canonSlots:=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin 368=>k.val) h)
theorem nat_injective : Function.Injective natSlots:=by
  intro i j h;have hv:=congrArg (fun k : Fin 368=>k.val) h
  exact Fin.ext (by change 174+i.val=174+j.val at hv;omega)
theorem count_injective : Function.Injective countSlots:=by decide
theorem canon_outside (i : Fin 368) (hi:174 ≤ i.val) : ∀ j,canonSlots j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin 368=>k.val) h
  change j.val=i.val at hv;omega
theorem nat_outside (i : Fin 368) (hi:i.val<174 ∨ 352 ≤ i.val) : ∀ j,natSlots j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin 368=>k.val) h
  change 174+j.val=i.val at hv;omega

theorem nat_input (bits : List Bool) (i : Fin 178) :
    NatCold.input bits i=(if i.val=0 then frame bits else []):=by
  by_cases hi:i.val<174
  · simp [NatCold.input,Fin.addCases,CanonicalTest.input,hi]
  · simp [NatCold.input,Fin.addCases,hi,show i.val≠0 by omega]

theorem prime_run : ClockJoin.ReadyRun prime 1 (fun _=>[]) (fun _=>[true]):=by
  let final:Configuration 1 2:=⟨1,fun _=>0,fun _=>[true]⟩
  have hs:step prime (initialConfiguration prime (fun _=>[]))=some final:=by rfl
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs.le⟩

theorem fold_run (a b c : List Bool) : ClockJoin.ReadyRun fold 1 ![a,b,c,[]]
    ![a,b,c,[readTapeBit a 0 && readTapeBit b 0 && readTapeBit c 0]]:=by
  let final:Configuration 4 2:=⟨1,fun _=>0,
    ![a,b,c,[readTapeBit a 0 && readTapeBit b 0 && readTapeBit c 0]]⟩
  have hs:step fold (initialConfiguration fold ![a,b,c,[]])=some final:=by
    apply congrArg some;apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs.le⟩

theorem count_run (bottom declared : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (time bottom declared) (input bottom declared) out ∧
      out 30=atomStream bottom.length (tree (value bottom)).atoms ∧
      out 356=List.replicate (count bottom) true ∧ out 358=UnaryTemplate.tape (count bottom) ∧
      (readTapeBit (out 367) 0=true ↔
        (∃ values,CanonicalBinary.encodeBalancedList values=value bottom) ∧
        CanonicalBinary.decodeNat (value declared)=some (count bottom)) := by
  obtain ⟨co,hc,cstream,ccount,cflag⟩:=CanonicalTest.fields_run bottom
  have hcan:=hc.focus canonSlots canon_injective (input bottom declared) (by
    intro i
    simp only [input,canonSlots,Fin.val_castAdd,if_neg (show i.val≠174 by omega),CanonicalTest.input])
  let one:=install canonSlots (input bottom declared) co
  have one_new (i : Fin 368) (hi:174 ≤ i.val) : one i=input bottom declared i:=
    install_other _ _ _ _ (canon_outside i hi)
  obtain ⟨no,hn,np,_nc,nflag,ndecode⟩:=NatCold.nat_run declared
  have hnat:=hn.focus natSlots nat_injective one (by
    intro i;rw [one_new _ (by change 174 ≤ 174+i.val;omega)]
    simp only [input,natSlots,if_neg (show 174+i.val≠0 by omega),
      show (174+i.val=174 ↔ i.val=0) by omega,nat_input])
  let two:=install natSlots one no
  have two_old (i : Fin 368) (hi:i.val<174) : two i=co ⟨i.val,hi⟩:=by
    rw [show two=install natSlots one no by rfl,install_other _ _ _ _ (nat_outside i (Or.inl hi))]
    exact install_slot canonSlots canon_injective _ co ⟨i.val,hi⟩
  have two_new (i : Fin 368) (hi:352 ≤ i.val) : two i=[]:=by
    rw [show two=install natSlots one no by rfl,install_other _ _ _ _ (nat_outside i (Or.inr hi)),
      one_new _ (by omega)]
    simp only [input,if_neg (show i.val≠0 by omega),if_neg (show i.val≠174 by omega)]
  obtain ⟨ct,ht,raw,template,_binary⟩:=CloseoutRowsCountWord.word_run (count bottom)
  have hcount:=ht.focus countSlots count_injective two (by
    intro i
    by_cases hi:i=0
    · subst i;exact (two_old 41 (by decide)).trans ccount
    · rw [countSlots,if_neg hi,two_new _ (by change 352 ≤ 351+i.val;have hv:=Fin.pos_iff_ne_zero.mpr hi;omega)]
      simp only [CloseoutRowsCountWord.input,if_neg hi])
  let three:=install countSlots two ct
  have untouched (i : Fin 368) (hi:∀ j,countSlots j≠i) : three i=two i:=install_other _ _ _ _ hi
  have hp:=prime_run.focus (fun _ : Fin 1=>(365 : Fin 368)) (by decide) three (by
    intro i;rw [untouched _ (by decide),two_new _ (by decide)])
  let four:=install (fun _ : Fin 1=>(365 : Fin 368)) three (fun _=>[true])
  have four_other (i : Fin 368) (hi:i≠365) : four i=three i:=
    install_other _ _ _ _ (by intro j;exact Ne.symm hi)
  have four_left:four 348=frame (BitFields.payload declared):=by
    rw [four_other _ (by decide),untouched _ (by decide)]
    exact (install_slot natSlots nat_injective one no 174).trans np
  have four_right:four 360=frame (CloseoutRowsCountBinary.bits (count bottom)):=by
    rw [four_other _ (by decide)]
    exact (install_slot countSlots count_injective two ct 9).trans _binary
  have heq:=CloseoutRowsIntegerTests.equality_run (BitFields.payload declared)
    (CloseoutRowsCountBinary.bits (count bottom))
  have he:=heq.focus equalSlots (by decide) four (by
    intro i;fin_cases i
    · exact four_left
    · exact four_right
    · exact install_slot (fun _ : Fin 1=>(365 : Fin 368)) (by decide) three (fun _=>[true]) 0
    · rw [four_other _ (by decide),untouched _ (by decide),two_new _ (by decide)];rfl)
  let five:=install equalSlots four (CloseoutRowsIntegerTests.compared (BitFields.payload declared)
    (CloseoutRowsCountBinary.bits (count bottom)))
  have five_other (i : Fin 368) (hi:∀ j,equalSlots j≠i) : five i=four i:=install_other _ _ _ _ hi
  have fcanon:five 172=co 172:=by
    rw [five_other _ (by decide),four_other _ (by decide),untouched _ (by decide),two_old _ (by decide)]
    rfl
  have fnat:five 349=no 175:=by
    rw [five_other _ (by decide),four_other _ (by decide),untouched _ (by decide)]
    exact install_slot natSlots nat_injective one no 175
  have fcount:five 365=[decide (value (BitFields.payload declared)=count bottom)]:=by
    change install equalSlots four _ (equalSlots 2)=_
    rw [install_slot _ (by decide)]
    simp only [CloseoutRowsIntegerTests.compared,CloseoutRowsCountBinary.value_bits]
    rfl
  have hf:=(fold_run (five 172) (five 349) (five 365)).focus flagSlots (by decide) five (by
    intro i;fin_cases i
    · rfl
    · rfl
    · rfl
    · rw [five_other _ (by decide),four_other _ (by decide),untouched _ (by decide),two_new _ (by decide)];rfl)
  have h1:=ClockJoin.join canonical natural _ _ _ _ _ hcan hnat
  have h2:=ClockJoin.join phase1 counter _ _ _ _ _ h1 hcount
  have h3:=ClockJoin.join phase2 primer _ _ _ _ _ h2 hp
  have h4:=ClockJoin.join phase3 equality _ _ _ _ _ h3 he
  have hall:=ClockJoin.join phase4 finish _ _ _ _ _ h4 hf
  have htime:(((((CanonicalTest.budget bottom+1+NatCold.budget declared)+1+
      CloseoutRowsCountWord.budget (count bottom))+1+1)+1+
      (4*max (BitFields.payload declared).length (CloseoutRowsCountBinary.bits (count bottom)).length+4))+1+1)=
      time bottom declared:=by unfold time;omega
  rw [htime] at hall
  refine ⟨_,hall,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),five_other _ (by decide),four_other _ (by decide),
      untouched _ (by decide),two_old _ (by decide)]
    exact cstream
  · rw [install_other _ _ _ _ (by decide),five_other _ (by decide),four_other _ (by decide)]
    exact (install_slot countSlots count_injective two ct 5).trans raw
  · rw [install_other _ _ _ _ (by decide),five_other _ (by decide),four_other _ (by decide)]
    exact (install_slot countSlots count_injective two ct 7).trans template
  · change readTapeBit (install flagSlots five _ (flagSlots 3)) 0=true ↔_
    rw [install_slot _ (by decide)]
    change (readTapeBit (five 172) 0 && readTapeBit (five 349) 0 && readTapeBit (five 365) 0)=true ↔_
    rw [fcanon,fnat,fcount]
    rw [show readTapeBit [decide (value (BitFields.payload declared)=count bottom)] 0=
      decide (value (BitFields.payload declared)=count bottom) by rfl]
    simp only [Bool.and_eq_true,decide_eq_true_eq,cflag]
    constructor
    · rintro ⟨⟨hc',hn'⟩,he'⟩
      exact ⟨hc',he' ▸ ndecode hn'⟩
    · rintro ⟨hc',hn'⟩
      have hf':readTapeBit (no 175) 0=true:=nflag.mpr (Option.isSome_iff_exists.mpr ⟨_,hn'⟩)
      exact ⟨⟨hc',hf'⟩,Option.some.inj ((ndecode hf').symm.trans hn')⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCount
