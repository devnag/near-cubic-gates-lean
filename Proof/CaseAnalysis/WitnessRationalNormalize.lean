import Proof.CaseAnalysis.WitnessRationalWidth

/-! Actual coefficient fields are normalized at the produced policy width.
The single pre-gcd flag checks canonical framing, integer/natural validity,
positive denominator, and both original payload lengths. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalNormalize
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 539) : Fin 552:=i.castAdd 13
def leftSlots : Fin 5→Fin 552:=![539,343,540,541,542]
def rightSlots : Fin 5→Fin 552:=![539,535,543,544,545]
def kindSlots : Fin 6→Fin 552:=![535,546,547,548,549,550]
theorem old_injective : Function.Injective old:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 552=>k.val) h)
def input (b : ℕ) (bits : List Bool) (i : Fin 552):=
  if i.val=539 then List.replicate b true else if i.val=1 then frame bits else []
def squeezed (b : ℕ) (bits : List Bool) : Fin 5→List Bool:=
  ![List.replicate b true,frame bits,frame (ClockNormalize.resize b bits),
    [decide (bits.length ≤ b)],List.replicate (2*b+1) false]
noncomputable def cold:=RecoveryFocus.machine old RationalCold.machine
noncomputable def left:=RecoveryFocus.machine leftSlots ClockNormalize.machine
noncomputable def right:=RecoveryFocus.machine rightSlots ClockNormalize.machine
noncomputable def kind:=RecoveryFocus.machine kindSlots CompetitorWitnessKind.machine
noncomputable def cbank (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool):=install old (input b bits) c
noncomputable def lbank (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool):=
  install leftSlots (cbank b bits c) (squeezed b (RationalCold.numerator bits))
noncomputable def rbank (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool):=
  install rightSlots (lbank b bits c) (squeezed b (RationalCold.denominator bits))
def kindOutput (bits : List Bool):=CompetitorWitnessKind.tapes
  (CompetitorWitnessKind.after (RationalCold.denominator bits))
  (CompetitorWitnessKind.flags (RationalCold.denominator bits)) (2*(RationalCold.denominator bits).length+1)
noncomputable def kbank (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool):=
  install kindSlots (rbank b bits c) (kindOutput bits)
def passes (b : ℕ) (bits : List Bool) : Prop:=PairHeader.valid bits ∧
  (CanonicalBinary.decodeInt (value (RationalCold.numeratorWord bits))).isSome ∧
  (CanonicalBinary.decodeNat (value (RationalCold.denominatorWord bits))).isSome ∧
  value (RationalCold.denominator bits)≠0 ∧
  (RationalCold.numerator bits).length ≤ b ∧ (RationalCold.denominator bits).length ≤ b
instance (b : ℕ) (bits : List Bool) : Decidable (passes b bits):=by
  unfold passes PairHeader.valid
  infer_instance
def bit (bank : Fin 552→List Bool):=
  readTapeBit (bank 148) 0 && readTapeBit (bank 360) 0 && readTapeBit (bank 536) 0 &&
    !readTapeBit (bank 546) 0 && readTapeBit (bank 541) 0 && readTapeBit (bank 544) 0
def finished (bank : Fin 552→List Bool):=Function.update bank 551 [bit bank]
def finish : Machine 552 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q scan=>if q.val=0 then
    some ⟨1,fun i=>if i=551 then some (scan 148 && scan 360 && scan 536 && !scan 546 && scan 541 && scan 544)
      else none,fun _=>.stay⟩ else none
noncomputable def first:=Composition.machine cold left
noncomputable def second:=Composition.machine first right
noncomputable def third:=Composition.machine second kind
noncomputable def machine:=Composition.machine third finish
def budget (b : ℕ) (bits : List Bool):=
  RationalCold.budget bits+1+(4*b+4)+1+(4*b+4)+1+
    (16*(RationalCold.denominator bits).length+27)+1+1

theorem squeezed_run (b : ℕ) (bits : List Bool) :
    ClockJoin.ReadyRun ClockNormalize.machine (4*b+4) (ClockNormalize.input b bits) (squeezed b bits):=by
  obtain ⟨r,hr,h0,h1,h2,h3,h4,hh,hs⟩:=ClockNormalize.normalize_run b bits
  exact ⟨r,hr,by funext i;fin_cases i <;> assumption,hh,hs.le⟩
theorem c_old (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool) (i : Fin 539) :
    cbank b bits c (old i)=c i:=install_slot _ old_injective _ _ _
theorem c_fresh (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool) (i : Fin 552) (hi : 539 ≤ i.val) :
    cbank b bits c i=input b bits i:=by
  apply install_other
  intro j h;have hv:=congrArg Fin.val h;change j.val=i.val at hv;omega
theorem left_input (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool)
    (hn : c 343=frame (RationalCold.numerator bits)) :
    ∀ i,cbank b bits c (leftSlots i)=ClockNormalize.input b (RationalCold.numerator bits) i:=by
  intro i;fin_cases i
  · exact c_fresh b bits c 539 (by decide)
  · exact (c_old b bits c 343).trans hn
  all_goals exact c_fresh b bits c _ (by decide)
theorem right_input (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool)
    (hd : c 535=frame (RationalCold.denominator bits)) :
    ∀ i,lbank b bits c (rightSlots i)=ClockNormalize.input b (RationalCold.denominator bits) i:=by
  intro i;fin_cases i
  · change install leftSlots _ _ (leftSlots 0)=_
    rw [install_slot _ (by decide)]
    rfl
  all_goals rw [lbank,install_other _ _ _ _ (by decide)]
  · exact (c_old b bits c 535).trans hd
  all_goals exact c_fresh b bits c _ (by decide)
theorem kind_input (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool) :
    ∀ i,rbank b bits c (kindSlots i)=CompetitorWitnessKind.input (RationalCold.denominator bits) i:=by
  intro i;fin_cases i
  · change install rightSlots _ _ (rightSlots 1)=_
    rw [install_slot _ (by decide)]
    rfl
  all_goals
    rw [rbank,install_other _ _ _ _ (by decide),lbank,install_other _ _ _ _ (by decide)]
    exact c_fresh b bits c _ (by decide)
theorem k_old (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool) (i : Fin 539)
    (hi : i=148 ∨ i=360 ∨ i=536) : kbank b bits c (old i)=c i:=by
  rcases hi with rfl|rfl|rfl
  all_goals
    rw [kbank,install_other _ _ _ _ (by decide),rbank,install_other _ _ _ _ (by decide),
      lbank,install_other _ _ _ _ (by decide)]
    exact c_old b bits c _
theorem k_left (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool) (i : Fin 5)
    (hi : i=2 ∨ i=3) : kbank b bits c (leftSlots i)=squeezed b (RationalCold.numerator bits) i:=by
  rcases hi with rfl|rfl
  all_goals
    rw [kbank,install_other _ _ _ _ (by decide),rbank,install_other _ _ _ _ (by decide)]
    exact install_slot _ (by decide) _ _ _
theorem k_right (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool) (i : Fin 5)
    (hi : i=0 ∨ i=2 ∨ i=3) : kbank b bits c (rightSlots i)=squeezed b (RationalCold.denominator bits) i:=by
  rcases hi with rfl|rfl|rfl
  all_goals
    rw [kbank,install_other _ _ _ _ (by decide)]
    exact install_slot _ (by decide) _ _ _
theorem k_zero (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool) :
    kbank b bits c 546=[decide (value (RationalCold.denominator bits)=0)]:=by
  change install kindSlots _ _ (kindSlots 1)=_
  rw [install_slot _ (by decide)]
  rfl
theorem k_blank (b : ℕ) (bits : List Bool) (c : Fin 539→List Bool) : kbank b bits c 551=[]:=by
  rw [kbank,install_other _ _ _ _ (by decide),rbank,install_other _ _ _ _ (by decide),
    lbank,install_other _ _ _ _ (by decide)]
  exact c_fresh b bits c _ (by decide)
theorem finish_run (bank : Fin 552→List Bool) (hblank : bank 551=[]) :
    ClockJoin.ReadyRun finish 1 bank (finished bank):=by
  let final : Configuration 552 2:=⟨1,fun _=>0,finished bank⟩
  have hs:step finish (initialConfiguration finish bank)=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=551
      · subst i
        simp [applyAction,initialConfiguration,finish,final,finished,bit,Configuration.scanned,hblank,writeTapeBit]
      · simp [applyAction,initialConfiguration,finish,final,finished,hi]
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs.le⟩

theorem normalize_run (b : ℕ) (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget b bits) (input b bits) output ∧
      output 551=[decide (passes b bits)] ∧
      output 539=List.replicate b true ∧
      output 540=frame (ClockNormalize.resize b (RationalCold.numerator bits)) ∧
      output 543=frame (ClockNormalize.resize b (RationalCold.denominator bits)):=by
  obtain ⟨c,hc,hhead,hint,hnat,_,hnum,hden,_⟩:=RationalCold.fields_run bits
  have hc':=hc.focus old old_injective (input b bits) (by
    intro i
    simp only [input,old,RationalCold.input,Fin.val_castAdd,if_neg (show i.val≠539 by omega)]
    rfl)
  have hl:=(squeezed_run b (RationalCold.numerator bits)).focus leftSlots (by decide) (cbank b bits c)
    (left_input b bits c hnum)
  have hr:=(squeezed_run b (RationalCold.denominator bits)).focus rightSlots (by decide) (lbank b bits c)
    (right_input b bits c hden)
  obtain ⟨kr,hkr,krt,krh,krs⟩:=CompetitorWitnessKind.kind_ready (RationalCold.denominator bits)
  have hk:ClockJoin.ReadyRun CompetitorWitnessKind.machine (16*(RationalCold.denominator bits).length+27)
      (CompetitorWitnessKind.input (RationalCold.denominator bits)) (kindOutput bits):=⟨kr,hkr,krt,krh,krs.le⟩
  have hk':=hk.focus kindSlots (by decide) (rbank b bits c) (kind_input b bits c)
  have h1:=ClockJoin.join cold left _ _ _ _ _ hc' hl
  have h2:=ClockJoin.join first right _ _ _ _ _ h1 hr
  have h3:=ClockJoin.join second kind _ _ _ _ _ h2 hk'
  have hall:=ClockJoin.join third finish _ _ _ _ _ h3 (finish_run (kbank b bits c) (k_blank b bits c))
  refine ⟨finished (kbank b bits c),hall,?_,?_,?_,?_⟩
  · change [bit (kbank b bits c)]=_
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    unfold bit
    have h148:kbank b bits c 148=c 148:=k_old b bits c 148 (Or.inl rfl)
    have h360:kbank b bits c 360=c 360:=k_old b bits c 360 (Or.inr (Or.inl rfl))
    have h536:kbank b bits c 536=c 536:=k_old b bits c 536 (Or.inr (Or.inr rfl))
    have h541:kbank b bits c 541=[decide ((RationalCold.numerator bits).length ≤ b)]:=k_left b bits c 3 (Or.inr rfl)
    have h544:kbank b bits c 544=[decide ((RationalCold.denominator bits).length ≤ b)]:=k_right b bits c 3 (Or.inr (Or.inr rfl))
    rw [h148,h360,h536,h541,h544,k_zero]
    simp only [Bool.and_eq_true,decide_eq_true_eq,hhead,hint,hnat]
    simp only [readTapeBit,List.getD,List.getElem?_cons_zero,Option.getD_some,
      Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not,passes,and_assoc]
  · exact k_right b bits c 0 (Or.inl rfl)
  · exact k_left b bits c 2 (Or.inl rfl)
  · exact k_right b bits c 2 (Or.inr (Or.inl rfl))

end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalNormalize
