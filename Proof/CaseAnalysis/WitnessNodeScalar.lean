import Proof.CaseAnalysis.WitnessNodeSmall
import Proof.Amplification.RecoveryPrefixCompare

/-! One fixed scalar worker is shared by all three node fields. It compares
binary payloads to the physically supplied arity and current-node bounds,
and retains the small-value flags and source payload. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeScalar
open LocalBitMultitape RecoveryRootRound RecoveryExecution CompetitorRationalProducts RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def smallSlots : Fin 11 → Fin 21:=![0,4,5,6,7,8,9,10,11,12,13]
def normSlots : Fin 5 → Fin 21:=![1,4,14,15,16]
def firstSlots : Fin 4 → Fin 21:=![2,14,17,18]
def secondSlots : Fin 4 → Fin 21:=![3,14,19,20]
theorem small_injective : Function.Injective smallSlots:=by decide
theorem norm_injective : Function.Injective normSlots:=by decide
theorem first_injective : Function.Injective firstSlots:=by decide
theorem second_injective : Function.Injective secondSlots:=by decide

def input (w : ℕ) (left right bits : List Bool) : Fin 21 → List Bool:=
  ![List.replicate 3 true,List.replicate w true,frame left,frame right,frame bits,
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
def booted (w : ℕ) (left right bits : List Bool) : Fin 21 → List Bool:=
  ![List.replicate 3 true,List.replicate w true,frame left,frame right,frame bits,
    [],[],[],[],[],[],[],[],[],[],[],[],[false],[],[false],[]]
def bootSlots : Fin 2 → Fin 21:=![17,19]
theorem boot_injective : Function.Injective bootSlots:=by decide
def bootRaw : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q.val=1)
  rule:=fun _ _=>some ⟨1,fun _=>some false,fun _=>.stay⟩
noncomputable def boot:=RecoveryFocus.machine bootSlots bootRaw
theorem bootRaw_run : ClockJoin.ReadyRun bootRaw 1 (fun _=>[]) (fun _=>[false]):=by
  let final : Configuration 2 2:=⟨1,fun _=>0,fun _=>[false]⟩
  have hs : step bootRaw (initialConfiguration bootRaw (fun _=>[]))=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  obtain ⟨r,hr,hf,ht⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],ht.le⟩
theorem boot_run (w : ℕ) (left right bits : List Bool) :
    ClockJoin.ReadyRun boot 1 (input w left right bits) (booted w left right bits):=by
  have h:=bounded_focus bootSlots boot_injective _ _ _ bootRaw_run (input w left right bits)
    (by intro i;fin_cases i <;> rfl)
  have he:install bootSlots (input w left right bits) (fun _=>[false])=booted w left right bits:=by
    funext i
    by_cases h17:i=17
    · subst i
      change install bootSlots _ _ (bootSlots 0)=_
      rw [install_slot _ boot_injective];rfl
    · by_cases h19:i=19
      · subst i
        change install bootSlots _ _ (bootSlots 1)=_
        rw [install_slot _ boot_injective];rfl
      · rw [install_other _ _ _ _ (by intro j;fin_cases j;exact Ne.symm h17;exact Ne.symm h19)]
        fin_cases i <;> simp_all [input,booted]
  rw [he] at h
  exact h

noncomputable def small:=RecoveryFocus.machine smallSlots NodeSmall.machine
noncomputable def norm:=RecoveryFocus.machine normSlots ClockNormalize.machine
noncomputable def first:=RecoveryFocus.machine firstSlots RecoveryPrefixCompare.machine
noncomputable def second:=RecoveryFocus.machine secondSlots RecoveryPrefixCompare.machine
noncomputable def initial:=Composition.machine boot small
noncomputable def normalized:=Composition.machine initial norm
noncomputable def compared:=Composition.machine normalized first
noncomputable def machine:=Composition.machine compared second
def budget (w : ℕ):=12*w+58

theorem small_input (w : ℕ) (left right bits : List Bool) :
    ∀ i,booted w left right bits (smallSlots i)=NodeSmall.input bits i:=by
  intro i;fin_cases i <;> rfl

theorem norm_input (w : ℕ) (left right bits : List Bool) (out : Fin 11 → List Bool)
    (hp : out 1=frame bits) :
    ∀ i,install smallSlots (booted w left right bits) out (normSlots i)=ClockNormalize.input w bits i:=by
  intro i
  fin_cases i
  · rw [install_other _ _ _ _ (by decide)];rfl
  · change install smallSlots _ out (smallSlots 1)=_
    rw [install_slot _ small_injective,hp];rfl
  all_goals rw [install_other _ _ _ _ (by decide)];rfl

theorem first_input (w : ℕ) (left right bits : List Bool) (smallOut : Fin 11 → List Bool)
    (normOut : Fin 5 → List Bool) (hp : normOut 2=frame (ClockNormalize.resize w bits)) :
    ∀ i,install normSlots (install smallSlots (booted w left right bits) smallOut) normOut (firstSlots i)=
      ![frame left,frame (ClockNormalize.resize w bits),[false],List.replicate 0 false] i:=by
  intro i
  fin_cases i
  · rw [install_other _ _ _ _ (by decide),install_other _ _ _ _ (by decide)];rfl
  · change install normSlots _ normOut (normSlots 2)=_
    rw [install_slot _ norm_injective,hp];rfl
  all_goals rw [install_other _ _ _ _ (by decide),install_other _ _ _ _ (by decide)];rfl

def compareOut (left right : List Bool) : Fin 4 → List Bool:=
  ![frame left,frame right,[decide (value left ≤ value right)],List.replicate (2*left.length+3) false]

theorem compare_run (left right : List Bool) (hw : left.length=right.length) :
    ClockJoin.ReadyRun RecoveryPrefixCompare.machine (4*left.length+8)
      ![frame left,frame right,[false],List.replicate 0 false] (compareOut left right):=by
  obtain ⟨r,hr,ht,hh,hs⟩:=RecoveryPrefixCompare.compare_ready left right false 0 hw
  exact ⟨r,hr,by simpa only [Nat.zero_max,compareOut] using ht,hh,hs.le⟩

theorem second_input (w : ℕ) (left right bits : List Bool) (smallOut : Fin 11 → List Bool)
    (normOut : Fin 5 → List Bool) :
    ∀ i,install firstSlots
      (install normSlots (install smallSlots (booted w left right bits) smallOut) normOut)
      (compareOut left (ClockNormalize.resize w bits)) (secondSlots i)=
        ![frame right,frame (ClockNormalize.resize w bits),[false],List.replicate 0 false] i:=by
  intro i
  fin_cases i
  · rw [install_other _ _ _ _ (by decide),install_other _ _ _ _ (by decide),
      install_other _ _ _ _ (by decide)];rfl
  · change install firstSlots _ (compareOut left (ClockNormalize.resize w bits)) (firstSlots 1)=_
    rw [install_slot _ first_injective];rfl
  all_goals
    rw [install_other _ _ _ _ (by decide),install_other _ _ _ _ (by decide),
      install_other _ _ _ _ (by decide)]
    rfl

theorem scalar_run (w : ℕ) (left right bits : List Bool)
    (hl : left.length=w) (hr : right.length=w) (hb : bits.length ≤ w) : ∃ out,
    ClockJoin.ReadyRun machine (budget w) (input w left right bits) out ∧
      out 0=List.replicate 3 true ∧ out 1=List.replicate w true ∧
      out 2=frame left ∧ out 3=frame right ∧ out 4=frame bits ∧
      out 6=[decide (bits.length ≤ 3)] ∧
      (∀ j : Fin 5,out (smallSlots (NodeSmall.tagSlots (j.succ.castAdd 1)))=
        [NodeTag.flags (ClockNormalize.resize 3 bits) j]) ∧
      out 17=[decide (value left ≤ value bits)] ∧ out 19=[decide (value right ≤ value bits)]:=by
  obtain ⟨so,hs,sd,sp,sfit,sflags⟩:=NodeSmall.small_run bits
  have hsmall:=bounded_focus smallSlots small_injective _ _ _ hs
    (booted w left right bits) (small_input w left right bits)
  have hi:=ClockJoin.join boot small _ _ _ _ _ (boot_run w left right bits) hsmall
  obtain ⟨nr,hn,nd,np,nvalue,_,_,nh,nsteps⟩:=ClockNormalize.normalize_run w bits
  have hnready : ClockJoin.ReadyRun ClockNormalize.machine (4*w+4) (ClockNormalize.input w bits) nr.final.tapes:=
    ⟨nr,hn,rfl,nh,nsteps.le⟩
  have hnorm:=bounded_focus normSlots norm_injective _ _ _ hnready
    (install smallSlots (booted w left right bits) so) (norm_input w left right bits so sp)
  have hnormal:=ClockJoin.join initial norm _ _ _ _ _ hi hnorm
  have hfirst:=compare_run left (ClockNormalize.resize w bits)
    (by simpa using hl)
  have hf:=bounded_focus firstSlots first_injective _ _ _ hfirst
    (install normSlots (install smallSlots (booted w left right bits) so) nr.final.tapes)
    (first_input w left right bits so _ nvalue)
  have hcomp:=ClockJoin.join normalized first _ _ _ _ _ hnormal hf
  have hsecond:=compare_run right (ClockNormalize.resize w bits)
    (by simpa using hr)
  have he:=bounded_focus secondSlots second_injective _ _ _ hsecond
    (install firstSlots (install normSlots (install smallSlots (booted w left right bits) so) nr.final.tapes)
      (compareOut left (ClockNormalize.resize w bits))) (second_input w left right bits so _)
  have h:=ClockJoin.join compared second _ _ _ _ _ hcomp he
  have ht:(((1+1+33)+1+(4*w+4))+1+(4*left.length+8))+1+(4*right.length+8)=budget w:=by
    unfold budget;omega
  rw [ht] at h
  refine ⟨_,h,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),install_other _ _ _ _ (by decide),
      install_other _ _ _ _ (by decide)]
    exact (install_slot smallSlots small_injective _ _ 0).trans sd
  · rw [install_other _ _ _ _ (by decide),install_other _ _ _ _ (by decide)]
    exact (install_slot normSlots norm_injective _ _ 0).trans nd
  · rw [install_other _ _ _ _ (by decide)]
    exact install_slot firstSlots first_injective _ _ 0
  · exact install_slot secondSlots second_injective _ _ 0
  · rw [install_other _ _ _ _ (by decide),install_other _ _ _ _ (by decide)]
    exact (install_slot normSlots norm_injective _ _ 1).trans np
  · rw [install_other _ _ _ _ (by decide),install_other _ _ _ _ (by decide),
      install_other _ _ _ _ (by decide)]
    exact (install_slot smallSlots small_injective _ _ 3).trans sfit
  · intro j
    have hloc : ∀ i,secondSlots i≠smallSlots (NodeSmall.tagSlots (j.succ.castAdd 1)):=by
      fin_cases j <;> decide
    have hloc1 : ∀ i,firstSlots i≠smallSlots (NodeSmall.tagSlots (j.succ.castAdd 1)):=by
      fin_cases j <;> decide
    have hloc2 : ∀ i,normSlots i≠smallSlots (NodeSmall.tagSlots (j.succ.castAdd 1)):=by
      fin_cases j <;> decide
    rw [install_other _ _ _ _ hloc,install_other _ _ _ _ hloc1,install_other _ _ _ _ hloc2,
      install_slot _ small_injective]
    exact sflags j
  · rw [install_other _ _ _ _ (by decide)]
    change install firstSlots _ _ (firstSlots 2)=_
    rw [install_slot _ first_injective]
    change [decide (value left ≤ value (ClockNormalize.resize w bits))]=_
    rw [ClockScalarFields.resize_value w bits hb]
  · change install secondSlots _ _ (secondSlots 2)=_
    rw [install_slot _ second_injective]
    change [decide (value right ≤ value (ClockNormalize.resize w bits))]=_
    rw [ClockScalarFields.resize_value w bits hb]

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeScalar
