import Proof.CaseAnalysis.RowsSignedAppend

/-! The three numeric tests needed by the canonical signed-integer guard.
All scans use framed binary words, including padded and empty zero words. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerTests
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics CloseoutWitness
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bootRaw : Machine 5 5 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==4
  rule:=fun q _=>if q.val=0 then
      some ⟨1,![some false,some true,some true,some true,some true],![.stay,.right,.stay,.stay,.stay]⟩
    else if q.val=1 then
      some ⟨2,![none,some true,none,none,none],![.stay,.right,.stay,.stay,.stay]⟩
    else if q.val=2 then
      some ⟨3,![none,some false,none,none,none],![.stay,.left,.stay,.stay,.stay]⟩
    else if q.val=3 then
      some ⟨4,fun _=>none,![.stay,.left,.stay,.stay,.stay]⟩
    else none
def constants : Fin 5→List Bool:=![frame [],frame [true],[true],[true],[true]]
def observed (r : ExecutionReceipt 5 5):=(List.ofFn r.final.tapes,List.ofFn r.final.heads,r.steps)
theorem boot_run : ClockJoin.ReadyRun bootRaw 4 (fun _=>[]) constants:=by
  have h:(run bootRaw 4 (fun _=>[])).map observed=
      some (List.ofFn constants,List.ofFn (fun _ : Fin 5=>0),4):=by rfl
  cases hr:run bootRaw 4 (fun _=>[]) with
  | none=>simp [hr] at h
  | some r=>
    simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq,observed] at h
    exact ⟨r,hr,List.ofFn_injective h.1,
      fun i=>congrFun (List.ofFn_injective h.2.1) i,h.2.2.le⟩

def bootSlots : Fin 5→Fin 10:=![2,3,4,5,6]
def firstSlots : Fin 4→Fin 10:=![0,2,4,7]
def secondSlots : Fin 4→Fin 10:=![0,3,5,8]
def thirdSlots : Fin 4→Fin 10:=![1,2,6,9]
theorem boot_injective : Function.Injective bootSlots:=by decide
theorem first_injective : Function.Injective firstSlots:=by decide
theorem second_injective : Function.Injective secondSlots:=by decide
theorem third_injective : Function.Injective thirdSlots:=by decide
def input (left mag : List Bool) : Fin 10→List Bool:=
  ![frame left,frame mag,[],[],[],[],[],[],[],[]]
def primed (left mag : List Bool) : Fin 10→List Bool:=
  ![frame left,frame mag,frame [],frame [true],[true],[true],[true],[],[],[]]
def compared (left right : List Bool) : Fin 4→List Bool:=
  ![frame left,frame right,[decide (value left=value right)],
    List.replicate (2*max left.length right.length+1) false]
noncomputable def firstData (left mag : List Bool):=install firstSlots (primed left mag) (compared left [])
noncomputable def secondData (left mag : List Bool):=install secondSlots (firstData left mag) (compared left [true])
noncomputable def finalData (left mag : List Bool):=install thirdSlots (secondData left mag) (compared mag [])
noncomputable def boot:=RecoveryFocus.machine bootSlots bootRaw
noncomputable def first:=RecoveryFocus.machine firstSlots NumericEquality.readyMachine
noncomputable def second:=RecoveryFocus.machine secondSlots NumericEquality.readyMachine
noncomputable def third:=RecoveryFocus.machine thirdSlots NumericEquality.readyMachine
noncomputable def start:=Composition.machine boot first
noncomputable def middle:=Composition.machine start second
noncomputable def machine:=Composition.machine middle third

theorem prime_run (left mag : List Bool) : ClockJoin.ReadyRun boot 4 (input left mag) (primed left mag):=by
  have h:=bounded_focus bootSlots boot_injective _ _ _ boot_run (input left mag)
    (by intro i;fin_cases i <;> rfl)
  have he:install bootSlots (input left mag) constants=primed left mag:=by
    funext i;fin_cases i
    all_goals first
      | exact install_slot _ boot_injective _ _ 0
      | exact install_slot _ boot_injective _ _ 1
      | exact install_slot _ boot_injective _ _ 2
      | exact install_slot _ boot_injective _ _ 3
      | exact install_slot _ boot_injective _ _ 4
      | exact install_other _ _ _ _ (by decide)
  rw [he] at h
  exact h

theorem equality_run (left right : List Bool) :
    ClockJoin.ReadyRun NumericEquality.readyMachine (4*max left.length right.length+4)
      ![frame left,frame right,[true],[]] (compared left right):=by
  obtain ⟨r,hr,rt,rh,rs⟩:=NumericEquality.equality_ready left right [] [] true 0
  exact ⟨r,by simpa only [List.append_nil,List.replicate_zero] using hr,
    by simpa only [List.append_nil,Bool.true_and,Nat.zero_max,compared] using rt,rh,rs.le⟩

theorem second_input (left mag : List Bool) : ∀ i,
    firstData left mag (secondSlots i)=![frame left,frame [true],[true],[]] i:=by
  intro i;fin_cases i
  · change install firstSlots _ _ (firstSlots 0)=_
    rw [install_slot _ first_injective];rfl
  all_goals rw [firstData,install_other _ _ _ _ (by decide)];rfl

theorem third_input (left mag : List Bool) : ∀ i,
    secondData left mag (thirdSlots i)=![frame mag,frame [],[true],[]] i:=by
  intro i;fin_cases i
  all_goals rw [secondData,install_other _ _ _ _ (by decide)]
  · rw [firstData,install_other _ _ _ _ (by decide)];rfl
  · change install firstSlots _ _ (firstSlots 1)=_
    rw [install_slot _ first_injective];rfl
  all_goals rw [firstData,install_other _ _ _ _ (by decide)];rfl

def time (left mag : List Bool):=
  ((4+1+(4*max left.length 0+4))+1+(4*max left.length 1+4))+1+(4*max mag.length 0+4)
def budget (left mag : List Bool):=12*(left.length+mag.length+1)+24
theorem time_bound (left mag : List Bool) : time left mag ≤ budget left mag:=by
  unfold time budget
  omega

theorem tests_run (left mag : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget left mag) (input left mag) out ∧
      out 0=frame left ∧ out 1=frame mag ∧
      out 4=[decide (value left=0)] ∧ out 5=[decide (value left=1)] ∧
      out 6=[decide (value mag=0)]:=by
  have h0:=bounded_focus firstSlots first_injective _ _ _ (equality_run left [])
    (primed left mag) (by intro i;fin_cases i <;> rfl)
  have h1:=bounded_focus secondSlots second_injective _ _ _ (equality_run left [true])
    (firstData left mag) (second_input left mag)
  have h2:=bounded_focus thirdSlots third_injective _ _ _ (equality_run mag [])
    (secondData left mag) (third_input left mag)
  have ha:=ClockJoin.join boot first _ _ _ _ _ (prime_run left mag) h0
  have hb:=ClockJoin.join start second _ _ _ _ _ ha h1
  have hc:=ClockJoin.join middle third _ _ _ _ _ hb h2
  have more:=ClockJoin.enlarge machine (time left mag) (budget left mag) _ _ hc (time_bound left mag)
  refine ⟨finalData left mag,more,?_,?_,?_,?_,?_⟩
  · rw [finalData,install_other _ _ _ _ (by decide)]
    change install secondSlots _ _ (secondSlots 0)=_
    rw [install_slot _ second_injective];rfl
  · change install thirdSlots _ _ (thirdSlots 0)=_
    rw [install_slot _ third_injective];rfl
  · rw [finalData,install_other _ _ _ _ (by decide),secondData,install_other _ _ _ _ (by decide)]
    change install firstSlots _ _ (firstSlots 2)=_
    rw [install_slot _ first_injective];rfl
  · rw [finalData,install_other _ _ _ _ (by decide)]
    change install secondSlots _ _ (secondSlots 2)=_
    rw [install_slot _ second_injective];rfl
  · change install thirdSlots _ _ (thirdSlots 2)=_
    rw [install_slot _ third_injective];rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerTests
