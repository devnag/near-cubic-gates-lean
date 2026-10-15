import Proof.Amplification.RecoveryTseitinNativeFormula

/-! Produce the common cubic capacity and original node-count sentinel from
raw unary arity and node count, preserving the native graph and output index. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (n count output : Nat) (word : List Bool) (i : Fin 1370) : List Bool :=
  if i=0 then List.replicate n true else if i=1062 then word else
  if i=1339 then List.replicate output true else if i=1342 then List.replicate count true else []
def sumSlots : Fin 4→Fin 1370 := ![0,1342,1343,1344]
def powerSlots (i : Fin 20) : Fin 1370 :=
  if i=0 then 1343 else if i=9 then 1336 else ⟨1344+i.val,by have hi:=i.isLt; omega⟩
def countSlots : Fin 4→Fin 1370 := ![1342,1364,1338,1365]
theorem sum_injective : Function.Injective sumSlots := by decide
theorem count_injective : Function.Injective countSlots := by decide
theorem power_injective : Function.Injective powerSlots := by
  intro i j he
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [powerSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
theorem power_away (i : Fin 1370) (hi : i.val<1344) (h6 : i≠1336) (h3 : i≠1343) :
    ∀ j,powerSlots j≠i := by
  intro j he
  have hv:=congrArg Fin.val he
  have hn6 : i.val≠1336:=fun h=>h6 (Fin.ext h)
  have hn3 : i.val≠1343:=fun h=>h3 (Fin.ext h)
  dsimp only [powerSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
noncomputable def sumMachine:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def powerMachine:=RecoveryFocus.machine powerSlots (PCPSerializerCapacity.Power.machine 3 2199023255552)
noncomputable def countMachine:=RecoveryFocus.machine countSlots Counter.machine
noncomputable def first:=Composition.machine sumMachine powerMachine
noncomputable def driversMachine:=Composition.machine first countMachine
def driversBudget (n count : Nat) :=
  (2*(n+count)+6+1+PCPSerializerCapacity.Power.budget 3 2199023255552 (n+count))+1+Counter.budget count

theorem drivers_run (n count output : Nat) (word : List Bool) : ∃ out,
    ClockJoin.ReadyRun driversMachine (driversBudget n count) (input n count output word) out ∧
      out 1336=List.replicate (Reuse.capacity n count) true ∧
      out 1338=CompareMachine.word count ∧ out 1342=List.replicate count true ∧
      (∀ i : Fin 1342,i≠1336 → i≠1338 → out (i.castAdd 28)=input n count output word (i.castAdd 28)) := by
  let sumOut : Fin 4→List Bool := ![List.replicate n true,List.replicate count true,
    List.replicate (n+count) true,List.replicate (n+count+2) false]
  let middle:=install sumSlots (input n count output word) sumOut
  have hsum:=(ClockUnarySum.sum_ready n count).focus sumSlots sum_injective (input n count output word)
    (by intro i; fin_cases i <;> rfl)
  have m0 : middle 0=List.replicate n true := install_slot sumSlots sum_injective _ sumOut 0
  have mc : middle 1342=List.replicate count true := install_slot sumSlots sum_injective _ sumOut 1
  have ms : middle 1343=List.replicate (n+count) true := install_slot sumSlots sum_injective _ sumOut 2
  have mother (i : Fin 1370) (hi : i≠0 ∧ i≠1342 ∧ i≠1343 ∧ i≠1344) :
      middle i=input n count output word i :=
    install_other sumSlots _ sumOut i (by
      intro j he
      fin_cases j
      · exact hi.1 he.symm
      · exact hi.2.1 he.symm
      · exact hi.2.2.1 he.symm
      · exact hi.2.2.2 he.symm)
  obtain ⟨power,hpower,psource,pcap⟩:=PCPSerializerCapacity.Power.capacity_run 3 2199023255552 (n+count)
  have hinput : ∀ i : Fin 20,middle (powerSlots i)=DimensionPolynomial.input 3 (n+count) i := by
    intro i
    fin_cases i
    · exact ms
    all_goals rw [mother _ (by decide)]; rfl
  have hp:=hpower.focus powerSlots power_injective middle hinput
  let powered:=install powerSlots middle power
  have pc : powered 1336=List.replicate (Reuse.capacity n count) true :=
    (install_slot powerSlots power_injective middle power 9).trans pcap
  have p0 : powered 0=List.replicate n true :=
    (install_other powerSlots middle power 0 (power_away 0 (by decide) (by decide) (by decide))).trans m0
  have pcount : powered 1342=List.replicate count true :=
    (install_other powerSlots middle power 1342 (power_away 1342 (by decide) (by decide) (by decide))).trans mc
  have pblank (i : Fin 1370) (hi : i=1338 ∨ i=1364 ∨ i=1365) : powered i=[] := by
    dsimp only [powered]
    rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      have hj:=j.isLt
      dsimp only [powerSlots] at hv
      rcases hi with rfl|rfl|rfl <;> split_ifs at hv <;> dsimp at hv <;> omega)]
    rw [mother i (by rcases hi with rfl|rfl|rfl <;> decide)]
    rcases hi with rfl|rfl|rfl <;> rfl
  obtain ⟨counter,hcounter,csource,cword⟩:=DriverAtoms.counter_run count
  have hc:=hcounter.focus countSlots count_injective powered (by
    intro i
    fin_cases i
    · exact pcount
    · exact pblank 1364 (by simp)
    · exact pblank 1338 (by simp)
    · exact pblank 1365 (by simp))
  let out:=install countSlots powered counter
  have hfirst:=ClockJoin.join sumMachine powerMachine _ _ _ _ _ hsum hp
  have hwhole:=ClockJoin.join first countMachine _ _ _ _ _ hfirst hc
  refine ⟨out,hwhole,?_,?_,?_,?_⟩
  · exact (install_other countSlots powered counter 1336 (by decide)).trans pc
  · exact (install_slot countSlots count_injective powered counter 2).trans cword
  · exact (install_slot countSlots count_injective powered counter 0).trans csource
  · intro i h6 h8
    have hi:=i.isLt
    have hn6 : i.val≠1336:=fun h=>h6 (Fin.ext h)
    have hn8 : i.val≠1338:=fun h=>h8 (Fin.ext h)
    dsimp only [out]
    rw [install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      fin_cases j <;> dsimp [countSlots] at hv <;> omega)]
    by_cases h0 : i=0
    · subst i; exact p0
    dsimp only [powered]
    rw [install_other _ _ _ _ (power_away _ (by simp only [Fin.val_castAdd]; omega)
      (by intro he; have hv:=congrArg Fin.val he; exact h6 (Fin.ext hv))
      (by intro he; have hv:=congrArg Fin.val he; change i.val=1343 at hv; omega))]
    exact mother _ (by
      have hn0 : i.val≠0:=fun h=>h0 (Fin.ext h)
      refine ⟨?_,?_,?_,?_⟩
      all_goals
        intro he
        have hv:=congrArg Fin.val he
        simp at hv
        omega)

end NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
