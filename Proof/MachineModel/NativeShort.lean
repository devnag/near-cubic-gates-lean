import Proof.MachineModel.NativeMeasured
import Proof.Supplier.RowTupleFields

/-! Print the short comparison and zero-index fields used by the empty
native bank, using the existing unary and fixed-width scalar workers. -/
namespace NearCubicWires.ExtIncidence.NativeShort
open LocalBitMultitape RepairOrdinary
open RepairOrdinary.RecoveryRootRound
open RepairOrdinary.RowCommonSize (put focus_put)
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (n w Q : ℕ) : RowCommonSize.Store:=fun i=>
  if i=0 then UnaryTemplate.tape n else if i=1 then List.replicate w true
  else if i=2 then UnaryTemplate.tape Q else []

def data1 (n w Q : ℕ):=put (input n w Q) 3 4
  (CompareMachine.word (n+1)) (List.replicate (n+2) false)
def slots1 : Fin 3→Fin 17:=![0,3,4]
noncomputable def phase1:=RecoveryFocus.machine slots1 (UWalkUnary.machine true true)
noncomputable def joined1:=phase1
theorem ready1 (n w Q : ℕ) : ClockJoin.ReadyRun phase1 (2*n+6) (input n w Q) (data1 n w Q):=by
  apply focus_put _ _ _ _ (DecompositionCountDrivers.template_ready true true n) slots1 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [input,slots1]
  · intro i;fin_cases i <;> simp [put,input,slots1,UWalkUnary.output,UWalkUnary.lead,CompareMachine.word]
theorem joined1_ready (n w Q : ℕ) : ClockJoin.ReadyRun joined1
    ((2*n+6)) (input n w Q) (data1 n w Q):=
  ready1 n w Q

def data2 (n w Q : ℕ):=put (data1 n w Q) 5 6
  (UnaryTemplate.tape w) (List.replicate (w+3) false)
def slots2 : Fin 3→Fin 17:=![1,5,6]
noncomputable def phase2:=RecoveryFocus.machine slots2 (DimensionTemplate.machine false)
noncomputable def joined2:=Composition.machine joined1 phase2
theorem ready2 (n w Q : ℕ) : ClockJoin.ReadyRun phase2 (2*w+8) (data1 n w Q) (data2 n w Q):=by
  apply focus_put _ _ _ _ (DimensionTemplate.ready false w) slots2 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [data1,put,input,slots2,DimensionTemplate.input]
  · intro i;fin_cases i <;> simp [data1,put,input,slots2,DimensionTemplate.output]
theorem joined2_ready (n w Q : ℕ) : ClockJoin.ReadyRun joined2
    ((2*n+6)+1+(2*w+8)) (input n w Q) (data2 n w Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined1_ready n w Q) (ready2 n w Q)

def data3 (n w Q : ℕ):=put (data2 n w Q) 7 8
  (CompareMachine.word w) (List.replicate (w+2) false)
def slots3 : Fin 3→Fin 17:=![5,7,8]
noncomputable def phase3:=RecoveryFocus.machine slots3 (UWalkUnary.machine true false)
noncomputable def joined3:=Composition.machine joined2 phase3
theorem ready3 (n w Q : ℕ) : ClockJoin.ReadyRun phase3 (2*w+6) (data2 n w Q) (data3 n w Q):=by
  apply focus_put _ _ _ _ (DecompositionCountDrivers.template_ready true false w) slots3 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [data2,data1,put,input,slots3]
  · intro i;fin_cases i <;> simp [data2,put,slots3,UWalkUnary.output,UWalkUnary.lead,CompareMachine.word]
theorem joined3_ready (n w Q : ℕ) : ClockJoin.ReadyRun joined3
    ((2*n+6)+1+(2*w+8)+1+(2*w+6)) (input n w Q) (data3 n w Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined2_ready n w Q) (ready3 n w Q)

def data4 (n w Q : ℕ):=put (data3 n w Q) 9 10
  (CompareMachine.word Q) (List.replicate (Q+2) false)
def slots4 : Fin 3→Fin 17:=![2,9,10]
noncomputable def phase4:=RecoveryFocus.machine slots4 (UWalkUnary.machine true false)
noncomputable def joined4:=Composition.machine joined3 phase4
theorem ready4 (n w Q : ℕ) : ClockJoin.ReadyRun phase4 (2*Q+6) (data3 n w Q) (data4 n w Q):=by
  apply focus_put _ _ _ _ (DecompositionCountDrivers.template_ready true false Q) slots4 (by decide) _ 1 2
  · intro i;fin_cases i <;> simp [data3,data2,data1,put,input,slots4]
  · intro i;fin_cases i <;> simp [data3,data2,data1,put,input,slots4,UWalkUnary.output,UWalkUnary.lead,CompareMachine.word]
theorem joined4_ready (n w Q : ℕ) : ClockJoin.ReadyRun joined4
    ((2*n+6)+1+(2*w+8)+1+(2*w+6)+1+(2*Q+6)) (input n w Q) (data4 n w Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined3_ready n w Q) (ready4 n w Q)

def data5 (n w Q : ℕ):=put (data4 n w Q) 11 12
  (CompareMachine.word 1) (List.replicate (2) false)
def slots5 : Fin 2→Fin 17:=![11,12]
noncomputable def phase5:=RecoveryFocus.machine slots5 (HierarchyFixedWord.machine [false,true])
noncomputable def joined5:=Composition.machine joined4 phase5
theorem ready5 (n w Q : ℕ) : ClockJoin.ReadyRun phase5 (6) (data4 n w Q) (data5 n w Q):=by
  apply focus_put _ _ _ _ (RowCommonResources.literal_ready [false,true]) slots5 (by decide) _ 0 1
  · intro i;fin_cases i <;> simp [data4,data3,data2,data1,put,input,slots5]
  · intro i;fin_cases i <;> simp [put,slots5,CompareMachine.word]
theorem joined5_ready (n w Q : ℕ) : ClockJoin.ReadyRun joined5
    ((2*n+6)+1+(2*w+8)+1+(2*w+6)+1+(2*Q+6)+1+(6)) (input n w Q) (data5 n w Q):=
  ClockJoin.join _ _ _ _ _ _ _ (joined4_ready n w Q) (ready5 n w Q)

def zeroSlots : Fin 5→Fin 17:=![1,13,14,15,16]
noncomputable def zero:=RecoveryFocus.machine zeroSlots ClockNormalize.machine
noncomputable def machine:=Composition.machine joined5 zero
def budget (n w Q : ℕ):=2*n+8*w+2*Q+41
theorem short_run (n w Q : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget n w Q) (input n w Q) out ∧
      (∀ i : Fin 13,out (i.castAdd 4)=data5 n w Q (i.castAdd 4)) ∧
      out 14=frame (SignedSortKey.binary w 0):=by
  obtain ⟨z,hz,z0,z2⟩:=RowTupleColdFields.zero_ready w
  have h:=hz.focus zeroSlots (by decide) (data5 n w Q) (by
    intro i;fin_cases i <;> simp [data5,data4,data3,data2,data1,input,put,zeroSlots,ClockScalarFields.zeroInput])
  have whole:=ClockJoin.join _ _ _ _ _ _ _ (joined5_ready n w Q) h
  have time : (2*n+6)+1+(2*w+8)+1+(2*w+6)+1+(2*Q+6)+1+(6)+1+(4*w+4)=budget n w Q:=by unfold budget;omega
  rw [time] at whole
  refine ⟨_,whole,?_,(install_slot zeroSlots (by decide) (data5 n w Q) z 2).trans z2⟩
  intro i
  by_cases hi : i=1
  · subst i;exact (install_slot zeroSlots (by decide) (data5 n w Q) z 0).trans z0
  have notslot : ∀ j,zeroSlots j≠i.castAdd 4:=by
    intro j he
    have hv:=congrArg (fun x : Fin 17=>x.val) he
    have hb:=i.isLt
    have hn : i.val≠1:=fun h=>hi (Fin.ext h)
    fin_cases j <;> simp [zeroSlots] at hv <;> omega
  exact install_other zeroSlots (data5 n w Q) z _ notslot

end NearCubicWires.ExtIncidence.NativeShort
