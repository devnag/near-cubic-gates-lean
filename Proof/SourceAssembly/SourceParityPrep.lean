import Proof.SourceAssembly.SourceParityNatural

/- Derive the literal q driver, framed native q cache and reusable gate scratch
from the retained arity tape. Every other input is cold; allocation is paid. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyParityPrep
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RecoveryRootRound CloseoutRowsEstimator
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
noncomputable section

def capSlots (i : Fin 22) : Fin 47:=i.castAdd 25
def natSlots (i : Fin 22) : Fin 47:=if i=0 then 1 else ⟨i.val+21,by omega⟩
def eraseSlots : Fin 3→Fin 47:=![43,11,44]
def copySlots : Fin 3→Fin 47:=![0,45,46]
theorem cap_inj : Function.Injective capSlots:=by decide
theorem nat_inj : Function.Injective natSlots:=by decide
theorem erase_inj : Function.Injective eraseSlots:=by decide
theorem copy_inj : Function.Injective copySlots:=by decide

def first:=RecoveryFocus.machine capSlots Capacity.core
def natural:=RecoveryFocus.machine natSlots Natural.machine
def erase:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
def copy:=RecoveryFocus.machine copySlots (UWalkUnary.machine true false)
def machine:=Composition.machine first (Composition.machine natural (Composition.machine erase copy))
def input (q : Nat) : Fin 47→List Bool:=fun i=>if i=0 then UWalkUnary.source (q+2) q else []
def budget (q : Nat):=(2*q+6+1+DriverPower.budget 2 256 q)+1+
  (Natural.budget q+1+(2*Capacity.value q+4+1+(2*q+6)))
def erased (q : Nat) : Fin 3→List Bool:=
  ![List.replicate (Capacity.value q) false,List.replicate (Capacity.value q) true,
    List.replicate (Capacity.value q+1) false]

theorem erase_ready (q : Nat) : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 1)
    (2*Capacity.value q+4) (![[],List.replicate (Capacity.value q) true,[]]) (erased q) := by
  obtain ⟨r,hr,rt,rh,rs⟩:=RecoveryScratchErase.erase_ready (Capacity.value q) 0 (fun _ : Fin 1=>[]) (by simp)
  have hi : (Fin.addCases (motive:=fun _ : Fin 3=>List Bool) (Fin.addCases (motive:=fun _ : Fin 2=>List Bool) (fun _ : Fin 1=>[]) (fun _ : Fin 1=>List.replicate (Capacity.value q) true))
      (fun _ : Fin 1=>List.replicate 0 false))=(![[],List.replicate (Capacity.value q) true,[]]) := by
    funext i;fin_cases i <;>rfl
  simp only [Nat.zero_max] at rt
  rw [hi] at hr
  refine ⟨r,hr,?_,rh,rs.le⟩
  exact rt.trans (by funext i;fin_cases i <;>rfl)

theorem cap_other (q : Nat) (A : Fin 22→List Bool) (i : Fin 47) (hi : 22 ≤ i.val) :
    install capSlots (input q) A i=[] := by
  rw [install_other capSlots _ _ i (by intro j he;have hv:=congrArg Fin.val he;change j.val=i.val at hv;omega)]
  simp [input,show i≠0 by intro he;subst i;contradiction]

theorem nat_other (A : Fin 47→List Bool) (B : Fin 22→List Bool) (i : Fin 47)
    (hi : i.val<22 ∧ i≠1 ∨ 43 ≤ i.val) : install natSlots A B i=A i := by
  apply install_other
  intro j he
  by_cases hj:j=0
  · simp [natSlots,hj] at he
    subst i
    simp at hi
  · have hv:=congrArg Fin.val he
    simp only [natSlots,hj,if_false] at hv
    rcases hi with hi|hi <;>omega

theorem run (q : Nat) : ∃ A,ClockJoin.ReadyRun machine (budget q) (input q) A ∧
    A 0=UWalkUnary.source (q+2) q ∧A 41=frame (natWord q) ∧
    A 43=List.replicate (Capacity.value q) false ∧A 45=CompareMachine.word q ∧
    A 11=List.replicate (Capacity.value q) true := by
  obtain ⟨cap,hcap,c0,c1,c11⟩:=Capacity.core_run (q+2) q
  let A:=install capSlots (input q) cap
  have hA:=hcap.focus capSlots cap_inj (input q) (by intro i;fin_cases i <;>rfl)
  have a0 : A 0=UWalkUnary.source (q+2) q:=(install_slot capSlots cap_inj (input q) cap 0).trans c0
  have a1 : A 1=List.replicate q true:=(install_slot capSlots cap_inj (input q) cap 1).trans c1
  have a11 : A 11=List.replicate (Capacity.value q) true:=(install_slot capSlots cap_inj (input q) cap 11).trans c11
  obtain ⟨nat,hnat,n20,_n17⟩:=SourceAssemblyParityNatural.cold_run q
  let B:=install natSlots A nat
  have hB:=hnat.focus natSlots nat_inj A (by
    intro i;fin_cases i
    · exact a1
    all_goals exact cap_other q cap _ (by decide))
  have b0 : B 0=UWalkUnary.source (q+2) q:=(nat_other A nat 0 (by decide)).trans a0
  have b11 : B 11=List.replicate (Capacity.value q) true:=(nat_other A nat 11 (by decide)).trans a11
  have b41 : B 41=frame (natWord q):=(install_slot natSlots nat_inj A nat 20).trans n20
  have blank (i : Fin 47) (hi : 43 ≤ i.val) : B i=[] :=
    (nat_other A nat i (Or.inr hi)).trans (cap_other q cap i (by omega))
  let D:=install eraseSlots B (erased q)
  have hD:=(erase_ready q).focus eraseSlots erase_inj B (by
    intro i;fin_cases i
    · exact blank 43 (by decide)
    · exact b11
    · exact blank 44 (by decide))
  have d0 : D 0=UWalkUnary.source (q+2) q:=(install_other eraseSlots B (erased q) 0 (by decide)).trans b0
  have d45 : D 45=[]:=(install_other eraseSlots B (erased q) 45 (by decide)).trans (blank 45 (by decide))
  have d46 : D 46=[]:=(install_other eraseSlots B (erased q) 46 (by decide)).trans (blank 46 (by decide))
  let E:=install copySlots D (UWalkUnary.result true false (q+2) q)
  have hE:=(UWalkUnary.ready true false (q+2) q).focus copySlots copy_inj D (by
    intro i;fin_cases i
    · exact d0
    · exact d45
    · exact d46)
  refine ⟨E,ClockJoin.join _ _ _ _ _ _ _ hA (ClockJoin.join _ _ _ _ _ _ _ hB (ClockJoin.join _ _ _ _ _ _ _ hD hE)),?_,?_,?_,?_,?_⟩
  · exact install_slot copySlots copy_inj D _ 0
  · exact (install_other copySlots D _ 41 (by decide)).trans
      ((install_other eraseSlots B _ 41 (by decide)).trans b41)
  · exact (install_other copySlots D _ 43 (by decide)).trans (install_slot eraseSlots erase_inj B _ 0)
  · have h:=install_slot copySlots copy_inj D (UWalkUnary.result true false (q+2) q) 1
    simpa [E,copySlots,UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,CompareMachine.word] using h
  · exact (install_other copySlots D _ 11 (by decide)).trans (install_slot eraseSlots erase_inj B _ 1)

end
end SourceAssemblyParityPrep
