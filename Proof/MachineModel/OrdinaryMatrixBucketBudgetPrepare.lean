import Proof.MachineModel.OrdinaryMatrixBucketDivide

namespace NearCubicWires.RepairOrdinary.MatrixBucketBudgetPrepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5 → Fin 9 := ![0,2,3,4,5]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def copy := RecoveryFocus.machine slots MatrixTemplateCopy.resetMachine
def input (C G : ℕ) : Fin 9 → List Bool := ![UnaryTemplate.tape C,UnaryTemplate.tape G,[],[],[],[],[],[],[]]
def guard : Machine 9 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then
      some ⟨1,fun _ => none,fun i => if i=1 then .right else .stay⟩
    else if q.val=1 then
      some ⟨2,fun i => if i=6 then some (bits 1) else none,fun i => if i=1 then .left else .stay⟩
    else none
def raised (i : Fin 9) : ℕ := if i=1 then 1 else 0
def guarded (G : ℕ) (tapes : Fin 9 → List Bool) (i : Fin 9) :=
  if i=6 then [decide (0<G)] else tapes i
noncomputable def machine := Composition.machine copy guard
def budget (C : ℕ) := 4*C+15

theorem guard_run (G : ℕ) (tapes : Fin 9 → List Bool)
    (h1 : tapes 1=UnaryTemplate.tape G) (h6 : tapes 6=[]) :
    ∃ actual,runFrom guard 2 (RecoveryCalls.restarted guard (fun _ => 0) tapes)=some actual ∧
      actual.final.heads=(fun _ => 0) ∧ actual.final.tapes=guarded G tapes ∧ actual.steps=2 := by
  have hb : readTapeBit (tapes 1) 1=decide (0<G) := by
    rw [h1]
    cases G with
    | zero => rfl
    | succ G => exact UnaryTemplate.tape_mark (G+1) 0 (by omega)
  have hfirst : step guard (RecoveryCalls.restarted guard (fun _ => 0) tapes)=some ⟨1,raised,tapes⟩ := by
    simp [step,guard,RecoveryCalls.restarted]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  have hlast : step guard ⟨1,raised,tapes⟩=some ⟨2,fun _ => 0,guarded G tapes⟩ := by
    have hs : (⟨1,raised,tapes⟩ : Configuration 9 3).scanned 1=decide (0<G) := hb
    simp [step,guard,hs]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      by_cases hi : i=6
      · subst i
        simp [applyAction,guarded,h6]
        rfl
      · simp [applyAction,guarded,hi]
  have path := (Timed.single (by rfl) hfirst).trans (Timed.single (by rfl) hlast)
  obtain ⟨actual,ha,hf,hs⟩ := path.run (by rfl)
  exact ⟨actual,ha,by rw [hf],by rw [hf],hs⟩

theorem prepare_run (C G : ℕ) :
    ∃ actual,run machine (budget C) (input C G)=some actual ∧
      actual.final.heads=(fun _ => 0) ∧
      actual.final.tapes 0=UnaryTemplate.tape C ∧ actual.final.tapes 1=UnaryTemplate.tape G ∧
      actual.final.tapes 2=List.replicate C true ∧ actual.final.tapes 6=[decide (0<G)] ∧
      actual.final.tapes 7=[] ∧ actual.final.tapes 8=[] ∧ actual.steps≤budget C := by
  obtain ⟨base,hb,b0,b1,_,_,bh,bs⟩ := MatrixTemplateCopy.reset_run C
  have ready : ReadyRun MatrixTemplateCopy.resetMachine (4*C+12) (MatrixTemplateCopy.resetInput C) base.final.tapes :=
    ⟨base,hb,rfl,bh,bs⟩
  obtain ⟨copied,hc,ch,ct,cs⟩ := HierarchyBinary.focused_run slots slots_injective MatrixTemplateCopy.resetMachine
    _ _ ready (fun _ => 0) (input C G) (by intro i; rfl) (by intro i; fin_cases i <;> rfl)
  have localT (i : Fin 5) : copied.final.tapes (slots i)=base.final.tapes i := by
    rw [ct]
    exact install_slot slots slots_injective _ _ i
  have otherT (i : Fin 9) (hn : RecoveryFocus.pick slots i=none) : copied.final.tapes i=input C G i := by
    rw [ct]
    simp only [install,hn]
  obtain ⟨tested,ht,th,tt,ts⟩ := guard_run G copied.final.tapes (otherT 1 (by decide)) (otherT 6 (by decide))
  have hi : RecoveryCalls.restarted guard (fun _ => 0) copied.final.tapes=Composition.restart copied.final guard.start := by
    apply configuration_ext
    · rfl
    · exact ch.symm
    · rfl
  rw [hi] at ht
  have joined := Composition.run_join copy guard _ _ _ copied tested hc ht
  refine ⟨Composition.joinedReceipt copied tested,joined,th,?_,?_,?_,?_,?_,?_,?_⟩
  · change tested.final.tapes 0=_
    rw [tt]
    exact (localT 0).trans b0
  · change tested.final.tapes 1=_
    rw [tt]
    exact otherT 1 (by decide)
  · change tested.final.tapes 2=_
    rw [tt]
    exact (localT 1).trans b1
  · change tested.final.tapes 6=_
    rw [tt]
    rfl
  · change tested.final.tapes 7=_
    rw [tt]
    exact otherT 7 (by decide)
  · change tested.final.tapes 8=_
    rw [tt]
    exact otherT 8 (by decide)
  · change copied.steps+1+tested.steps≤budget C
    rw [cs,ts]
    exact Nat.le_refl _

end NearCubicWires.RepairOrdinary.MatrixBucketBudgetPrepare
