import Proof.Hierarchy.CompetitorValidityLoop

/-! Cold-workspace entry to the complete validity list. The caller supplies
the produced scalar-record stream and physical width, erase-capacity and
record-count words. All work tapes begin blank and every head begins at zero.
One physical driver move and its handoff enter the checked rejecting loop. -/
namespace NearCubicWires.RepairOrdinary.CompetitorValidityEntry
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
open CompetitorValidity CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev controlCount {t s : ℕ} (_ : Machine t s) : ℕ := s
noncomputable abbrev bodyStates := controlCount recordProgram
def input (b : ℕ) (xs : List Comparison) : Fin 72 → List Bool := fun i => match i.val with
  | 6 => List.replicate (CompetitorRationalDecision.width b) true
  | 67 => words b xs
  | 69 => List.replicate (capacity b) true
  | 71 => CompareMachine.word xs.length
  | _ => []
def loopHeads : Fin 72 → ℕ := fun i => if i.val=71 then 1 else 0
def caps (b : ℕ) : Fin 72 → ℕ := fun i => if i.val=70 then capacity b+1 else 0
noncomputable def loopStart (b : ℕ) (xs : List Comparison) :
    Configuration 72 (Fintype.card (RepeatMachine.Control bodyStates)) :=
  ⟨loopProgram.start,loopHeads,input b xs⟩

theorem cold_loop_run (b : ℕ) (xs : List Comparison) (hv : ∀ a∈xs,a.Valid b) :
    ∃ r,runFrom loopProgram (loopBudget b xs.length) (loopStart b xs)=some r ∧
      r.steps≤loopBudget b xs.length ∧
      (r.final.control=RepeatMachine.phaseCode bodyStates 3 ↔ ∀ a∈xs,a.passes) := by
  have hstore : Store b (words b xs) (data b (words b xs) (fun _ => [])) := by
    constructor
    · rfl
    · rfl
    · rfl
    · rfl
    · intro j
      have he : data b (words b xs) (fun _ => []) (scratchSlot j)=[] := by fin_cases j <;> rfl
      rw [he]
      simp
  obtain ⟨base,hr,hs,haccept⟩ := validity_loop_run b xs (data b (words b xs) (fun _ => [])) hv hstore
  have hi : ZeroPadding.config (caps b) (loopStart b xs)=
      RepeatMachine.cfg 0 (cfg recordProgram.start 0 (data b (words b xs) (fun _ => []))) xs.length 1 := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,caps,loopStart,input,
        RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases,cfg,data,ZeroPadding.pad]
  have hr' : runFrom loopProgram (loopBudget b xs.length) (ZeroPadding.config (caps b) (loopStart b xs))=some base := by
    rw [hi]
    exact hr
  obtain ⟨r,hrr,hf,hrs,_⟩ := ZeroPadding.run_unpad loopProgram (caps b) _ _ base hr'
  have hcontrol := congrArg Configuration.control hf
  change r.final.control=base.final.control at hcontrol
  exact ⟨r,hrr,hrs.trans_le hs,by rw [hcontrol]; exact haccept⟩

def enter : Machine 72 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i.val=71 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine enter loopProgram
noncomputable def success : Fin (2+Fintype.card (RepeatMachine.Control bodyStates)) :=
  (RepeatMachine.phaseCode bodyStates 3).natAdd 2
def budget (b n : ℕ) := n*(recordBudget b+3)+5

theorem enter_run (tapes : Fin 72 → List Bool) :
    ∃ r : ExecutionReceipt 72 2,run enter 1 tapes=some r ∧
      r.final=⟨1,loopHeads,tapes⟩ ∧ r.steps=1 := by
  have hstep : step enter (initialConfiguration enter tapes)=some (⟨1,loopHeads,tapes⟩ : Configuration 72 2) := by
    simp [step,enter,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i.val=71 <;> simp [applyAction,loopHeads,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hstep).run (by rfl)

theorem validity_entry_run (b : ℕ) (xs : List Comparison) (hv : ∀ a∈xs,a.Valid b) :
    ∃ r,run machine (budget b xs.length) (input b xs)=some r ∧ r.steps≤budget b xs.length ∧
      (r.final.control=success ↔ ∀ a∈xs,a.passes) := by
  obtain ⟨start,hr,hf,hs⟩ := enter_run (input b xs)
  obtain ⟨loop,hl,hls,haccept⟩ := cold_loop_run b xs hv
  have he : Composition.restart start.final loopProgram.start=loopStart b xs := by
    rw [hf]
    rfl
  have hl' : runFrom loopProgram (loopBudget b xs.length) (Composition.restart start.final loopProgram.start)=some loop := by
    rw [he]
    exact hl
  have hall := Composition.run_join enter loopProgram 1 (loopBudget b xs.length) _ start loop hr hl'
  have ht : 1+1+loopBudget b xs.length=budget b xs.length := by unfold loopBudget budget; omega
  rw [ht] at hall
  refine ⟨Composition.joinedReceipt start loop,hall,?_,?_⟩
  · change start.steps+1+loop.steps≤budget b xs.length
    omega
  · change loop.final.control.natAdd 2=(RepeatMachine.phaseCode bodyStates 3).natAdd 2 ↔ _
    have heq : loop.final.control.natAdd 2=(RepeatMachine.phaseCode bodyStates 3).natAdd 2 ↔
        loop.final.control=RepeatMachine.phaseCode bodyStates 3 := by
      constructor
      · intro he
        apply Fin.ext
        have hv := congrArg Fin.val he
        simp only [Fin.val_natAdd] at hv
        omega
      · intro he
        rw [he]
    exact heq.trans haccept

end NearCubicWires.RepairOrdinary.CompetitorValidityEntry
