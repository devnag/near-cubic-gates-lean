import Proof.Hierarchy.CompetitorMonomialColdClear

/-! Whole bulk monomial producer from blank work tapes and physical record,
width/capacity/count inputs. One paid outer rewind resets both global
cursors only after the entire stream has been emitted. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding CompetitorMonomialStream CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outerSlots (j : Fin 88) : Fin 89 := j.castAdd 1
def extendTapes (tapes : Fin 88 → List Bool) (n : ℕ) : Fin 89 → List Bool :=
  Fin.addCases (m := 88) (n := 1) (motive := fun _ => List Bool) tapes (fun _ => CompareMachine.word n)
def input (b t : ℕ) (xs : List Entry) := extendTapes (coldInput b t (words b xs)) xs.length
noncomputable def bootProgram := RecoveryFocus.machine outerSlots (clearProgram workSlot)
def loopHeads : Fin 89 → ℕ := fun i => if i.val=88 then 1 else 0
def enter : Machine 89 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i.val=88 then .right else .stay⟩ else none
noncomputable def tailProgram := Composition.machine enter loopProgram
noncomputable def program := Composition.machine bootProgram tailProgram
def budget (t n : ℕ) := loopBudget t n+2*capacity t+7

theorem outer_injective : Function.Injective outerSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 89 => a.val) h)

theorem boot_run (b t : ℕ) (xs : List Entry) :
    ClockJoin.ReadyRun bootProgram (2*capacity t+4) (input b t xs)
      (extendTapes (zeroed b t (words b xs)) xs.length) := by
  have hin : ∀ j,input b t xs (outerSlots j)=coldInput b t (words b xs) j := by simp [input,extendTapes,outerSlots]
  have hf := CompetitorRationalProducts.bounded_focus outerSlots outer_injective _ _ _ (cold_clear_run b t (words b xs)) (input b t xs) hin
  have he : install outerSlots (input b t xs) (zeroed b t (words b xs))=
      extendTapes (zeroed b t (words b xs)) xs.length := by
    funext i
    refine Fin.addCases (m := 88) (n := 1) ?_ ?_ i
    · intro j
      simp only [extendTapes,Fin.addCases_left]
      change install outerSlots _ _ (outerSlots j)=_
      exact install_slot outerSlots outer_injective _ _ j
    · intro j
      fin_cases j
      apply install_other
      intro k hk
      have hv := congrArg Fin.val hk
      change k.val=88 at hv
      omega
  rw [he] at hf
  exact hf

theorem enter_run (tapes : Fin 89 → List Bool) :
    ∃ r : ExecutionReceipt 89 2,run enter 1 tapes=some r ∧ r.final=⟨1,loopHeads,tapes⟩ ∧ r.steps=1 := by
  have hstep : step enter (initialConfiguration enter tapes)=some (⟨1,loopHeads,tapes⟩ : Configuration 89 2) := by
    simp [step,enter,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i.val=88 <;> simp [applyAction,loopHeads,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hstep).run (by rfl)

theorem cold_stream_run (b t : ℕ) (xs : List Entry) (hv : ∀ a∈xs,a.Valid b)
    (htarget : width b≤t) (hn : xs.length≤t) :
    ∃ r out,run program (budget t xs.length) (input b t xs)=some r ∧ r.steps≤budget t xs.length ∧
      r.final.tapes=extendTapes out xs.length ∧ Store b t (words b xs) (termWords t xs) out ∧
      (∀ a∈contributions xs,a.Valid (width b)) := by
  obtain ⟨boot,hboot,hbt,hbh,hbs⟩ := boot_run b t xs
  let startTapes := zeroed b t (words b xs)
  obtain ⟨start,hstart,hstartf,hstarts⟩ := enter_run (extendTapes startTapes xs.length)
  obtain ⟨loop,out,hloop,hloops,hloopf,hout,hvalid⟩ := stream_run b t xs startTapes hv htarget hn (zeroed_store b t (words b xs))
  have heLoop : Composition.restart start.final loopProgram.start=
      RepeatMachine.cfg 0 (cfg 0 bodyProgram.start 0 startTapes) xs.length 1 := by
    rw [hstartf]
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 88) (n := 1) ?_ ?_ i
      · intro j
        have hj : j.val≠88 := by omega
        simp [Composition.restart,loopHeads,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,cfg,heads,hj]
      · intro j
        fin_cases j
        rfl
    · rfl
  have hl' : runFrom loopProgram (loopBudget t xs.length) (Composition.restart start.final loopProgram.start)=some loop := by rw [heLoop]; exact hloop
  have htail := Composition.run_join enter loopProgram _ _ _ start loop hstart hl'
  let tail := Composition.joinedReceipt start loop
  have heStart : Composition.restart boot.final tailProgram.start=
      Composition.leftConfig _ (initialConfiguration enter (extendTapes startTapes xs.length)) := by
    apply configuration_ext
    · rfl
    · funext i
      exact hbh i
    · exact hbt
  have ht' : runFrom tailProgram (1+1+loopBudget t xs.length) (Composition.restart boot.final tailProgram.start)=some tail := by rw [heStart]; exact htail
  have hall := Composition.run_join bootProgram tailProgram _ _ _ boot tail hboot ht'
  have hcost : (2*capacity t+4)+1+(1+1+loopBudget t xs.length)=budget t xs.length := by unfold budget; omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt boot tail,out,hall,?_,?_,hout,hvalid⟩
  · change boot.steps+1+(start.steps+1+loop.steps)≤budget t xs.length
    omega
  · change loop.final.tapes=extendTapes out xs.length
    rw [hloopf]
    rfl

noncomputable def machine := Rewind.machine program
def readyInput (b t : ℕ) (xs : List Entry) : Fin 90 → List Bool :=
  Fin.addCases (m := 89) (n := 1) (motive := fun _ => List Bool) (input b t xs) (fun _ => [])
def readyBudget (t n : ℕ) := 2*budget t n+2

theorem ready_stream_run (b t : ℕ) (xs : List Entry) (hv : ∀ a∈xs,a.Valid b)
    (htarget : width b≤t) (hn : xs.length≤t) :
    ∃ out,ClockJoin.ReadyRun machine (readyBudget t xs.length) (readyInput b t xs) out ∧
      out 74=termWords t xs ∧ out 83=List.replicate t true ∧ out 88=CompareMachine.word xs.length ∧
      (∀ a∈contributions xs,a.Valid (width b)) := by
  obtain ⟨base,store,hr,hs,ht,hstore,hvalid⟩ := cold_stream_run b t xs hv htarget hn
  obtain ⟨r,hrun,hrt,hrh,hrs,_⟩ := Rewind.reset_run program _ _ base hr
  have hc : 2*base.steps+2≤readyBudget t xs.length := by unfold readyBudget; omega
  have hmore := runFrom_moreFuel machine _ (readyBudget t xs.length-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hc] at hmore
  refine ⟨r.final.tapes,⟨r,hmore,rfl,hrh,by omega⟩,?_,?_,?_,hvalid⟩
  · exact (hrt 74).trans (congrFun ht 74) |>.trans hstore.output
  · exact (hrt 83).trans (congrFun ht 83) |>.trans hstore.shortWidth
  · exact (hrt 88).trans (congrFun ht 88)

end NearCubicWires.RepairOrdinary.CompetitorMonomialEntry
