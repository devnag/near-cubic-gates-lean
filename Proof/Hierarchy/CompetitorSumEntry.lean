import Proof.Hierarchy.CompetitorSumBootstrap

/-! Whole cold ordinary signed-rational fold. Only the scalar-record stream
and its physical dimension words are supplied; all work tapes start blank
and every head starts at zero. The initialization, entry, updates, driver
exhaustion and reset are all in the stated execution budget. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding CompetitorSumFold CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outerSlots (j : Fin 94) : Fin 95 := j.castAdd 1
def extendTapes (tapes : Fin 94 → List Bool) (n : ℕ) : Fin 95 → List Bool :=
  Fin.addCases (m := 94) (n := 1) (motive := fun _ => List Bool) tapes (fun _ => CompareMachine.word n)
def input (b : ℕ) (xs : List CompetitorValidity.Estimate) := extendTapes (coldInput b (words b xs)) xs.length
noncomputable def bootProgram := RecoveryFocus.machine outerSlots bootstrapProgram
def loopHeads : Fin 95 → ℕ := fun i => if i.val=94 then 1 else 0
def enter : Machine 95 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i.val=94 then .right else .stay⟩ else none
noncomputable def tailProgram := Composition.machine enter loopProgram
noncomputable def machine := Composition.machine bootProgram tailProgram
def budget (b n : ℕ) := loopBudget b n+2*capacity b+20*b+61

theorem outer_injective : Function.Injective outerSlots := by
  intro i j h
  have hv := congrArg (fun a : Fin 95 => a.val) h
  exact Fin.ext hv

theorem boot_run (b : ℕ) (xs : List CompetitorValidity.Estimate) (hb : 1≤b) :
    ∃ out,ClockJoin.ReadyRun bootProgram (bootstrapBudget b) (input b xs) (extendTapes out xs.length) ∧
      Store b CompetitorSumWidth.zero (words b xs) out := by
  obtain ⟨out,hr,hs⟩ := bootstrap_run b (words b xs) hb
  have hin : ∀ j,input b xs (outerSlots j)=coldInput b (words b xs) j := by simp [input,extendTapes,outerSlots]
  have hf := CompetitorRationalProducts.bounded_focus outerSlots outer_injective _ _ _ hr (input b xs) hin
  have he : install outerSlots (input b xs) out=extendTapes out xs.length := by
    funext i
    refine Fin.addCases (m := 94) (n := 1) ?_ ?_ i
    · intro j
      simp only [extendTapes,Fin.addCases_left]
      change install outerSlots (input b xs) out (outerSlots j)=out j
      exact install_slot outerSlots outer_injective (input b xs) out j
    · intro j
      fin_cases j
      apply install_other
      intro k hk
      have hv := congrArg Fin.val hk
      change k.val=94 at hv
      omega
  rw [he] at hf
  exact ⟨out,hf,hs⟩

theorem enter_run (tapes : Fin 95 → List Bool) :
    ∃ r : ExecutionReceipt 95 2,run enter 1 tapes=some r ∧
      r.final=⟨1,loopHeads,tapes⟩ ∧ r.steps=1 := by
  have hstep : step enter (initialConfiguration enter tapes)=some (⟨1,loopHeads,tapes⟩ : Configuration 95 2) := by
    simp [step,enter,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i.val=94 <;> simp [applyAction,loopHeads,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hstep).run (by rfl)

theorem cold_sum_run (b : ℕ) (xs : List CompetitorValidity.Estimate) (hb : 1≤b)
    (hv : CompetitorSumWidth.Trace b CompetitorSumWidth.zero xs) :
    ∃ r out,run machine (budget b xs.length) (input b xs)=some r ∧ r.steps≤budget b xs.length ∧
      (∀ i : Fin 94,r.final.tapes (i.castAdd 1)=out i) ∧
      (∀ i : Fin 94,r.final.heads (i.castAdd 1)=heads (words b xs).length i) ∧
      Store b (folded CompetitorSumWidth.zero xs) (words b xs) out ∧
      (folded CompetitorSumWidth.zero xs).value=(xs.map CompetitorValidity.Estimate.value).sum := by
  obtain ⟨startTapes,hboot,hstore⟩ := boot_run b xs hb
  obtain ⟨boot,hbootrun,hboott,hbooth,hboots⟩ := hboot
  obtain ⟨start,hstart,hstartf,hstarts⟩ := enter_run (extendTapes startTapes xs.length)
  obtain ⟨loop,out,hloop,hloops,hloopf,hout,hvalue⟩ := sum_loop_run b CompetitorSumWidth.zero xs startTapes hv hstore
  have heLoop : Composition.restart start.final loopProgram.start=
      RepeatMachine.cfg 0 (cfg bodyProgram.start 0 startTapes) xs.length 1 := by
    rw [hstartf]
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 94) (n := 1) ?_ ?_ i
      · intro j
        have hj : j.val≠94 := by omega
        simp [Composition.restart,loopHeads,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,cfg,heads,hj]
      · intro j
        fin_cases j
        rfl
    · rfl
  have hl' : runFrom loopProgram (loopBudget b xs.length)
      (Composition.restart start.final loopProgram.start)=some loop := by rw [heLoop]; exact hloop
  have htail := Composition.run_join enter loopProgram 1 (loopBudget b xs.length) _ start loop hstart hl'
  let tail := Composition.joinedReceipt start loop
  have heStart : Composition.restart boot.final tailProgram.start=
      Composition.leftConfig _ (initialConfiguration enter (extendTapes startTapes xs.length)) := by
    apply configuration_ext
    · rfl
    · funext i
      exact hbooth i
    · exact hboott
  have ht' : runFrom tailProgram (1+1+loopBudget b xs.length)
      (Composition.restart boot.final tailProgram.start)=some tail := by rw [heStart]; exact htail
  have hall := Composition.run_join bootProgram tailProgram (bootstrapBudget b) (1+1+loopBudget b xs.length)
    _ boot tail hbootrun ht'
  have hcost : bootstrapBudget b+1+(1+1+loopBudget b xs.length)=budget b xs.length := by
    unfold bootstrapBudget budget
    omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt boot tail,out,hall,?_,?_,?_,hout,?_⟩
  · change boot.steps+1+(start.steps+1+loop.steps)≤budget b xs.length
    omega
  · intro i
    change loop.final.tapes (i.castAdd 1)=out i
    rw [hloopf]
    simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,cfg]
  · intro i
    change loop.final.heads (i.castAdd 1)=heads (words b xs).length i
    rw [hloopf]
    simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,cfg]
  · have hz : CompetitorSumWidth.zero.value=0 := by norm_num [CompetitorSumWidth.zero,CompetitorValidity.Estimate.value]
    simpa only [hz,zero_add] using hvalue

theorem uniform_cold_sum_run (k : ℕ) (xs : List CompetitorValidity.Estimate) (hv : ∀ a∈xs,a.Valid k) :
    ∃ r out,run machine (budget (CompetitorSumWidth.width xs.length k) xs.length)
        (input (CompetitorSumWidth.width xs.length k) xs)=some r ∧
      r.steps≤budget (CompetitorSumWidth.width xs.length k) xs.length ∧
      (∀ i : Fin 94,r.final.tapes (i.castAdd 1)=out i) ∧
      (∀ i : Fin 94,r.final.heads (i.castAdd 1)=heads (words (CompetitorSumWidth.width xs.length k) xs).length i) ∧
      Store (CompetitorSumWidth.width xs.length k) (folded CompetitorSumWidth.zero xs)
        (words (CompetitorSumWidth.width xs.length k) xs) out ∧
      (folded CompetitorSumWidth.zero xs).value=(xs.map CompetitorValidity.Estimate.value).sum := by
  exact cold_sum_run (CompetitorSumWidth.width xs.length k) xs
    (by unfold CompetitorSumWidth.width; nlinarith) (CompetitorSumWidth.uniform_trace k xs hv)

end NearCubicWires.RepairOrdinary.CompetitorSumEntry
