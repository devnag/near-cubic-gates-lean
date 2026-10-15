import Proof.Hierarchy.CompetitorBankMergeLoop
import Proof.Hierarchy.CompetitorBankMergePrepare

/-! Whole cold merge: actual dimensions, n-driver entry, streaming aligned
P/N additions, and one final source/output rewind. -/
namespace NearCubicWires.RepairOrdinary.CompetitorBankMerge
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def enter : Machine 47 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=27 then .right else .stay⟩ else none
def loopHeads : Fin 47 → ℕ := fun i => if i=27 then 1 else 0
noncomputable def wideLoopProgram := TapeEmbedding.machine 19 loopProgram
noncomputable def runProgram := Composition.machine prepareProgram (Composition.machine enter wideLoopProgram)
def runBudget (w n : ℕ) := CompetitorResidueTable.coldPrepareBudget w+loopBudget w n+3

theorem enter_run (tapes : Fin 47 → List Bool) :
    ∃ r,run enter 1 tapes=some r ∧ r.final=⟨1,loopHeads,tapes⟩ ∧ r.steps=1 := by
  have hstep : step enter (initialConfiguration enter tapes)=some (⟨1,loopHeads,tapes⟩ : Configuration 47 2) := by
    simp [step,enter,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=27 <;> simp [applyAction,loopHeads,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hstep).run (by rfl)

theorem cold_run (w : ℕ) (xs : List Pair) (suffixA suffixB : List Bool)
    (hv : ∀ a∈xs,Valid w a.1 a.2) :
    ∃ r,run runProgram (runBudget w xs.length)
      (input w xs.length (leftWords w xs++suffixA) (rightWords w xs++suffixB))=some r ∧
      r.steps≤runBudget w xs.length ∧ r.final.tapes 8=mergedWords w xs ∧
      r.final.tapes 19=leftWords w xs++suffixA ∧ r.final.tapes 23=rightWords w xs++suffixB ∧
      r.final.tapes 9=List.replicate w true ∧ r.final.tapes 27=CompareMachine.word xs.length := by
  obtain ⟨prepared,hprepare,hstore,hcount⟩ := prepare_run w xs.length (leftWords w xs++suffixA) (rightWords w xs++suffixB)
  obtain ⟨first,hfirst,hft,hfh,hfs⟩ := hprepare
  obtain ⟨start,hstart,hstartf,hstarts⟩ := enter_run prepared
  obtain ⟨base,out,hbase,hbs,hbf,hout⟩ := loop_run w xs suffixA suffixB (prepared ∘ bodySlots) hv hstore
  let extra : Fin 19 → List Bool := fun i => prepared (i.natAdd 28)
  have hloop := TapeEmbedding.run_embed loopProgram (fun _ : Fin 19 => 0) extra _ _ base hbase
  have hin : TapeEmbedding.config (fun _ : Fin 19 => 0) extra
      (RepeatMachine.cfg 0 (cfg bodyProgram.start 0 0 0 (prepared ∘ bodySlots)) xs.length 1)=
      RecoveryCalls.restarted wideLoopProgram loopHeads prepared := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      refine Fin.addCases (m := 28) (n := 19) ?_ ?_ i
      · intro j
        refine Fin.addCases (m := 27) (n := 1) ?_ ?_ j
        · intro k
          simp only [TapeEmbedding.config,RepeatMachine.cfg,controlConfig,RecoveryCalls.restarted,
            cfg,Fin.addCases_left,Function.comp_apply,bodySlots]
          rfl
        · intro k
          fin_cases k
          change CompareMachine.word xs.length=prepared 27
          exact hcount.symm
      · intro j
        simp only [TapeEmbedding.config,RecoveryCalls.restarted,Fin.addCases_right,extra]
  rw [hin] at hloop
  let loop := TapeEmbedding.receipt (fun _ : Fin 19 => 0) extra base
  have he : Composition.restart start.final wideLoopProgram.start=
      RecoveryCalls.restarted wideLoopProgram loopHeads prepared := by rw [hstartf]; rfl
  have hl' : runFrom wideLoopProgram (loopBudget w xs.length)
      (Composition.restart start.final wideLoopProgram.start)=some loop := by rw [he]; exact hloop
  have htail := Composition.run_join enter wideLoopProgram _ _ _ start loop hstart hl'
  have he' : Composition.restart first.final (Composition.machine enter wideLoopProgram).start=
      Composition.leftConfig _ (initialConfiguration enter prepared) := by
    apply configuration_ext
    · rfl
    · funext i
      exact hfh i
    · exact hft
  have ht' : runFrom (Composition.machine enter wideLoopProgram) (1+1+loopBudget w xs.length)
      (Composition.restart first.final (Composition.machine enter wideLoopProgram).start)=
      some (Composition.joinedReceipt start loop) := by rw [he']; exact htail
  have hall := Composition.run_join prepareProgram (Composition.machine enter wideLoopProgram)
    _ _ _ first (Composition.joinedReceipt start loop) hfirst ht'
  have htime : CompetitorResidueTable.coldPrepareBudget w+1+(1+1+loopBudget w xs.length)=runBudget w xs.length := by
    unfold runBudget
    omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first (Composition.joinedReceipt start loop),hall,?_,?_,?_,?_,?_,?_⟩
  · change first.steps+1+(start.steps+1+base.steps)≤runBudget w xs.length
    omega
  · change base.final.tapes 8=mergedWords w xs
    rw [hbf]
    exact hout.output
  · change base.final.tapes 19=leftWords w xs++suffixA
    rw [hbf]
    exact hout.sourceLeft
  · change base.final.tapes 23=rightWords w xs++suffixB
    rw [hbf]
    exact hout.sourceRight
  · change base.final.tapes 9=List.replicate w true
    rw [hbf]
    exact hout.width
  · change base.final.tapes 27=CompareMachine.word xs.length
    rw [hbf]
    rfl

noncomputable def machine := Rewind.machine runProgram
def readyInput (w n : ℕ) (left right : List Bool) : Fin 48 → List Bool :=
  Fin.addCases (m := 47) (n := 1) (motive := fun _ => List Bool) (input w n left right) (fun _ => [])
def budget (w n : ℕ) := 2*runBudget w n+2

theorem ready_run (w : ℕ) (xs : List Pair) (suffixA suffixB : List Bool)
    (hv : ∀ a∈xs,Valid w a.1 a.2) :
    ∃ out,ClockJoin.ReadyRun machine (budget w xs.length)
      (readyInput w xs.length (leftWords w xs++suffixA) (rightWords w xs++suffixB)) out ∧
      out 8=mergedWords w xs ∧ out 19=leftWords w xs++suffixA ∧ out 23=rightWords w xs++suffixB ∧
      out 9=List.replicate w true ∧ out 27=CompareMachine.word xs.length := by
  obtain ⟨base,hr,hs,h8,h19,h23,h9,h27⟩ := cold_run w xs suffixA suffixB hv
  obtain ⟨r,hrun,hrt,hrh,hrs,_⟩ := Rewind.reset_run runProgram _ _ base hr
  have hc : 2*base.steps+2≤budget w xs.length := by unfold budget; omega
  have hmore := runFrom_moreFuel machine _ (budget w xs.length-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hc] at hmore
  refine ⟨r.final.tapes,⟨r,hmore,rfl,hrh,by omega⟩,
    (hrt 8).trans h8,(hrt 19).trans h19,(hrt 23).trans h23,(hrt 9).trans h9,(hrt 27).trans h27⟩

end NearCubicWires.RepairOrdinary.CompetitorBankMerge
