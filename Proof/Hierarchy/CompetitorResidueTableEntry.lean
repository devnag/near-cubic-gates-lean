import Proof.Hierarchy.CompetitorResidueTablePrepare

/-! Whole cold table execution with paid dimension preparation, physical
n-driver entry and one final rewind of source, output and retained drivers. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
open CompetitorPlaneStream (Cell oldWords)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def enter : Machine 46 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=27 then .right else .stay⟩ else none
def loopHeads : Fin 46 → ℕ := fun i => if i=27 then 1 else 0
noncomputable def wideLoopProgram := TapeEmbedding.machine 18 loopProgram
noncomputable def runProgram := Composition.machine coldPrepareProgram (Composition.machine enter wideLoopProgram)
def runBudget (w q n : ℕ) := coldPrepareBudget w+loopBudget w q n+3

theorem enter_run (tapes : Fin 46 → List Bool) :
    ∃ r,run enter 1 tapes=some r ∧ r.final=⟨1,loopHeads,tapes⟩ ∧ r.steps=1 := by
  have hstep : step enter (initialConfiguration enter tapes)=some (⟨1,loopHeads,tapes⟩ : Configuration 46 2) := by
    simp [step,enter,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=27 <;> simp [applyAction,loopHeads,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hstep).run (by rfl)

theorem cold_run (w q : ℕ) (xs : List Cell) (suffix : List Bool)
    (hq : q≤w) (hv : ∀ a∈xs,Valid w a) :
    ∃ r,run runProgram (runBudget w q xs.length)
      (input w q xs.length (oldWords w xs++suffix))=some r ∧
      r.steps≤runBudget w q xs.length ∧
      r.final.tapes 8=residueWords w q xs ∧ r.final.tapes 19=oldWords w xs++suffix ∧
      r.final.tapes 9=List.replicate w true ∧ r.final.tapes 4=List.replicate q true ∧
      r.final.tapes 27=CompareMachine.word xs.length := by
  obtain ⟨prepared,hprepare,hstore,hcount⟩ := cold_prepare_run w q xs.length (oldWords w xs++suffix)
  obtain ⟨first,hfirst,hft,hfh,hfs⟩ := hprepare
  obtain ⟨start,hstart,hstartf,hstarts⟩ := enter_run prepared
  obtain ⟨base,out,hbase,hbs,hbf,hout⟩ := loop_run w q xs suffix (prepared ∘ bodySlots) hq hv hstore
  let extra : Fin 18 → List Bool := fun i => prepared (i.natAdd 28)
  have hloop := TapeEmbedding.run_embed loopProgram (fun _ : Fin 18 => 0) extra _ _ base hbase
  have hin : TapeEmbedding.config (fun _ : Fin 18 => 0) extra
      (RepeatMachine.cfg 0 (cfg bodyProgram.start 0 0 (prepared ∘ bodySlots)) xs.length 1)=
      RecoveryCalls.restarted wideLoopProgram loopHeads prepared := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      refine Fin.addCases (m := 28) (n := 18) ?_ ?_ i
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
  let loop := TapeEmbedding.receipt (fun _ : Fin 18 => 0) extra base
  have hstartLoop : Composition.restart start.final wideLoopProgram.start=
      RecoveryCalls.restarted wideLoopProgram loopHeads prepared := by rw [hstartf]; rfl
  have hl' : runFrom wideLoopProgram (loopBudget w q xs.length)
      (Composition.restart start.final wideLoopProgram.start)=some loop := by
    rw [hstartLoop]
    exact hloop
  have htail := Composition.run_join enter wideLoopProgram _ _ _ start loop hstart hl'
  have hprepareTail : Composition.restart first.final (Composition.machine enter wideLoopProgram).start=
      Composition.leftConfig _ (initialConfiguration enter prepared) := by
    apply configuration_ext
    · rfl
    · funext i
      exact hfh i
    · exact hft
  have ht' : runFrom (Composition.machine enter wideLoopProgram) (1+1+loopBudget w q xs.length)
      (Composition.restart first.final (Composition.machine enter wideLoopProgram).start)=
      some (Composition.joinedReceipt start loop) := by rw [hprepareTail]; exact htail
  have hall := Composition.run_join coldPrepareProgram (Composition.machine enter wideLoopProgram)
    _ _ _ first (Composition.joinedReceipt start loop) hfirst ht'
  have htime : coldPrepareBudget w+1+(1+1+loopBudget w q xs.length)=runBudget w q xs.length := by
    unfold runBudget
    omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first (Composition.joinedReceipt start loop),hall,?_,?_,?_,?_,?_,?_⟩
  · change first.steps+1+(start.steps+1+base.steps)≤runBudget w q xs.length
    omega
  · change base.final.tapes 8=residueWords w q xs
    rw [hbf]
    exact hout.output
  · change base.final.tapes 19=oldWords w xs++suffix
    rw [hbf]
    exact hout.source
  · change base.final.tapes 9=List.replicate w true
    rw [hbf]
    exact hout.width
  · change base.final.tapes 4=List.replicate q true
    rw [hbf]
    exact hout.crop
  · change base.final.tapes 27=CompareMachine.word xs.length
    rw [hbf]
    rfl

noncomputable def machine := Rewind.machine runProgram
def readyInput (w q n : ℕ) (source : List Bool) : Fin 47 → List Bool :=
  Fin.addCases (m := 46) (n := 1) (motive := fun _ => List Bool) (input w q n source) (fun _ => [])
def budget (w q n : ℕ) := 2*runBudget w q n+2

theorem ready_run (w q : ℕ) (xs : List Cell) (suffix : List Bool)
    (hq : q≤w) (hv : ∀ a∈xs,Valid w a) :
    ∃ out,ClockJoin.ReadyRun machine (budget w q xs.length)
      (readyInput w q xs.length (oldWords w xs++suffix)) out ∧
      out 8=residueWords w q xs ∧ out 19=oldWords w xs++suffix ∧
      out 9=List.replicate w true ∧ out 4=List.replicate q true ∧
      out 27=CompareMachine.word xs.length := by
  obtain ⟨base,hr,hs,h8,h19,h9,h4,h27⟩ := cold_run w q xs suffix hq hv
  obtain ⟨r,hrun,hrt,hrh,hrs,_⟩ := Rewind.reset_run runProgram _ _ base hr
  have hc : 2*base.steps+2≤budget w q xs.length := by unfold budget; omega
  have hmore := runFrom_moreFuel machine _ (budget w q xs.length-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hc] at hmore
  refine ⟨r.final.tapes,⟨r,hmore,rfl,hrh,by omega⟩,
    (hrt 8).trans h8,(hrt 19).trans h19,(hrt 9).trans h9,(hrt 4).trans h4,(hrt 27).trans h27⟩

theorem budget_bound (w q n : ℕ) (hq : q≤w) : budget w q n≤120000*(n+1)*(w+1)^2 := by
  have hd := CompetitorDimensions.budget_bound w
  have hb := body_budget_bound w q hq
  have hm := Nat.mul_le_mul_left n hb
  unfold budget runBudget coldPrepareBudget loopBudget capacity CompetitorReusableDecision.capacity at *
  have hu : 1≤(w+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left n hu
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorResidueTable
