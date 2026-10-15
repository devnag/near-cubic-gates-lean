import Proof.Hierarchy.CompetitorOddRowSliceLoop
import Proof.Hierarchy.CompetitorOddRowSlicePrepare

/-! Cold odd-row selection. The only supplied fields are the original raw
source, raw Q and the retained U template. All half-row dimensions, entry
moves, row iterations and final source/output reset are executed and paid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorOddRowSlice
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loopPadding (u : ℕ) : Fin 4 → ℕ := fun i => if i=3 then u+2 else 0

theorem template_padding (u : ℕ) :
    ZeroPadding.pad (u+2) (CompareMachine.word u)=UnaryTemplate.tape u := by
  simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem template_loop_run (h : ℕ) (rows : List Row) (suffix : List Bool) (hv : ∀ row∈rows,rowValid h row) :
    ∃ r,runFrom loopProgram (loopBudget h rows.length)
      ⟨loopProgram.start,![1,0,0,1],![UnaryTemplate.tape h,sourceRows rows++suffix,[],UnaryTemplate.tape rows.length]⟩=some r ∧
      r.steps≤loopBudget h rows.length ∧
      r.final.tapes=![UnaryTemplate.tape h,sourceRows rows++suffix,selectedRows rows,UnaryTemplate.tape rows.length] := by
  obtain ⟨base,hb,hs,hf⟩ := loop_run h rows suffix hv
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_config loopProgram (loopPadding rows.length) _ _ base hb
  have hin : ZeroPadding.config (loopPadding rows.length)
      (RepeatMachine.cfg 0 (MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape h) 1
        (sourceRows rows++suffix) 0 []) rows.length 1)=
      (⟨loopProgram.start,![1,0,0,1],![UnaryTemplate.tape h,sourceRows rows++suffix,[],UnaryTemplate.tape rows.length]⟩ : Configuration 4 _) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,loopPadding,RepeatMachine.cfg,controlConfig,
        TapeEmbedding.config,MatrixRawBlock.config,Fin.addCases,template_padding]
  rw [hin] at hr
  refine ⟨r,hr,hrs.trans_le hs,?_⟩
  rw [hrf,hf]
  funext i
  fin_cases i <;> simp [ZeroPadding.config,loopPadding,RepeatMachine.cfg,controlConfig,
    TapeEmbedding.config,MatrixRawBlock.config,Fin.addCases,template_padding]

def enter : Machine 21 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=0 ∨ i=3 then .right else .stay⟩ else none
def loopHeads : Fin 21 → ℕ := fun i => if i=0 ∨ i=3 then 1 else 0
noncomputable def wideLoopProgram := TapeEmbedding.machine 17 loopProgram
noncomputable def runProgram := Composition.machine prepareProgram (Composition.machine enter wideLoopProgram)
def runBudget (u q : ℕ) := prepareBudget u q+loopBudget (halfBytes u q) u+3

theorem enter_run (tapes : Fin 21 → List Bool) :
    ∃ r,run enter 1 tapes=some r ∧ r.final=⟨1,loopHeads,tapes⟩ ∧ r.steps=1 := by
  have hstep : step enter (initialConfiguration enter tapes)=some (⟨1,loopHeads,tapes⟩ : Configuration 21 2) := by
    simp [step,enter,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=0 ∨ i=3 <;> simp [applyAction,loopHeads,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hstep).run (by rfl)

theorem cold_run (q : ℕ) (rows : List Row) (suffix : List Bool)
    (hv : ∀ row∈rows,rowValid (halfBytes rows.length q) row) :
    ∃ r,run runProgram (runBudget rows.length q)
      (input rows.length q (sourceRows rows++suffix))=some r ∧
      r.steps≤runBudget rows.length q ∧ r.final.tapes 2=selectedRows rows ∧
      r.final.tapes 1=sourceRows rows++suffix ∧ r.final.tapes 3=UnaryTemplate.tape rows.length ∧
      r.final.tapes 4=List.replicate q true := by
  obtain ⟨prepared,hprepare,h0,h1,h2,h3,h4⟩ := prepare_run rows.length q (sourceRows rows++suffix)
  obtain ⟨first,hfirst,hft,hfh,hfs⟩ := hprepare
  obtain ⟨start,hstart,hstartf,hstarts⟩ := enter_run prepared
  obtain ⟨base,hbase,hbs,hbt⟩ := template_loop_run (halfBytes rows.length q) rows suffix hv
  let extra : Fin 17 → List Bool := fun i => prepared (i.natAdd 4)
  have hloop := TapeEmbedding.run_embed loopProgram (fun _ : Fin 17 => 0) extra _ _ base hbase
  have hin : TapeEmbedding.config (fun _ : Fin 17 => 0) extra
      (⟨loopProgram.start,![1,0,0,1],![UnaryTemplate.tape (halfBytes rows.length q),sourceRows rows++suffix,[],UnaryTemplate.tape rows.length]⟩ : Configuration 4 _)=
      RecoveryCalls.restarted wideLoopProgram loopHeads prepared := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      refine Fin.addCases (m := 4) (n := 17) ?_ ?_ i
      · intro j
        simp only [TapeEmbedding.config,RecoveryCalls.restarted,Fin.addCases_left]
        fin_cases j
        · exact h0.symm
        · exact h1.symm
        · exact h2.symm
        · exact h3.symm
      · intro j
        simp only [TapeEmbedding.config,RecoveryCalls.restarted,Fin.addCases_right,extra]
  rw [hin] at hloop
  let loop := TapeEmbedding.receipt (fun _ : Fin 17 => 0) extra base
  have he : Composition.restart start.final wideLoopProgram.start=
      RecoveryCalls.restarted wideLoopProgram loopHeads prepared := by rw [hstartf]; rfl
  have hl' : runFrom wideLoopProgram (loopBudget (halfBytes rows.length q) rows.length)
      (Composition.restart start.final wideLoopProgram.start)=some loop := by rw [he]; exact hloop
  have htail := Composition.run_join enter wideLoopProgram _ _ _ start loop hstart hl'
  have he' : Composition.restart first.final (Composition.machine enter wideLoopProgram).start=
      Composition.leftConfig _ (initialConfiguration enter prepared) := by
    apply configuration_ext
    · rfl
    · funext i
      exact hfh i
    · exact hft
  have ht' : runFrom (Composition.machine enter wideLoopProgram) (1+1+loopBudget (halfBytes rows.length q) rows.length)
      (Composition.restart first.final (Composition.machine enter wideLoopProgram).start)=
      some (Composition.joinedReceipt start loop) := by rw [he']; exact htail
  have hall := Composition.run_join prepareProgram (Composition.machine enter wideLoopProgram)
    _ _ _ first (Composition.joinedReceipt start loop) hfirst ht'
  have htime : prepareBudget rows.length q+1+(1+1+loopBudget (halfBytes rows.length q) rows.length)=runBudget rows.length q := by
    unfold runBudget
    omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first (Composition.joinedReceipt start loop),hall,?_,?_,?_,?_,?_⟩
  · change first.steps+1+(start.steps+1+base.steps)≤runBudget rows.length q
    omega
  · change base.final.tapes 2=selectedRows rows
    rw [hbt]
    rfl
  · change base.final.tapes 1=sourceRows rows++suffix
    rw [hbt]
    rfl
  · change base.final.tapes 3=UnaryTemplate.tape rows.length
    rw [hbt]
    rfl
  · exact h4

noncomputable def machine := Rewind.machine runProgram
def readyInput (u q : ℕ) (source : List Bool) : Fin 22 → List Bool :=
  Fin.addCases (m := 21) (n := 1) (motive := fun _ => List Bool) (input u q source) (fun _ => [])
def budget (u q : ℕ) := 2*runBudget u q+2

theorem ready_run (q : ℕ) (rows : List Row) (suffix : List Bool)
    (hv : ∀ row∈rows,rowValid (halfBytes rows.length q) row) :
    ∃ out,ClockJoin.ReadyRun machine (budget rows.length q)
      (readyInput rows.length q (sourceRows rows++suffix)) out ∧
      out 2=selectedRows rows ∧ out 1=sourceRows rows++suffix ∧
      out 3=UnaryTemplate.tape rows.length ∧ out 4=List.replicate q true := by
  obtain ⟨base,hr,hs,h2,h1,h3,h4⟩ := cold_run q rows suffix hv
  obtain ⟨r,hrun,hrt,hrh,hrs,_⟩ := Rewind.reset_run runProgram _ _ base hr
  have hc : 2*base.steps+2≤budget rows.length q := by unfold budget; omega
  have hmore := runFrom_moreFuel machine _ (budget rows.length q-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hc] at hmore
  refine ⟨r.final.tapes,⟨r,hmore,rfl,hrh,by omega⟩,
    (hrt 2).trans h2,(hrt 1).trans h1,(hrt 3).trans h3,(hrt 4).trans h4⟩

end NearCubicWires.RepairOrdinary.CompetitorOddRowSlice
