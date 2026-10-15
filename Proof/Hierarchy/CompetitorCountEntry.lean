import Proof.Hierarchy.CompetitorCountFold

/-! Cold arithmetic reset workspace and a paid entry-head move for the raw
count fold. The matrix/count/width words and zero accumulator are literal
inputs; the enclosing producer next supplies the accumulator by a real run. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountEntry
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroStore : CompetitorCountAccumulator.Store := ⟨0,[],[]⟩
def input (b w : ℕ) (xs : List ℕ) : Fin 9 → List Bool :=
  fun i => match i.val with
    | 0 => CompetitorCountFold.raw b xs
    | 1 => List.replicate b true
    | 2 => List.replicate w true
    | 4 => List.replicate (2*w+1) false
    | 5 => frame (binary w 0)
    | 8 => CompareMachine.word xs.length
    | _ => []
def loopHeads : Fin 9 → ℕ := fun i => if i.val=8 then 1 else 0
def caps (w : ℕ) : Fin 9 → ℕ := fun i => if i.val=7 then 4*w+3 else 0
noncomputable def loopStart (b w : ℕ) (xs : List ℕ) : Configuration 9 (Fintype.card (RepeatMachine.Control 17)) :=
  ⟨CompetitorCountFold.machine.start,loopHeads,input b w xs⟩

theorem loop_run (b w : ℕ) (xs : List ℕ) (hw : b≤w)
    (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^w) :
    ∃ r : ExecutionReceipt 9 (Fintype.card (RepeatMachine.Control 17)),
      runFrom CompetitorCountFold.machine (xs.length*(16*w+20)+3) (loopStart b w xs)=some r ∧
      r.final.tapes 5=frame (binary w xs.sum) ∧
      r.final.tapes 0=CompetitorCountFold.raw b xs ∧
      r.steps=xs.length*(16*w+20)+3 := by
  obtain ⟨base,hr,hf,hs,_⟩ := CompetitorCountFold.count_fold_run [] [] b w zeroStore xs hw hx
    (by simpa [zeroStore] using hfit) (by simp [zeroStore]) (by simp [zeroStore])
  have hi : ZeroPadding.config (caps w) (loopStart b w xs)=
      RepeatMachine.cfg 0 (CompetitorCountAccumulator.cfg CompetitorCountAccumulator.machine.start zeroStore b w
        ([]++CompetitorCountFold.raw b xs++[]) 0) xs.length 1 := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,caps,loopStart,input,zeroStore,
        RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases,
        CompetitorCountAccumulator.cfg,CompetitorCountAccumulator.Store.tapes,ZeroPadding.pad]
  have hr' : runFrom CompetitorCountFold.machine (xs.length*(16*w+20)+3)
      (ZeroPadding.config (caps w) (loopStart b w xs))=some base := by
    rw [hi]
    exact hr
  obtain ⟨r,hrr,hrf,hrs,_⟩ := ZeroPadding.run_unpad CompetitorCountFold.machine (caps w) _ _ base hr'
  have hbase5 : base.final.tapes 5=frame (binary w xs.sum) := by
    rw [hf]
    change frame (binary w (CompetitorCountFold.folded w zeroStore xs).accumulator)=_
    rw [CompetitorCountFold.accumulator_folded]
    simp [zeroStore]
  have hbase0 : base.final.tapes 0=CompetitorCountFold.raw b xs := by
    rw [hf]
    change []++CompetitorCountFold.raw b xs++[]=CompetitorCountFold.raw b xs
    simp
  have h5 := congrArg (fun c : Configuration 9 (Fintype.card (RepeatMachine.Control 17)) => c.tapes 5) hrf
  have h0 := congrArg (fun c : Configuration 9 (Fintype.card (RepeatMachine.Control 17)) => c.tapes 0) hrf
  have h5' : r.final.tapes 5=base.final.tapes 5 := by simpa [ZeroPadding.config,caps,ZeroPadding.pad] using h5
  have h0' : r.final.tapes 0=base.final.tapes 0 := by simpa [ZeroPadding.config,caps,ZeroPadding.pad] using h0
  refine ⟨r,hrr,?_,?_,hrs.trans hs⟩
  · exact h5'.trans hbase5
  · exact h0'.trans hbase0

def enter : Machine 9 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i.val=8 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine enter CompetitorCountFold.machine

theorem enter_run (tapes : Fin 9 → List Bool) :
    ∃ r : ExecutionReceipt 9 2,run enter 1 tapes=some r ∧
      r.final=⟨1,loopHeads,tapes⟩ ∧ r.steps=1 := by
  have hstep : step enter (initialConfiguration enter tapes)=some (⟨1,loopHeads,tapes⟩ : Configuration 9 2) := by
    simp [step,enter,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  exact (Timed.single (by rfl) hstep).run (by rfl)

theorem entry_run (b w : ℕ) (xs : List ℕ) (hw : b≤w)
    (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^w) :
    ∃ r : ExecutionReceipt 9 (2+Fintype.card (RepeatMachine.Control 17)),
      run machine (xs.length*(16*w+20)+5) (input b w xs)=some r ∧
      r.final.tapes 5=frame (binary w xs.sum) ∧
      r.final.tapes 0=CompetitorCountFold.raw b xs ∧
      r.steps=xs.length*(16*w+20)+5 := by
  obtain ⟨start,hr,hf,hs⟩ := enter_run (input b w xs)
  obtain ⟨loop,hl,hl5,hl0,hls⟩ := loop_run b w xs hw hx hfit
  have he : Composition.restart start.final CompetitorCountFold.machine.start=loopStart b w xs := by
    rw [hf]
    rfl
  have hl' : runFrom CompetitorCountFold.machine (xs.length*(16*w+20)+3)
      (Composition.restart start.final CompetitorCountFold.machine.start)=some loop := by
    rw [he]
    exact hl
  have hall := Composition.run_join enter CompetitorCountFold.machine 1 (xs.length*(16*w+20)+3)
    _ start loop hr hl'
  have ht : 1+1+(xs.length*(16*w+20)+3)=xs.length*(16*w+20)+5 := by omega
  rw [ht] at hall
  refine ⟨Composition.joinedReceipt start loop,hall,hl5,hl0,?_⟩
  change start.steps+1+loop.steps=xs.length*(16*w+20)+5
  omega

end NearCubicWires.RepairOrdinary.CompetitorCountEntry
