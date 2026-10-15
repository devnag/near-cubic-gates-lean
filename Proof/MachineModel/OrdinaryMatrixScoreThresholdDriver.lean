import Proof.MachineModel.OrdinaryMatrixScoreNegativeFold

/-! The actual threshold field is applied with a physically printed true
assignment driver. Both driver moves back to zero are paid; no threshold
magnitude, sign or selected flag is inserted as an abstract instruction. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreThresholdDriver
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2 → Fin 18 := ![1,17]
theorem slots_injective : Function.Injective slots := by decide
def picked : Fin 18 → Option (Fin 2) := ![none,some 0,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 1]
theorem pick_slots (i : Fin 18) : RecoveryFocus.pick slots i=picked i := by
  fin_cases i
  all_goals first | decide | exact RecoveryFocus.pick_slot slots slots_injective 0 | exact RecoveryFocus.pick_slot slots slots_injective 1
def tapes (source driver counter : List Bool) (c w P N : ℕ) (scratch : Fin 10 → List Bool) : Fin 18 → List Bool :=
  Fin.addCases (m := 17) (n := 1) (motive := fun _ => List Bool)
    (MatrixScoreWeightClear.tapes source driver c w P N scratch) (fun _ => counter)
def heads (pos apos : ℕ) : Fin 18 → ℕ :=
  Fin.addCases (m := 17) (n := 1) (motive := fun _ => ℕ) (MatrixScoreWeightClear.heads pos apos) (fun _ => 0)
noncomputable def print := RecoveryFocus.machine slots (HierarchyFixedWord.machine [true,true])
noncomputable def call := TapeEmbedding.machine 1 MatrixScoreWeightCycle.machine
def reset : Machine 18 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q _ => if h : q.val<2 then some ⟨⟨q.val+1,by omega⟩,fun _ => none,
    fun i => if i=1 then .left else .stay⟩ else none
noncomputable def first := Composition.machine print call
noncomputable def machine := Composition.machine first reset
def budget (c p w : ℕ) := 2*c+4*p+16*w+41

theorem print_run (source : List Bool) (pos c w P N : ℕ) (scratch : Fin 10 → List Bool) :
    ∃ actual,runFrom print 6
      (RecoveryCalls.restarted print (heads pos 0) (tapes source [] [] c w P N scratch))=some actual ∧
      actual.final.heads=heads pos 0 ∧
      actual.final.tapes=tapes source [true,true] (zeros 2) c w P N scratch ∧ actual.steps=6 := by
  have ready : ReadyRun (HierarchyFixedWord.machine [true,true]) 6 (fun _ => []) ![[true,true],zeros 2] :=
    HierarchyFixedWord.word_ready [true,true]
  obtain ⟨actual,hr,hh,ht,hs⟩ := HierarchyBinary.focused_run slots slots_injective _ _ _ ready
    (heads pos 0) (tapes source [] [] c w P N scratch) (by intro i; fin_cases i <;> rfl)
    (by intro i; fin_cases i <;> rfl)
  refine ⟨actual,hr,hh,?_,hs⟩
  rw [ht]
  funext i
  fin_cases i <;> simp [Fin.addCases,install,pick_slots,picked,tapes,MatrixScoreWeightClear.tapes]

theorem reset_run (ambient : Fin 18 → List Bool) (pos : ℕ) :
    ∃ actual,runFrom reset 2 (⟨0,heads pos 2,ambient⟩ : Configuration 18 3)=some actual ∧
      actual.final=⟨2,heads pos 0,ambient⟩ ∧ actual.steps=2 := by
  have step1 : step reset (⟨0,heads pos 2,ambient⟩ : Configuration 18 3)=some ⟨1,heads pos 1,ambient⟩ := by
    simp [step,reset]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Fin.addCases,applyAction,heads,MatrixScoreWeightClear.heads,HeadMove.apply]
    · rfl
  have step2 : step reset (⟨1,heads pos 1,ambient⟩ : Configuration 18 3)=some ⟨2,heads pos 0,ambient⟩ := by
    simp [step,reset]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Fin.addCases,applyAction,heads,MatrixScoreWeightClear.heads,HeadMove.apply]
    · rfl
  exact ((Timed.single (by rfl) step1).trans (Timed.single (by rfl) step2)).run (by rfl)

theorem threshold_run (pre suffix : List Bool) (p c w P N : ℕ) (theta : ℤ)
    (scratch : Fin 10 → List Bool) (hs : ∀ i,(scratch i).length≤c)
    (habs : theta.natAbs<2^p) (hw : p≤w) (hc : 4*w+3≤c)
    (hfit : theta.natAbs+(if theta<0 then N else P)<2^w) :
    ∃ finalScratch : Fin 10 → List Bool,(∀ i,(finalScratch i).length≤c) ∧
      ∃ actual,runFrom machine (budget c p w)
        (RecoveryCalls.restarted machine (heads pre.length 0)
          (tapes (pre++frame (MatrixScoreBatch.signMagnitude p theta)++suffix) [] [] c w P N scratch))=some actual ∧
        actual.final.heads=heads (pre.length+2*p+3) 0 ∧
        actual.final.tapes=tapes (pre++frame (MatrixScoreBatch.signMagnitude p theta)++suffix) [true,true] (zeros 2) c w
          (nextPositive P theta.natAbs (decide (theta<0)) true)
          (nextNegative N theta.natAbs (decide (theta<0)) true) finalScratch ∧
        actual.steps≤budget c p w := by
  let source := pre++frame (MatrixScoreBatch.signMagnitude p theta)++suffix
  obtain ⟨printed,hp,hph,hpt,hps⟩ := print_run source pre.length c w P N scratch
  obtain ⟨finalScratch,hss,body,hb,hbh,hbt,hbs⟩ := MatrixScoreWeightCycle.cycle_run pre suffix [] []
    (SignedSortKey.binary p theta.natAbs) c w P N (decide (theta<0)) true scratch hs (by simpa using hw) hc
    (by intro _; simpa only [SignedSortKey.binary_value p theta.natAbs habs,decide_eq_true_eq] using hfit)
  have he := TapeEmbedding.run_embed MatrixScoreWeightCycle.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => zeros 2) _ _ body hb
  let expanded := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => zeros 2) body
  have hin : TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => zeros 2)
      (MatrixScoreWeightCycle.input (pre++frame (decide (theta<0)::SignedSortKey.binary p theta.natAbs)++suffix)
        ([]++[true,true]++[]) pre.length 0 c w P N scratch)=
      Composition.restart printed.final call.start := by
    apply configuration_ext
    · rfl
    · exact hph.symm
    · exact hpt.symm
  simp only [List.length_nil] at he
  rw [hin] at he
  have middle := Composition.run_join print call 6 _ _ printed expanded hp he
  have eh : expanded.final.heads=heads (pre.length+2*p+3) 2 := by
    funext i
    fin_cases i <;> simp [Fin.addCases,expanded,TapeEmbedding.receipt,TapeEmbedding.config,hbh,heads,MatrixScoreWeightClear.heads]
  have et : expanded.final.tapes=tapes source [true,true] (zeros 2) c w
      (nextPositive P theta.natAbs (decide (theta<0)) true)
      (nextNegative N theta.natAbs (decide (theta<0)) true) finalScratch := by
    funext i
    fin_cases i <;> simp [Fin.addCases,expanded,TapeEmbedding.receipt,TapeEmbedding.config,hbt,tapes,source,
      MatrixScoreBatch.signMagnitude,SignedSortKey.binary_value p theta.natAbs habs]
  obtain ⟨last,hl,hlf,hls⟩ := reset_run expanded.final.tapes (pre.length+2*p+3)
  have hr : Composition.restart (Composition.joinedReceipt printed expanded).final reset.start=
      (⟨0,heads (pre.length+2*p+3) 2,expanded.final.tapes⟩ : Configuration 18 3) := by
    apply configuration_ext
    · rfl
    · exact eh
    · rfl
  rw [← hr] at hl
  have joined := Composition.run_join first reset _ 2 _ (Composition.joinedReceipt printed expanded) last middle hl
  simp only [SignedSortKey.binary_length] at joined hbs
  have htime : (6+1+(2*c+4*p+16*w+31))+1+2=budget c p w := by unfold budget; omega
  rw [htime] at joined
  refine ⟨finalScratch,hss,Composition.joinedReceipt (Composition.joinedReceipt printed expanded) last,joined,?_,?_,?_⟩
  · change last.final.heads=_
    rw [hlf]
  · change last.final.tapes=_
    rw [hlf]
    exact et
  · change (printed.steps+1+body.steps)+1+last.steps≤_
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreThresholdDriver
