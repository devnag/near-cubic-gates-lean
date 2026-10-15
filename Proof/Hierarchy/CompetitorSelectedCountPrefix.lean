import Proof.Hierarchy.CompetitorCountProducerTemplate

/-! Execute the physical selector scan beside raw scalar widths, then move
the retained cell-count driver left once for the cold SUM entry. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedCount
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (b w : ℕ) : Fin 9 → List Bool :=
  ![List.replicate b true,List.replicate w true,[],[],[],[],[],[],[]]
noncomputable def data (b w : ℕ) (xs : List (Bool × ℕ)) : Fin 20 → List Bool :=
  Fin.addCases (m := 11) (n := 9) (motive := fun _ => List Bool)
    (CompetitorCountMask.input b xs).tapes (extra b w)
noncomputable def initialHeads (b : ℕ) (xs : List (Bool × ℕ)) : Fin 20 → ℕ :=
  Fin.addCases (m := 11) (n := 9) (motive := fun _ => ℕ) (CompetitorCountMask.input b xs).heads (fun _ => 0)
def scanHeads (n : ℕ) : Fin 20 → ℕ :=
  Fin.addCases (m := 11) (n := 9) (motive := fun _ => ℕ) (CompetitorCountMask.heads n) (fun _ => 0)
def heads (n : ℕ) : Fin 20 → ℕ := Function.update (scanHeads n) 3 0
def move : Machine 20 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,fun i => if i=3 then .left else .stay⟩ else none
noncomputable def scan := TapeEmbedding.machine 9 CompetitorCountMask.machine
noncomputable def prefixMachine := Composition.machine scan move
noncomputable def input (b w : ℕ) (xs : List (Bool × ℕ)) :=
  RecoveryCalls.restarted prefixMachine (initialHeads b xs) (data b w xs)
def prefixBudget (b n : ℕ) := CompetitorCountMask.budget b n+2
def sumSlots : Fin 11 → Fin 20 := ![9,11,12,13,14,15,16,17,3,18,19]

theorem move_run (n : ℕ) (a : Fin 20 → List Bool) :
    ∃ r,runFrom move 1 ⟨0,scanHeads n,a⟩=some r ∧ r.final=⟨1,heads n,a⟩ ∧ r.steps=1 := by
  have he : step move ⟨0,scanHeads n,a⟩=some ⟨1,heads n,a⟩ := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [applyAction,scanHeads,heads,CompetitorCountMask.heads,HeadMove.apply,Fin.addCases]
    · rfl
  exact (Timed.single (by rfl) he).run (by rfl)

theorem prefix_run (b w : ℕ) (xs : List (Bool × ℕ)) : ∃ r,
    runFrom prefixMachine (prefixBudget b xs.length) (input b w xs)=some r ∧ r.steps≤prefixBudget b xs.length ∧
    r.final.heads=heads xs.length ∧
    (∀ i,r.final.tapes (sumSlots i)=CompetitorCountProducer.templateInput b w (CompetitorCountMask.selected xs) i) ∧
    r.final.tapes 1=CompetitorCountMask.mask xs ∧
    r.final.tapes 8=CompetitorCountFold.raw b (CompetitorCountMask.counts xs) := by
  obtain ⟨base,hb,bs,bh,b9,b8,b1,_,b3⟩ := CompetitorCountMask.native_run b xs
  have hf := TapeEmbedding.run_embed CompetitorCountMask.machine (fun _ : Fin 9 => 0) (extra b w) _ _ base hb
  let first := TapeEmbedding.receipt (fun _ : Fin 9 => 0) (extra b w) base
  have fh : first.final.heads=scanHeads xs.length := by
    simp only [first,TapeEmbedding.receipt,TapeEmbedding.config,bh,scanHeads]
  obtain ⟨last,hl,lf,ls⟩ := move_run xs.length first.final.tapes
  have he : Composition.restart first.final move.start=(⟨0,scanHeads xs.length,first.final.tapes⟩ : Configuration 20 2) := by
    apply configuration_ext
    · rfl
    · exact fh
    · rfl
  have hl' : runFrom move 1 (Composition.restart first.final move.start)=some last := by rw [he];exact hl
  have hj := Composition.run_join scan move _ 1 _ first last hf hl'
  have hentry : Composition.leftConfig 2 (TapeEmbedding.config (fun _ : Fin 9 => 0) (extra b w)
      (CompetitorCountMask.input b xs))=input b w xs := by
    apply configuration_ext <;> rfl
  rw [hentry] at hj
  have hbudget : CompetitorCountMask.budget b xs.length+1+1=prefixBudget b xs.length := by unfold prefixBudget;omega
  rw [hbudget] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_,?_,?_,?_⟩
  · change base.steps+1+last.steps≤prefixBudget b xs.length
    unfold prefixBudget
    omega
  · change last.final.heads=_
    rw [lf]
  · intro i
    change last.final.tapes (sumSlots i)=_
    rw [lf]
    fin_cases i
    · exact b9
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · change base.final.tapes 3=UnaryTemplate.tape (CompetitorCountMask.selected xs).length
      rw [CompetitorCountMask.selected_length]
      exact b3
    · rfl
    · rfl
  · change last.final.tapes 1=_
    rw [lf]
    exact b1
  · change last.final.tapes 8=_
    rw [lf]
    exact b8

end NearCubicWires.RepairOrdinary.CompetitorSelectedCount
