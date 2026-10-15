import Proof.Hierarchy.CompetitorCountTableLayout

/-! Transport an executed bank program beside retained Q/parity metadata,
then pay the one physical transition positioning the U driver. The original
machine is abstract here to avoid unfolding its composed state space. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawHeads (p : Program) (pos : ℕ) (i : Fin (tapes p)) := if i.val=93 then pos else 0
def uSlot (p : Program) := old p (CompetitorCountBanks.field p 44)
def prefixOf {s : ℕ} (p : Program) (firstMachine : Machine (CompetitorCountBanks.tapes p) s) :=
  Composition.machine (TapeEmbedding.machine 124 firstMachine) (moveMachine (uSlot p))

theorem embedded_heads (p : Program) (pos : ℕ) :
    Fin.addCases (m := CompetitorCountBanks.tapes p) (n := 124)
      (motive := fun _ => ℕ) (CompetitorCountBanks.heads p pos) (fun _ => 0)=rawHeads p pos := by
  funext i
  refine Fin.addCases (m := CompetitorCountBanks.tapes p) (n := 124) ?_ ?_ i <;> intro j
  · simp only [Fin.addCases_left]
    rfl
  · simp only [Fin.addCases_right,rawHeads,Fin.val_natAdd]
    have ht : 692 ≤ CompetitorCountBanks.tapes p := by
      unfold CompetitorCountBanks.tapes CompetitorCrossScheduler.tapes
      omega
    rw [if_neg (by omega)]

theorem moved_heads (p : Program) (pos : ℕ) :
    (fun i => if i=uSlot p then rawHeads p pos i+1 else rawHeads p pos i)=heads p pos := by
  funext i
  have hi : i=uSlot p ↔ i.val=44 := Fin.ext_iff
  simp only [hi,rawHeads,heads]
  split_ifs <;> omega

theorem prefix_dock {s : ℕ} (p : Program)
    (firstMachine : Machine (CompetitorCountBanks.tapes p) s) (fuel : ℕ)
    (r : MatrixScoreBatch.Request) (q : ℕ) (odd : Bool)
    (base : ExecutionReceipt (CompetitorCountBanks.tapes p) s)
    (hr : run firstMachine fuel (CompetitorCountBanks.input p r)=some base)
    (hh : base.final.heads=CompetitorCountBanks.heads p (MatrixScoreBatch.output r).length) :
    ∃ actual,run (prefixOf p firstMachine) (fuel+2) (input p r q odd)=some actual ∧
      actual.steps=base.steps+2 ∧ actual.final.heads=heads p (MatrixScoreBatch.output r).length ∧
      actual.final.tapes=extend p q odd base.final.tapes := by
  let first : ExecutionReceipt (tapes p) s :=
    TapeEmbedding.receipt (fun _ : Fin 124 => 0) (metadata q odd) base
  have hf := TapeEmbedding.run_embed firstMachine (fun _ : Fin 124 => 0) (metadata q odd)
    fuel (initialConfiguration firstMachine (CompetitorCountBanks.input p r)) base hr
  have hi : TapeEmbedding.config (fun _ : Fin 124 => 0) (metadata q odd)
      (initialConfiguration firstMachine (CompetitorCountBanks.input p r))=
      initialConfiguration (TapeEmbedding.machine 124 firstMachine) (input p r q odd) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := CompetitorCountBanks.tapes p) (n := 124) ?_ ?_ i <;> intro j
      · simp only [TapeEmbedding.config,Fin.addCases_left];rfl
      · simp only [TapeEmbedding.config,Fin.addCases_right];rfl
    · rfl
  rw [hi] at hf
  have fh : first.final.heads=rawHeads p (MatrixScoreBatch.output r).length := by
    change (Fin.addCases (motive := fun _ => ℕ) base.final.heads (fun _ : Fin 124 => 0))=_
    rw [hh,embedded_heads]
  obtain ⟨last,hl,lh,lt,ls⟩ := move_run (uSlot p) (rawHeads p (MatrixScoreBatch.output r).length)
    (extend p q odd base.final.tapes)
  have hl' : runFrom (moveMachine (uSlot p)) 1
      (Composition.restart first.final (moveMachine (uSlot p)).start)=some last := by
    have he : Composition.restart first.final (moveMachine (uSlot p)).start=
        (⟨0,rawHeads p (MatrixScoreBatch.output r).length,extend p q odd base.final.tapes⟩ :
          Configuration (tapes p) 2) := by
      apply configuration_ext
      · rfl
      · exact fh
      · rfl
    rw [he]
    exact hl
  have hj := Composition.run_join (TapeEmbedding.machine 124 firstMachine) (moveMachine (uSlot p))
    fuel 1 _ first last hf hl'
  refine ⟨Composition.joinedReceipt first last,?_,?_,?_,lt⟩
  · have hn : fuel+1+1=fuel+2 := by omega
    rw [hn] at hj
    exact hj
  · change base.steps+1+last.steps=base.steps+2
    omega
  · change last.final.heads=_
    rw [lh,moved_heads]

end NearCubicWires.RepairOrdinary.CompetitorCountTable
