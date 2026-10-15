import Proof.Hierarchy.CompetitorCountTableRecord
import Proof.Hierarchy.CompetitorSelectedRequestCount

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Plan.DirectCount
open LocalBitMultitape RepairOrdinary RecoveryRootRound RecoveryExecution
open RepairRepresentation MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
open CompetitorCrossScheduler (producer)

noncomputable def first (a : WilliamsAlgorithm) :=
  TapeEmbedding.machine 92 (CompetitorCountTable.machine a)
noncomputable def last (p : Program) :=
  RecoveryFocus.machine (CompetitorSelectedTable.slot p) CompetitorSelectedRequestCount.machine
noncomputable def machine (a : WilliamsAlgorithm) := Composition.machine (first a) (last (producer a))
def input (p : Program) (r : Request) (Q : Nat) (odd : Bool) (xs : List (Bool × Nat)) :=
  CompetitorSelectedTable.extend p xs (CompetitorCountTable.input p r Q odd)
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) (Q : Nat) :=
  CompetitorCountTable.budget a r Q + 1 + CompetitorSelectedRequestCount.budget r Q

theorem run (a : WilliamsAlgorithm) (r : Request) (Q : Nat) (odd : Bool)
    (f : Fin r.U → Fin r.U → Nat) (select : Fin r.U → Fin r.U → Bool)
    (hQ : Q ≤ CompetitorSameBucketColdDense.width r)
    (he : odd = true → r.U/2+r.U/2 = r.U)
    (hf : ∀ i j, f i j < 2^Q)
    (hc : ∀ i : Fin (r.U*r.U), Int.ModEq ((2 : Int)^Q)
      (SupplierPrinter.weightedDominance (leftScore r) (rightScore r) (weight r)
        i.divNat i.modNat) (f i.divNat i.modNat)) :
    ∃ actual, LocalBitMultitape.run (machine a) (budget a r Q)
      (input (producer a) r Q odd (CompetitorSelectedCells.cells odd f select)) = some actual ∧
      actual.steps ≤ budget a r Q ∧
      (∀ i, actual.final.heads (CompetitorSelectedTable.slot (producer a) i) =
        CompetitorSelectedRequestCount.outputHeads Q (r.U*r.U) i) ∧
      actual.final.tapes (CompetitorSelectedTable.slot (producer a) 86) =
        frame (SignedSortKey.binary (scalarWidth r Q)
          (selected (CompetitorSelectedCells.cells odd f select)).sum) ∧
      actual.final.tapes (CompetitorSelectedTable.slot (producer a) 0) = physicalInput r := by
  let p := producer a
  let xs := CompetitorSelectedCells.cells odd f select
  obtain ⟨base,hbase,bs,bh,bt,bQ,_,_,b0⟩ := CompetitorCountTable.cold_run a r Q odd f hQ he
    (fun i => hf i.divNat i.modNat) hc
  let before := TapeEmbedding.receipt (fun _ : Fin 92 => 0) (CompetitorSelectedTable.extra xs) base
  have hfirst := TapeEmbedding.run_embed (CompetitorCountTable.machine a) (fun _ : Fin 92 => 0)
    (CompetitorSelectedTable.extra xs) _ _ base hbase
  have hcword : base.final.tapes (CompetitorCountTable.slot p 141) =
      CompetitorCountFold.raw Q (counts xs) :=
    bt.trans (CompetitorSelectedCells.cells_word Q odd f select).symm
  have hheads : before.final.heads = CompetitorSelectedTable.heads p (MatrixScoreBatch.output r).length := by
    change Fin.addCases (motive := fun _ => Nat) base.final.heads (fun _ : Fin 92 => 0) = _
    rw [bh]
    rfl
  have hh : ∀ i, before.final.heads (CompetitorSelectedTable.slot p i) = 0 := by
    intro i
    rw [hheads]
    exact CompetitorSelectedTable.slot_heads p _ i
  have ht : ∀ i, before.final.tapes (CompetitorSelectedTable.slot p i) =
      CompetitorSelectedRequestCount.input r Q xs i :=
    CompetitorSelectedTable.extend_slot p r Q xs base.final.tapes b0 bQ hcword
  obtain ⟨child,ch,cs,chh,ct,_cw,c0⟩ := CompetitorSelectedRequestCount.native_run r Q xs
    (CompetitorSelectedCells.cells_length odd f select)
    (CompetitorSelectedCells.cells_fit Q odd f select hf)
  obtain ⟨tail,th,_,ts,thh,tt,_⟩ := RecoveryFocus.dock
    (CompetitorSelectedTable.slot p) (CompetitorSelectedTable.slot_injective p)
    CompetitorSelectedRequestCount.machine _ before.final.heads before.final.tapes _ hh ht child ch
  have htail : runFrom (last p) (CompetitorSelectedRequestCount.budget r Q)
      (Composition.restart before.final (last p).start) = some tail := th
  have hj := Composition.run_join (first a) (last p) _ _ _ before tail hfirst htail
  have hi : Composition.leftConfig _
      (TapeEmbedding.config (fun _ : Fin 92 => 0) (CompetitorSelectedTable.extra xs)
        (initialConfiguration (CompetitorCountTable.machine a) (CompetitorCountTable.input p r Q odd))) =
      initialConfiguration (machine a) (input p r Q odd xs) := by
    apply configuration_ext
    · rfl
    · funext i
      exact Fin.addCases (motive := fun i =>
        Fin.addCases (motive := fun _ => Nat) (fun _ => 0) (fun _ : Fin 92 => 0) i = 0)
        (fun _ => by rw [Fin.addCases_left]) (fun _ => by rw [Fin.addCases_right]) i
    · rfl
  rw [hi] at hj
  refine ⟨Composition.joinedReceipt before tail,hj,?_,?_,(tt 86).trans ct,(tt 0).trans c0⟩
  · change base.steps+1+tail.steps ≤ _
    rw [ts]
    unfold budget
    omega
  · intro i
    exact (thh i).trans (congrFun chh i)

theorem rect_mask_independent {u v : Nat} (f g : Fin u → Fin v → Nat)
    (select : Fin u → Fin v → Bool) :
    mask (CompetitorSelectedCells.rect f select) = mask (CompetitorSelectedCells.rect g select) := by
  simp [mask, CompetitorSelectedCells.rect, List.map_flatten, List.map_ofFn, Function.comp_def]

theorem input_has_no_answers (a : WilliamsAlgorithm) (r : Request) (Q : Nat) (odd : Bool)
    (f g : Fin r.U → Fin r.U → Nat) (select : Fin r.U → Fin r.U → Bool) :
    input (producer a) r Q odd (CompetitorSelectedCells.cells odd f select) =
      input (producer a) r Q odd (CompetitorSelectedCells.cells odd g select) := by
  have hm : mask (CompetitorSelectedCells.cells odd f select) =
      mask (CompetitorSelectedCells.cells odd g select) := by
    cases odd <;> simp only [CompetitorSelectedCells.cells, Bool.false_eq_true, ↓reduceIte]
    all_goals exact rect_mask_independent _ _ _
  unfold input CompetitorSelectedTable.extend CompetitorSelectedTable.extra
  simp only [hm]

end NearCubicWires.P1Plan.DirectCount
