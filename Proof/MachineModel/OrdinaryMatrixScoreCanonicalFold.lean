import Proof.MachineModel.OrdinaryMatrixScoreCanonicalWeights

/-! The executed full weight fold at the literal matrix request codec,
with its actual framed binary assignment and exact signed partial sums. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreCanonical
open LocalBitMultitape SignedSortKey MatrixScoreWeightList
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (p : ℕ) (weights : List ℤ) := weights.flatMap (fun w => frame (MatrixScoreBatch.signMagnitude p w))

theorem fold_run (weights : List ℤ) (pre suffix apre asuffix : List Bool) (p n c w positive negative : ℕ)
    (scratch : Fin 10 → List Bool) (hf : ∀ z ∈ weights,z.natAbs<2^p)
    (hw : p≤w) (hc : 4*w+3≤c) (hs : ∀ i,(scratch i).length≤c)
    (hp : positive+MatrixScoreBatch.part false weights n<2^w)
    (hn : negative+MatrixScoreBatch.part true weights n<2^w) :
    ∃ finalScratch : Fin 10 → List Bool,(∀ i,(finalScratch i).length≤c) ∧
      ∃ actual,runFrom MatrixScoreWeightList.machine (weights.length*(2*c+4*p+16*w+34)+3)
        (RepeatMachine.cfg 0 (MatrixScoreWeightCycle.input (pre++fields p weights++suffix)
          (apre++frame (binary weights.length n)++asuffix) pre.length apre.length c w positive negative scratch)
          weights.length 1)=some actual ∧
        actual.final=RepeatMachine.cfg 3 (MatrixScoreWeightCycle.input (pre++fields p weights++suffix)
          (apre++frame (binary weights.length n)++asuffix) (pre.length+(fields p weights).length)
          (apre.length+2*weights.length) c w
          (positive+MatrixScoreBatch.part false weights n) (negative+MatrixScoreBatch.part true weights n)
          finalScratch) weights.length 1 ∧ actual.steps≤weights.length*(2*c+4*p+16*w+34)+3 := by
  have hp' : positive+MatrixScoreWeightList.positive (items p n weights)<2^w := by rw [positive_items p n weights hf]; exact hp
  have hn' : negative+MatrixScoreWeightList.negative (items p n weights)<2^w := by rw [negative_items p n weights hf]; exact hn
  obtain ⟨final,hfs,actual,hr,he,has⟩ := driver_run (items p n weights) pre suffix apre ([false]++asuffix)
    weights.length 0 c p w positive negative scratch (by simp) (magnitude_width p n weights) hw hc hs hp' hn'
  have hassignment : apre++assignment (items p n weights)++([false]++asuffix)=
      apre++frame (binary weights.length n)++asuffix := by
    rw [assignment_items]
    have h := Streaming.frame_append (binary weights.length n) []
    simp only [List.append_nil,frame] at h
    rw [h]
    simp only [List.append_assoc]
  have hsource : word (items p n weights)=fields p weights := word_items p n weights
  rw [hsource,hassignment,items_length,positive_items p n weights hf,negative_items p n weights hf] at he
  rw [hsource,hassignment,items_length] at hr
  rw [items_length] at has
  have htime : weights.length*(cost c p w+2)+weights.length+3=
      weights.length*(2*c+4*p+16*w+34)+3 := by unfold cost; ring
  rw [htime] at hr has
  exact ⟨final,hfs,actual,hr,he,has⟩

end NearCubicWires.RepairOrdinary.MatrixScoreCanonical
