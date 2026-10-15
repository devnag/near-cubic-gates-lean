import Proof.MachineModel.OrdinaryMatrixScoreAdvance
import Proof.MachineModel.OrdinaryMatrixScoreRightCycle

/-! A remaining assignment performs the id increment and the row transform, then emits its
complete right record at `φ(id+1)`, returning the local cursors for the next iteration. The
record body runs on the 27-tape carrier; the `φ` tape is carried along untouched. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRightNext
open LocalBitMultitape SignedSortKey MatrixScorePhiLayout
open MatrixScoreWeight (zeros)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def cycle := TapeEmbedding.machine 1 MatrixScoreRightCycle.machine
noncomputable def machine := Composition.machine MatrixScoreAdvance.machine cycle
def budget (d p s c m k : ℕ) := advanceBudget d k m c+1+MatrixScoreRightCycle.budget d p s c m

theorem next_run (weights right : List ℤ) (suffix : List Bool)
    (p a s c cap m id template returnCap : ℕ) (work : Fin 12 → List Bool) (driver counter out : List Bool)
    (cols : List ℕ)
    (hlen : right.length=weights.length)
    (hf : ∀ z ∈ right,z.natAbs<2^p)
    (hw : p ≤ s+1) (hc : 4*(s+1)+5 ≤ c) (hm : 2*m ≤ c) (hcap : cap ≤ c+1)
    (hs : ∀ i,(work i).length ≤ c)
    (hrcap : returnCap ≤ MatrixScoreLeftRecord.budget weights.length p s c m)
    (ha : a<2^weights.length) (hid : id+1<2^m) (hcl : cols.length ≤ m)
    (hcols : ∀ z ∈ cols,z<2^weights.length) (hphi : weights.length+cols.length+2 ≤ c)
    (hp : MatrixScoreBatch.part false right (MatrixScorePhi.value cols (id+1))<2^s)
    (hn : MatrixScoreBatch.part true right (MatrixScorePhi.value cols (id+1))<2^s) :
    ∃ finalWork : Fin 12 → List Bool,(∀ i,(finalWork i).length ≤ c) ∧
      ∃ finalCap : ℕ,finalCap ≤ MatrixScoreLeftRecord.budget weights.length p s c m ∧
      ∃ actual,runFrom machine (budget weights.length p s c m cols.length)
        (RecoveryCalls.restarted machine (heads out.length)
          (tapes (MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++suffix)
            (frame (binary weights.length a)) weights.length c cap (s+1) (2^s) m id template work driver counter
            out returnCap cols))=some actual ∧
        actual.final.heads=heads (out++StablePartition.recordBits (encode s m
          (MatrixScoreBatch.linearForm right (MatrixScorePhi.value cols (id+1))) (id+1))).length ∧
        actual.final.tapes=tapes
          (MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++suffix)
          (frame (binary weights.length (MatrixScorePhi.value cols (id+1)))) weights.length c (c+1) (s+1) (2^s)
          m (id+1) template finalWork driver counter
          (out++StablePartition.recordBits (encode s m
            (MatrixScoreBatch.linearForm right (MatrixScorePhi.value cols (id+1))) (id+1))) finalCap cols ∧
        actual.steps ≤ budget weights.length p s c m cols.length := by
  let source := MatrixScoreCanonical.fields p weights++MatrixScoreCanonical.fields p right++suffix
  let v := MatrixScorePhi.value cols (id+1)
  obtain ⟨advanced,ha',ah,atapes,as⟩ := MatrixScoreAdvance.advance_run source weights.length a c cap (s+1) (2^s)
    m id template returnCap cols work driver counter out ha hid hcl hcols hm hphi
  obtain ⟨finalWork,hws,finalCap,hcb,finished,hf',fh,ft,fs⟩ := MatrixScoreRightCycle.cycle_run weights right suffix
    p v s c cap m (id+1) template returnCap work driver counter out hlen hf hw hc hm hcap hs hrcap hp hn
  have he := TapeEmbedding.run_embed MatrixScoreRightCycle.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => MatrixScorePhi.columnsWord weights.length cols) _ _ finished hf'
  have hi : Composition.restart advanced.final cycle.start=
      TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => MatrixScorePhi.columnsWord weights.length cols)
        (RecoveryCalls.restarted MatrixScoreRightCycle.machine (MatrixScoreLeftCycle.heads out.length)
          (MatrixScoreLeftCycle.tapes source (frame (binary weights.length v)) weights.length c cap (s+1) (2^s)
            m (id+1) template work driver counter out returnCap)) := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact atapes
  rw [← hi] at he
  have joined := Composition.run_join MatrixScoreAdvance.machine cycle _ _ _ advanced _ ha' he
  refine ⟨finalWork,hws,finalCap,hcb,Composition.joinedReceipt advanced _,joined,?_,?_,?_⟩
  · simp only [Composition.joinedReceipt,Composition.rightConfig,TapeEmbedding.receipt,TapeEmbedding.config,fh,
      heads]
    rfl
  · simp only [Composition.joinedReceipt,Composition.rightConfig,TapeEmbedding.receipt,TapeEmbedding.config,ft,
      tapes]
    rfl
  · change advanced.steps+1+finished.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreRightNext
