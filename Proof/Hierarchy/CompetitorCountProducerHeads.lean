import Proof.Hierarchy.CompetitorCountEntryHeads
import Proof.Hierarchy.CompetitorCountProducer

/-! The existing exact SUM producer with its full reusable scalar endpoint:
source/count cursors are explicit and the scalar result head is zero. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountProducer
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def finalHeads (b n : ℕ) (i : Fin 11) := if i.val=0 then b*n else if i.val=8 then 1 else 0

theorem fold_head_run (b w : ℕ) (xs : List ℕ) (middle : Fin 11 → List Bool)
    (hm : ∀ i : Fin 9,middle (i.castAdd 2)=CompetitorCountEntry.input b w xs i)
    (hw : b≤w) (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^w) :
    ∃ r : ExecutionReceipt 11 (2+Fintype.card (RepeatMachine.Control 17)),
      run foldProgram (xs.length*(16*w+20)+5) middle=some r ∧
      r.final.tapes 5=frame (binary w xs.sum) ∧ r.final.tapes 0=CompetitorCountFold.raw b xs ∧
      r.steps=xs.length*(16*w+20)+5 ∧ r.final.heads=finalHeads b xs.length ∧
      r.final.tapes 1=List.replicate b true ∧ r.final.tapes 2=List.replicate w true := by
  obtain ⟨base,hr,h5,h0,hs,hh,h1,h2⟩ := CompetitorCountEntry.entry_head_run b w xs hw hx hfit
  let extra : Fin 2 → List Bool := fun i => middle (i.natAdd 9)
  have hrun := TapeEmbedding.run_embed CompetitorCountEntry.machine (fun _ : Fin 2 => 0) extra _ _ base hr
  have hi : TapeEmbedding.config (fun _ : Fin 2 => 0) extra
      (initialConfiguration CompetitorCountEntry.machine (CompetitorCountEntry.input b w xs))=
      initialConfiguration foldProgram middle := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [TapeEmbedding.config,initialConfiguration,Fin.addCases_left] using (hm j).symm
      · simp only [TapeEmbedding.config,initialConfiguration,Fin.addCases_right,extra]
  rw [hi] at hrun
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 2 => 0) extra base,hrun,h5,h0,hs,?_,h1,h2⟩
  simp only [TapeEmbedding.receipt,TapeEmbedding.config,hh]
  funext i;fin_cases i <;> rfl

theorem producer_head_run (b w : ℕ) (xs : List ℕ)
    (hw : b≤w) (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^w) :
    ∃ r : ExecutionReceipt 11 (6+(2+Fintype.card (RepeatMachine.Control 17))),
      run machine (budget w xs.length) (input b w xs)=some r ∧
      r.final.tapes 5=frame (binary w xs.sum) ∧ r.final.tapes 0=CompetitorCountFold.raw b xs ∧
      r.steps≤budget w xs.length ∧ r.final.heads=finalHeads b xs.length ∧
      r.final.tapes 1=List.replicate b true ∧ r.final.tapes 2=List.replicate w true := by
  obtain ⟨middle,hzero,hm⟩ := zero_ready b w xs
  obtain ⟨zero,hz,hzt,hzh,hzs⟩ := hzero
  obtain ⟨fold,hf,hf5,hf0,hfs,hfh,hf1,hf2⟩ := fold_head_run b w xs middle hm hw hx hfit
  have he : Composition.restart zero.final foldProgram.start=initialConfiguration foldProgram middle := by
    apply configuration_ext
    · rfl
    · exact funext hzh
    · exact hzt
  have hf' : runFrom foldProgram (xs.length*(16*w+20)+5)
      (Composition.restart zero.final foldProgram.start)=some fold := by
    rw [he]
    exact hf
  have hj := Composition.run_join zeroProgram foldProgram (4*w+4) (xs.length*(16*w+20)+5) _ zero fold hz hf'
  have ht : (4*w+4)+1+(xs.length*(16*w+20)+5)=budget w xs.length := by unfold budget;omega
  rw [ht] at hj
  refine ⟨Composition.joinedReceipt zero fold,hj,hf5,hf0,?_,hfh,hf1,hf2⟩
  change zero.steps+1+fold.steps≤budget w xs.length
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorCountProducer
