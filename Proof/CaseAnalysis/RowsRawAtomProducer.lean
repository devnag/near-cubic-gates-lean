import Proof.CaseAnalysis.RowsRawAtomStart

/-! The whole actual source-count producer initializes its offset/count
with literal instructions, then executes the complete reusable batch.
Only the already paid bank and native count stream are input fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomProducer
open LocalBitMultitape RepairRepresentation
open CloseoutRowsRawAtomBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine CloseoutRowsRawAtomStart.machine
  CloseoutRowsRawAtomBatch.machine
def budget (C count : ℕ):=4+CloseoutRowsRawAtomBatch.budget C count
noncomputable def input (C : ℕ) (source out : List Bool):=
  Composition.leftConfig (Fintype.card (RecoveryCalls.Control CloseoutRowsRawAtomBatch.sizes))
    (⟨CloseoutRowsRawAtomStart.machine.start,
    CloseoutRowsRawAtomStart.heads out,CloseoutRowsRawAtomStart.data C source out⟩ : Configuration 17 4)

theorem producer_run (C B : ℕ) (ns : List ℕ) (out : List Bool)
    (hB : ns.sum≤B) (hc : 64*(B+2)^2≤C) :
    ∃ r,runFrom machine (budget C ns.length) (input C (countWord ns) out)=some r ∧
      r.final.heads=CloseoutRowsRawAtomReuse.heads (countWord ns).length ns.sum (out++atoms 0 ns) ∧
      r.final.tapes=CloseoutRowsRawAtomReuse.data C (countWord ns) ns.sum ns.sum (out++atoms 0 ns) ∧
      r.steps≤budget C ns.length := by
  obtain ⟨start,hs,sh,st,_⟩:=CloseoutRowsRawAtomStart.start_run C (countWord ns) out
  obtain ⟨body,hb,bf,_⟩:=batch_run C B ns out hB hc
  have entry:Composition.restart start.final CloseoutRowsRawAtomBatch.machine.start=
      CloseoutRowsRawAtomBatch.entry 0 C (countWord ns) 0 0 0 out:=by
    apply configuration_ext
    · rfl
    · exact sh
    · exact st
  rw [←entry] at hb
  have joined:=Composition.run_join CloseoutRowsRawAtomStart.machine CloseoutRowsRawAtomBatch.machine
    _ _ _ start body hs hb
  refine ⟨Composition.joinedReceipt start body,joined,?_,?_,runFrom_steps_le machine _ _ _ joined⟩
  · change body.final.heads=_
    rw [bf];rfl
  · change body.final.tapes=_
    rw [bf];rfl

theorem source_run {q : ℕ} (a : DecompositionAlgorithm)
    (occ : List (SupplierPipeline.SupportedNormalizedGate q)) (C : ℕ) (out : List Bool)
    (hc : 64*(ExtDecompositionBatch.B a occ+2)^2≤C) :
    ∃ r,runFrom machine (budget C occ.length)
      (input C (CloseoutRowsRawAtomMeaning.countWord a occ) out)=some r ∧
      r.final.heads=CloseoutRowsRawAtomReuse.heads (CloseoutRowsRawAtomMeaning.countWord a occ).length
        (ExtDecompositionBatch.B a occ) (out++atoms 0 (ExtDecompositionBatch.counts a occ)) ∧
      r.final.tapes=CloseoutRowsRawAtomReuse.data C (CloseoutRowsRawAtomMeaning.countWord a occ)
        (ExtDecompositionBatch.B a occ) (ExtDecompositionBatch.B a occ)
        (out++atoms 0 (ExtDecompositionBatch.counts a occ)) ∧
      r.steps≤budget C occ.length := by
  have total:=(ExtDecompositionBatch.B_eq_sum a occ).symm
  have h:=producer_run C (ExtDecompositionBatch.B a occ) (ExtDecompositionBatch.counts a occ) out
    total.le hc
  simpa only [ExtDecompositionBatch.counts_length,total,countWord,CloseoutRowsRawAtomMeaning.countWord] using h

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomProducer
