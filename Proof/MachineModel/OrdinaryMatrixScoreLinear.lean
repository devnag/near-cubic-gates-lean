import Proof.MachineModel.OrdinaryMatrixScoreFinish

/-! Complete physical shifted linear-form evaluation for one assignment.
All reusable work is cleared and initialized, all weights are read, and the
final borrow subtraction is executed in the same fixed twenty-tape carrier. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreLinear
open LocalBitMultitape SignedSortKey MatrixScoreFoldEntry
open MatrixScoreWeight (zeros scalar)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine MatrixScoreFoldEntry.machine MatrixScoreFinish.machine
def budget (d p s c : ℕ) := MatrixScoreFoldEntry.budget d c p (s+1)+1+MatrixScoreFinish.budget s c

theorem linear_run (weights : List ℤ) (pre suffix apre asuffix : List Bool) (p n s c cap : ℕ)
    (work : Fin 12 → List Bool) (hf : ∀ z ∈ weights,z.natAbs<2^p)
    (hw : p ≤ s+1) (hc : 4*(s+1)+5≤c) (hcap : cap≤c+1) (hs : ∀ i,(work i).length≤c)
    (hp : MatrixScoreBatch.part false weights n<2^s)
    (hn : MatrixScoreBatch.part true weights n<2^s) :
    ∃ finalWork : Fin 12 → List Bool,(∀ i,(finalWork i).length≤c) ∧
      finalWork 0=scalar c (s+1) (shifted s (MatrixScoreBatch.linearForm weights n)) ∧
      ∃ actual,runFrom machine (budget weights.length p s c)
        (RecoveryCalls.restarted machine (heads pre.length apre.length)
          (tapes (pre++MatrixScoreCanonical.fields p weights++suffix)
            (apre++frame (binary weights.length n)++asuffix) weights.length c cap (s+1) (2^s) 0 work))=some actual ∧
        actual.final.heads=heads (pre.length+(MatrixScoreCanonical.fields p weights).length)
          (apre.length+2*weights.length) ∧
        actual.final.tapes=tapes (pre++MatrixScoreCanonical.fields p weights++suffix)
          (apre++frame (binary weights.length n)++asuffix) weights.length c (c+1) (s+1) (2^s) 0 finalWork ∧
        actual.steps≤budget weights.length p s c := by
  have hn' : 0+MatrixScoreBatch.part true weights n<2^(s+1) := by
    simp only [Nat.zero_add]
    exact hn.trans (Nat.pow_lt_pow_right (by decide) (by omega))
  obtain ⟨scratch,hss,folded,hfRun,hfh,hft,hfs⟩ := MatrixScoreFoldEntry.entry_run weights pre suffix apre asuffix
    p n c cap (s+1) (2^s) 0 work hf hw (by omega) hcap hs (MatrixScoreShifted.offset_fit s _ hp) hn'
  simp only [Nat.zero_add] at hft
  obtain ⟨finalWork,hws,hw0,finished,hg,hgh,hgt,hgs⟩ := MatrixScoreFinish.finish_run
    (pre++MatrixScoreCanonical.fields p weights++suffix) (apre++frame (binary weights.length n)++asuffix)
    (pre.length+(MatrixScoreCanonical.fields p weights).length) (apre.length+2*weights.length)
    weights.length c s (MatrixScoreBatch.part false weights n) (MatrixScoreBatch.part true weights n)
    (2^s) 0 scratch hss hp hn hc
  have he : Composition.restart folded.final MatrixScoreFinish.machine.start=
      RecoveryCalls.restarted MatrixScoreFinish.machine
        (heads (pre.length+(MatrixScoreCanonical.fields p weights).length) (apre.length+2*weights.length))
        (tapes (pre++MatrixScoreCanonical.fields p weights++suffix) (apre++frame (binary weights.length n)++asuffix)
          weights.length c (c+1) (s+1) (2^s) 0
          (accumulators c (s+1) (2^s+MatrixScoreBatch.part false weights n)
            (MatrixScoreBatch.part true weights n) scratch)) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  rw [← he] at hg
  have joined := Composition.run_join MatrixScoreFoldEntry.machine MatrixScoreFinish.machine
    (MatrixScoreFoldEntry.budget weights.length c p (s+1)) (MatrixScoreFinish.budget s c)
    _ folded finished hfRun hg
  have hvalue : shifted s (MatrixScoreBatch.linearForm weights n)=
      shifted s ((MatrixScoreBatch.part false weights n : ℤ)-MatrixScoreBatch.part true weights n) := by
    rw [MatrixScoreBatch.linearForm_parts]
  rw [← hvalue] at hw0
  refine ⟨finalWork,hws,hw0,Composition.joinedReceipt folded finished,joined,hgh,hgt,?_⟩
  change folded.steps+1+finished.steps≤_
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixScoreLinear
