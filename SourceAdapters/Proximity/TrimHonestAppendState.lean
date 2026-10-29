import SourceAdapters.Proximity.TrimHonestAuxiliaryState
import SourceAdapters.Proximity.HonestRowTableData

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": auxiliary appending preserves every precondition of the
next source row, including reused row and answer buffers. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

theorem ready_after_append {n q N L cursor : ℕ} {C : Ctx} {input : BitInput n} {proof : BitInput N}
    {a b : DS VV MM} (h : HonestRowTable.Ready C input proof q L cursor a)
    (f : AppendFrame appendTemps a b) (hrc : b.rc rowStore ≤ blockVariableBound q) :
    HonestRowTable.Ready C input proof q L cursor b := by
  refine ⟨?_, h.oracle.of_append f (by decide) (by decide), ?_, ?_, ?_, hrc,
    (f.env localBound (by decide)).trans h.local_bound⟩
  · refine ⟨f.constants h.source.constants (by decide),
      (f.env QueryStep.boundReg (by decide)).trans h.source.bound_eq,
      (f.env SourceCallee.truthLengthReg (by decide)).trans h.source.truth_length,
      (f.env SourceRequests.lengthReg (by decide)).trans h.source.source_length,
      f.ip.trans h.source.input_cursor, f.kin.trans h.source.kin_nil, ?_, ?_, ?_, ?_⟩
    · rw [f.ram queryStore (by decide) (by decide)]
      exact h.source.query_length
    · rw [f.cursor queryStore (by decide) (by decide) (by decide)]
      exact h.source.query_cursor
    · rw [f.ram HonestTableCall.truthStore (by decide) (by decide)]
      exact h.source.truth_size
    · rw [f.cursor HonestTableCall.truthStore (by decide) (by decide) (by decide)]
      exact h.source.truth_cursor
  · rw [f.ram answerStore (by decide) (by decide)]
    exact h.answers_length
  · rw [f.cursor answerStore (by decide) (by decide) (by decide)]
    exact h.answers_cursor
  · rw [f.ram rowStore (by decide) (by decide)]
    exact h.row_length

theorem table_preserves_auxiliary {q N : ℕ} {V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q}
    {S : SourceCircuit} {coins : Fin (2 ^ (V S).randomBits)} {C : Ctx}
    {input : BitInput S.arity} {proof : BitInput N} {cursor : ℕ} {a b : DS VV MM}
    (h : AuxiliaryReady (V S) input (finiteProofOracle proof) coins.val a)
    (r : HonestRowTable.Result V S coins C input proof cursor a b) :
    AuxiliaryReady (V S) input (finiteProofOracle proof) coins.val b :=
  h.preserved (r.other_store keyStore (by decide)) (r.other_store auxiliaryStore (by decide))
    (r.other_cursor keyStore (by decide)) (r.other_cursor auxiliaryStore (by decide))
    (r.vars auxiliaryLength (by decide))

end NearCubicGates.Adapters.Proximity.TrimHonest
