import SourceAdapters.Proximity.TrimHonestInitialState
import SourceAdapters.Proximity.HonestCoinSetup

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": actual source-randomness setup preserves the prepared
finite oracles, reusable work stores and initial auxiliary prefix. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

theorem ready_after_coins {q N L cursor : ℕ} {V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q}
    {S : SourceCircuit} {C : Ctx} {input : BitInput S.arity} {proof : BitInput N} {a b : DS VV MM}
    (h : HonestRowTable.Ready C input proof q L cursor a) (c : HonestCoinSetup.Ready V S a b) :
    HonestRowTable.Ready C input proof q L cursor b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, (c.vars localBound (by decide)).trans h.local_bound⟩
  · refine ⟨c.constants, (c.vars QueryStep.boundReg (by decide)).trans h.source.bound_eq,
      (c.vars SourceCallee.truthLengthReg (by decide)).trans h.source.truth_length,
      (c.vars SourceRequests.lengthReg (by decide)).trans h.source.source_length,
      c.cursor.trans h.source.input_cursor, c.kin, ?_, ?_, ?_, ?_⟩
    · rw [c.ram]; exact h.source.query_length
    · rw [c.rc]; exact h.source.query_cursor
    · rw [c.ram]; exact h.source.truth_size
    · rw [c.rc]; exact h.source.truth_cursor
  · refine ⟨?_, (c.vars inputLength (by decide)).trans h.oracle.input_len, ?_, h.oracle.input_width,
      ?_, (c.vars proofLength (by decide)).trans h.oracle.proof_len, ?_, h.oracle.proof_width⟩
    · rw [c.ram]; exact h.oracle.input_ram
    · rw [c.rc]; exact h.oracle.input_cursor
    · rw [c.ram]; exact h.oracle.proof_ram
    · rw [c.rc]; exact h.oracle.proof_cursor
  · rw [c.ram]; exact h.answers_length
  · rw [c.rc]; exact h.answers_cursor
  · rw [c.ram]; exact h.row_length
  · rw [c.rc]; exact h.row_cursor

theorem auxiliary_after_coins {q N rows : ℕ} {V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q}
    {S : SourceCircuit} {input : BitInput S.arity} {proof : BitInput N} {a b : DS VV MM}
    (h : AuxiliaryReady (V S) input (finiteProofOracle proof) rows a) (c : HonestCoinSetup.Ready V S a b) :
    AuxiliaryReady (V S) input (finiteProofOracle proof) rows b :=
  h.preserved (congrFun c.ram _) (congrFun c.ram _) (congrFun c.rc _) (congrFun c.rc _)
    (c.vars auxiliaryLength (by decide))

end NearCubicGates.Adapters.Proximity.TrimHonest
