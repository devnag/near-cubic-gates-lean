import SourceAdapters.Proximity.TrimHonestLoopData
import SourceAdapters.Proximity.HonestPreparedRun

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the actual prepared-input initializer supplies the
reusable row state and an empty auxiliary prefix. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
open NearCubicGates.Adapters.Joins

def preparedCursor {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (p : AcceptedSourceInput) : ℕ :=
  (natWord (preparedHonestInput V p).length ++ natWord (sourceCircuitWord p.1).length).length

theorem initial_row_state {q : ℕ} {V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q}
    {proofSize : SourceCircuit → ℕ} {honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1)}
    {p : AcceptedSourceInput} {a : DS VV MM} {C : Ctx} (h : HonestPrepared.Initialized V proofSize honest p a)
    (hn : p.1.arity < 2 ^ C.Wd) (hN : proofSize p.1 < 2 ^ C.Wd) :
    HonestRowTable.Ready C p.2.val (honest p) q (sourceCircuitWord p.1).length (preparedCursor V p) a := by
  have hquery := h.others queryStore (by decide) (by decide) (by decide)
  have htruth := h.others HonestTableCall.truthStore (by decide) (by decide) (by decide)
  have hanswer := h.others answerStore (by decide) (by decide) (by decide)
  have hrow := h.others rowStore (by decide) (by decide) (by decide)
  refine ⟨⟨h.constants, h.bound, h.truth, h.source_length, h.cursor, h.kin,
    ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, h.local_bound⟩
  · rw [hquery.1]; simp
  · rw [hquery.2]; omega
  · rw [htruth.1]; simp
  · rw [htruth.2]; exact Nat.zero_le _
  · exact ⟨h.input_ram, h.input_length, h.input_cursor.le, hn,
      h.proof_ram, h.proof_length, h.proof_cursor.le, hN⟩
  · rw [hanswer.1]; simp
  · rw [hanswer.2]; omega
  · rw [hrow.1]; simp
  · rw [hrow.2]; omega

theorem initial_auxiliary {q : ℕ} {V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q}
    {proofSize : SourceCircuit → ℕ} {honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1)}
    {p : AcceptedSourceInput} {a : DS VV MM} (h : HonestPrepared.Initialized V proofSize honest p a) :
    AuxiliaryReady (V p.1) p.2.val (finiteProofOracle (honest p)) 0 a := by
  have hk := h.others keyStore (by decide) (by decide) (by decide)
  have hv := h.others auxiliaryStore (by decide) (by decide) (by decide)
  exact AuxiliaryReady.zero _ _ _ a hk.1 hv.1 hk.2 hv.2 (h.vars auxiliaryLength (by decide))

end NearCubicGates.Adapters.Proximity.TrimHonest
