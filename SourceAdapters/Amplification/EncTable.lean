import SourceAdapters.Amplification.EncProgram
import SourceAdapters.Amplification.EncPrep
import SourceAdapters.Code.Parsing
import SourceAdapters.Code.Composition
import Proof.Gates.CounterMachine.CellTablesSet

/-!
# The encoder table machine of X9, assembled (`app:sources`, "Full-range amplification interface")

`prepWF` (the width prefix, a word program) composed (`Code.composeFramed`, `app:sources`, "Uniform three-query PCPP and code interfaces") with `encWF R` (the
cell program `encP R`, compiled by `Cells.wordFunction_of_lang`): one ordinary machine from `encoderInput r` to
`encoderOutput R r`. Its budget is bounded in `EncBound.lean`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

/-- The preparation machine. -/
noncomputable def prepWF :
    WordFunction Joins.EncoderRequest Joins.encoderInput (fun r => frame (middleWord r))
      (fun r => 2 * prepCost (Joins.encoderInput r).length + 2) :=
  NearCubicGates.Close.Expand.PolyTab.wordFunction_of_ideal prepP 1 (by decide)
    (fun r => 4 * (Joins.encoderInput r).length + 10) (fun _ _ => 0) (fun r => prepCost (Joins.encoderInput r).length)
    (fun _ => le_rfl) (fun r => ⟨rfl, prep_runs r⟩)

/-- The width constants: `Wd = 2^L·(49 + size R)` for `L` leading ones; no calls. -/
def encSz (R : ℕ) : Sz := ⟨49 + R.size, 1, 0, 0, 0, 0⟩

theorem two_pow_size_ge (x : ℕ) : x + 1 ≤ 2 ^ x.size := Nat.lt_size_self x

theorem width_ok (R : ℕ) (r : Joins.EncoderRequest) :
    arityParam R r.n r.k + 5 ≤ (encSz R).W (leadOnes (middleWord r)) := by
  rw [middleWord, NearCubicGates.Close.CounterMachine.CellTablesProg.leadOnes_rep]
  unfold Sz.W encSz prefixLen
  simp only [one_mul]
  have h1 := arity_le R r.n r.k
  have h2 := two_pow_size_ge r.k
  have h3 := two_pow_size_ge r.n
  have h4 : r.n + r.k + 1 ≤ 2 ^ (r.k.size + r.n.size) := by
    rw [pow_add]; nlinarith
  have h5 := Nat.mul_le_mul_left (49 + R.size) h4
  unfold arityParam at h1 ⊢
  rw [Nat.mul_comm (2 ^ _)]
  nlinarith

/-- The cell program as an ordinary machine. -/
noncomputable def encWF (R : ℕ) :
    WordFunction Joins.EncoderRequest middleWord (Joins.encoderOutput R)
      (fun r => langBudget Code.Parsing.copyCallee (encSz R) NV 0 (middleWord r)
        (encCost R r.n r.k (prefixLen r))) :=
  wordFunction_of_lang middleWord (Joins.encoderOutput R) Code.Parsing.copyCallee (encSz R) (encP R)
    (fun r => encCost R r.n r.k (prefixLen r))
    (fun r => by
      obtain ⟨b, e, hout⟩ := encP_run (ctxOf Code.Parsing.copyCallee (encSz R) (middleWord r)) R (prefixLen r) r rfl
        (width_ok R r)
      exact ⟨b, _, e, hout, le_rfl⟩)
    (fun r => by have := width_ok R r; omega)

/-- **The encoder table machine** with its raw budget. -/
noncomputable def encTableWF (R : ℕ) :
    WordFunction Joins.EncoderRequest Joins.encoderInput (Joins.encoderOutput R)
      (fun r => (2 * (2 * prepCost (Joins.encoderInput r).length + 2) + 2) + 1 +
        (2 * langBudget Code.Parsing.copyCallee (encSz R) NV 0 (middleWord r) (encCost R r.n r.k (prefixLen r)) + 2)) :=
  Code.composeFramed prepWF (encWF R)

/-- A word function keeps working with a larger budget. -/
noncomputable def WordFunction.widen {Req : Type} {input output : Req → List Bool} {b b' : Req → ℕ}
    (F : WordFunction Req input output b) (h : ∀ r, b r ≤ b' r) : WordFunction Req input output b' where
  program := F.program
  realizes r := by
    obtain ⟨receipt, hrun, hout⟩ := F.realizes r
    refine ⟨receipt, ?_, hout⟩
    have := run_moreFuel F.program.machine (b r) (b' r - b r) _ receipt hrun
    rwa [Nat.add_sub_cancel' (h r)] at this

end NearCubicGates.Adapters.Amplification.Enc
