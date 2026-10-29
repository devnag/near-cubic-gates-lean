import SourceAdapters.Code.Preparation
import SourceAdapters.Code.CappedDock

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid removal of the capped-run status field, preserving
an exact frame of the returned word, including trailing zero bits. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.Parsing

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Joins

def frameEach : Script := .seq (.op (.emit true)) emitReadBit

theorem frame_each (C : Ctx) (a : State) (b : Bool) (hz : a.env 0 = 0) (hb : a.env 1 = b.toNat) :
    Ex C frameEach a {a with out := a.out ++ [true, b]} 4 := by
  have h := Ex.seq (Ex.op (OpEx.emit (C := C) true a))
    (emit_read_bit C {a with out := a.out ++ [true]} b hz hb)
  simpa [frameEach, List.append_assoc] using h

def resultInput (p : Bool × List Bool) : List Bool := p.1 :: frame p.2

def resultScript : Script := .seq (.op (.rdI 1))
  (.seq (mapField frameEach) (emitLiteral [false]))

def resultCost (p : Bool × List Bool) : ℕ := 10 * p.2.length + 10

theorem resultScript_runs (p : Bool × List Bool) :
    ∃ b n, Ex (ctxOf copyCallee payloadSize (resultInput p)) resultScript (a0 : State) b n ∧
      b.out = frame p.2 ∧ n ≤ resultCost p := by
  let C := ctxOf copyCallee payloadSize (resultInput p)
  have e1 := read_at_prefix C (a0 : State) [] p.1 (frame p.2)
    (by simp [C, ctxOf, resultInput]) rfl
  let a1 := readState (a0 : State) p.1
  have e2 := map_field C frameEach (fun b => [true, b]) 4 (frame_each C)
    a1 (by simp [a1, readState, a0, DS.set]) p.2 [p.1] []
    (by simp [C, ctxOf, resultInput]) (by simp [a1, readState, a0])
  let a2 := positioned a1 ([p.1].length + 2 * p.2.length + 1) 0
    (a1.out ++ p.2.flatMap (fun b => [true, b]))
  have e3 := emit_literal C [false] a2 (by simp [a2, a1, readState, positioned, a0, DS.set])
  refine ⟨_, _, Ex.seq e1 (Ex.seq e2 e3), ?_, ?_⟩
  · rw [NearCubicGates.Close.CounterMachine.CellTablesProg.frame_marks]
    simp [a2, a1, positioned, readState, a0, Streaming.marks]
  · simp only [List.length_cons, List.length_nil, resultCost]
    omega

def resultBudget (p : Bool × List Bool) : ℕ :=
  langBudget copyCallee payloadSize 2 0 (resultInput p) (resultCost p)

noncomputable def resultWordFunction :
    WordFunction (Bool × List Bool) resultInput (fun p => frame p.2) resultBudget :=
  wordFunction_of_lang resultInput (fun p => frame p.2) copyCallee payloadSize
    resultScript resultCost resultScript_runs (fun _ => by simp [payloadSize, Sz.W])

theorem resultBudget_bound (p : Bool × List Bool) :
    resultBudget p ≤ 1000000 * ((resultInput p).length + 1) := by
  have hl := leadOnes_le (resultInput p)
  have hlen : (resultInput p).length = 2 * p.2.length + 2 := by simp [resultInput, frame_length]
  dsimp [resultBudget, langBudget, payloadSize, resultCost, costA, costB, costC,
    Sz.W, Sz.Lk, Sz.Bk, TSK, copyCallee, Streaming.rewoundIdentityCopy, Streaming.copyProgram]
  norm_num
  omega

def cappedPair (p : Program) (r : CappedRequest) : Bool × List Bool :=
  ((LocalBitMultitape.run p.machine r.1 (p.inputTapes r.2)).isSome, cappedOutput p r)

theorem cappedPair_input (p : Program) (r : CappedRequest) :
    resultInput (cappedPair p r) = cappedResultWord p r := by
  cases hr : LocalBitMultitape.run p.machine r.1 (p.inputTapes r.2) <;>
    simp [resultInput, cappedPair, cappedOutput, cappedResultWord, hr]

/-- The shared cap program followed by an actual status-removing parser. The
returned payload is framed for subsequent caller composition. -/
noncomputable def framedCapped (p : Program) (C : ℕ)
    (W : WordFunction CappedRequest cappedRequestWord (fun r => frame (cappedResultWord p r))
      (fun r => C * (r.1 + r.2.length + 1))) :
    WordFunction CappedRequest cappedRequestWord (fun r => frame (cappedOutput p r))
      (fun r => (2 * (C * (r.1 + r.2.length + 1)) + 2) + 1 +
        (2 * resultBudget (cappedPair p r) + 2)) := by
  let Q : WordFunction CappedRequest (fun r => cappedResultWord p r)
      (fun r => frame (cappedOutput p r)) (fun r => resultBudget (cappedPair p r)) :=
    { program := resultWordFunction.program
      realizes := fun r => by
        obtain ⟨receipt, hr, ho⟩ := resultWordFunction.realizes (cappedPair p r)
        exact ⟨receipt, by simpa [cappedPair_input] using hr, ho⟩ }
  exact composeFramed W Q

theorem framedCapped_budget (p : Program) (C : ℕ)
    (W : WordFunction CappedRequest cappedRequestWord (fun r => frame (cappedResultWord p r))
      (fun r => C * (r.1 + r.2.length + 1))) (r : CappedRequest) :
    (2 * (C * (r.1 + r.2.length + 1)) + 2) + 1 + (2 * resultBudget (cappedPair p r) + 2) ≤
      (2000010 * (C + 1)) * (r.1 + r.2.length + 1) := by
  have hout := wf_out_len W r
  rw [frame_length] at hout
  have hb := resultBudget_bound (cappedPair p r)
  rw [cappedPair_input] at hb
  have hL : 1 ≤ r.1 + r.2.length + 1 := by omega
  nlinarith

/-- No new source hypothesis: this adapter consumes precisely X8. -/
theorem framedCapped_of_X8 (hX8 : CappedWordRun) (p : Program) :
    ∃ C : ℕ, Nonempty (WordFunction CappedRequest cappedRequestWord
      (fun r => frame (cappedOutput p r)) (fun r => C * (r.1 + r.2.length + 1))) := by
  obtain ⟨C, _, W⟩ := hX8 p
  obtain ⟨W⟩ := W
  exact ⟨2000010 * (C + 1), ⟨(framedCapped p C W).enlargeBudget (framedCapped_budget p C W)⟩⟩

end NearCubicGates.Adapters.Code.Parsing
