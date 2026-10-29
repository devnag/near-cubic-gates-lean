import SourceAdapters.Code.Parsing

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": actual concatenation of two framed input fields. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.PairTransform

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open Parsing

def pairWord (p : List Bool × List Bool) : List Bool := frame p.1 ++ frame p.2

def concatScript : Script := .seq (readField true) (readField true)

def concatCost (p : List Bool × List Bool) : ℕ := 8 * p.1.length + 8 * p.2.length + 9

theorem concat_runs (p : List Bool × List Bool) :
    ∃ b n, Ex (ctxOf copyCallee payloadSize (pairWord p)) concatScript (a0 : State) b n ∧
      b.out = p.1 ++ p.2 ∧ n ≤ concatCost p := by
  let C := ctxOf copyCallee payloadSize (pairWord p)
  have e1 := read_field C true (a0 : State) rfl p.1 [] (frame p.2)
    (by simp [C, ctxOf, pairWord]) rfl
  let s1 := positioned (a0 : State) (0 + 2 * p.1.length + 1) 0 ([] ++ if true then p.1 else [])
  have e2 := read_field C true s1 (by simp [s1, positioned, DS.set, a0]) p.2 (frame p.1) []
    (by simp [C, ctxOf, pairWord]) (by simp [s1, positioned, frame_length])
  refine ⟨_, _, Ex.seq e1 e2, ?_, ?_⟩
  · simp [positioned, s1]
  · simp only [costPerBit, if_true, concatCost]
    omega

def compiledConcatBudget (p : List Bool × List Bool) : ℕ :=
  langBudget copyCallee payloadSize 2 0 (pairWord p) (concatCost p)

noncomputable def compiledConcatenate : WordFunction (List Bool × List Bool) pairWord
    (fun p => p.1 ++ p.2) compiledConcatBudget :=
  wordFunction_of_lang pairWord (fun p => p.1 ++ p.2) copyCallee payloadSize concatScript concatCost
    concat_runs (fun _ => by simp [payloadSize, Sz.W])

theorem concat_budget (p : List Bool × List Bool) :
    compiledConcatBudget p ≤ 100000 * ((pairWord p).length + 1) := by
  have hl := leadOnes_le (pairWord p)
  have hlen : (pairWord p).length = 2 * p.1.length + 2 * p.2.length + 2 := by
    simp only [pairWord, List.length_append, frame_length]
    omega
  dsimp [compiledConcatBudget, langBudget, payloadSize, concatCost, costA, costB, costC,
    Sz.W, Sz.Lk, Sz.Bk, TSK, copyCallee, Streaming.rewoundIdentityCopy, Streaming.copyProgram]
  norm_num
  omega

/-- Decodes both fields and concatenates their exact payloads, including trailing zeros. -/
noncomputable def concatenate : WordFunction (List Bool × List Bool) pairWord
    (fun p => p.1 ++ p.2) (fun p => 100000 * ((pairWord p).length + 1)) :=
  compiledConcatenate.enlargeBudget concat_budget

end NearCubicGates.Adapters.Code.PairTransform
