import SourceAdapters.ShortPCP.Machines.WidthPrefix
import SourceAdapters.Code.Composition
import Proof.Gates.Codec.PairFrame
import Proof.Gates.WordPrograms.RegArith
import Proof.Gates.Expand.PolyTabPack

/-!
# Paid framing of the coordinate request

The construction in `lem:generator`: an actual ordinary preparer changes a raw
request into an internally framed payload before the paid width prefix.
It counts the physical input, rewinds it, and frames every physical bit.
Its public input is raw w and its output is exactly frame(frame w).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Adapters.ShortPCP.Machines.WidthPrefix
open NearCubicWires.RepairOrdinary.Streaming (marks)

def framePrep : WMX 1 5 := .seq (.wm countL) (.seq (addR 1 2 4)
  (.seq (.wm (WM.rewind 0 1)) (.seq (.wm (.inc 2))
    (.seq (.wm (frameStream 0 1 3 2)) (.wm (emitC 1 3 false))))))

def framePrepCost (n : ℕ) : ℕ := 120 * n + 60

theorem framePrep_runs (word : List Bool) :
    ∃ t, WXExec (8 * word.length + 16) framePrep
      (idealStart 1 5 word (fun _ => 0)) t (framePrepCost word.length) ∧
      t.st 1 = frame (frame word) := by
  let cap := 8 * word.length + 16
  let s1 := pst word [] (2 * word.length) 0 ![word.length, 2 * word.length, 0, 0, 0]
  have e1 := count_spec cap word (by dsimp [cap]; omega) word.length 0 (by omega)
  have hstart : pst word [] (2 * 0) 0 ![0, 2 * 0, 0, 0, 0] =
      idealStart 1 5 word (fun _ => 0) := by
    apply WState.eq
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hstart] at e1
  have e2 := addR_spec cap (A := (1 : Fin 5)) (B := 2) (T := 4)
    (by decide) (by decide) (by decide) s1 (by simp [s1, pst]) (by simp [s1, pst, cap]; omega)
  let s2 := s1.setv 2 (s1.val 2 + s1.val 1)
  have e3 := wrewind_spec cap (0 : Fin 2) (1 : Fin 5) (2 * word.length) s2
    (by simp [s2, s1, pst]) (by simp [s2, s1, pst, cap]; omega)
  let s3 := (s2.setv 1 0).seth 0 (s2.sh 0 - 2 * word.length)
  have e4 := WExec.inc (cap := cap) (2 : Fin 5) s3 (by simp [s3, s2, s1, pst, cap]; omega)
  let s4 := s3.setv 2 (s3.val 2 + 1)
  have e5 := frameStream_spec cap (0 : Fin 2) 1 (by decide) (3 : Fin 5) 2 (by decide)
    (frame word) [] [] s4 (by simp [s4, s3, s2, s1, pst])
    (by simp [s4, s3, s2, s1, pst]) (by simp [s4, s3, s2, s1, pst])
    (by simp [s4, s3, s2, s1, pst, frame_length])
    (by simp [frame_length, cap]; omega)
    (by simp [s4, s3, s2, s1, pst, frame_length, cap]; omega)
  let s5 := ((appendO s4 1 3 (marks (frame word))).setv 2 0).seth 0 (0 + (frame word).length)
  have e6 := emitC_spec (cap := cap) (1 : Fin 2) (3 : Fin 5) false s5
    (by simp [s5, s4, s3, s2, s1, pst, appendO])
    (by simp [s5, s4, s3, s2, s1, pst, appendO,
      frame_length, cap]; omega)
  refine ⟨((s5.sets 1 (s5.st 1 ++ [false])).seth 1 (s5.sh 1 + 1)).setv 3 (s5.val 3 + 1), ?_, ?_⟩
  · exact (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq (WXExec.wm e3)
      (WXExec.seq (WXExec.wm e4) (WXExec.seq (WXExec.wm e5) (WXExec.wm e6)))))).mono (by
        simp [framePrepCost, s1, pst, frame_length]
        omega)
  · simp [s5, s4, s3, s2, s1, pst, appendO, frame_eq_marks]

def framePrepBudget (word : List Bool) : ℕ := 2 * framePrepCost word.length + 2

/-- One fixed ordinary machine; framing and its rewind are included in the budget. -/
noncomputable def framePrepWF : WordFunction (List Bool) id (fun w => frame (frame w)) framePrepBudget :=
  wordFunction_of_ideal framePrep 1 (by decide) (fun w => 8 * w.length + 16) (fun _ _ => 0)
    (fun w => framePrepCost w.length) (fun _ => le_rfl) (fun w => ⟨rfl, framePrep_runs w⟩)

theorem framePrepBudget_le (word : List Bool) : framePrepBudget word ≤ 362 * (word.length + 1) := by
  simp only [framePrepBudget, framePrepCost]
  omega

/-- The exact internal FL input after both ordinary preprocessing machines. -/
def preparedInput (word : List Bool) : List Bool := ShortPCP.Time.prefixWord (frame word)

def preparedBudget (word : List Bool) : ℕ :=
  (2 * framePrepBudget word + 2) + 1 + (2 * prefixBudget (frame word).length + 2)

noncomputable def preparedWF :
    WordFunction (List Bool) id (fun w => frame (preparedInput w)) preparedBudget :=
  Code.composeFramed framePrepWF
    { program := prefixWF.program, realizes := fun w => prefixWF.realizes (frame w) }

end NearCubicGates.Adapters.Routing.CoordinateMachine
