import Proof.Gates.Codec.Frame
import Proof.Gates.Codec.Field
import Proof.Gates.WordPrograms.Hoare

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ} (cap : ℕ)

theorem frame_eq_marks (l : List Bool) : RepairOrdinary.frame l = marks l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [RepairOrdinary.frame, marks, ih]

/-- `dst` gains `frame (u ++ v)`. -/
def pairFrame (A B dst : Fin (ns + 1)) (OP KA KB : Fin nr) : WM ns nr :=
  .seq (frameStream A dst OP KA) (.seq (frameStream B dst OP KB) (emitC dst OP false))

/-- **The entry word.** From `u` at the head of `A` and `v` at the head of `B` (both heads `0`, lengths in `KA`, `KB`),
`dst` gains `frame (u ++ v)`; the heads of `A`, `B` end past `u`, `v`; `KA`, `KB` end at `0`; `OP` counts the output;
nothing else changes. -/
theorem pairFrame_spec (A B dst : Fin (ns + 1)) (hAd : A ≠ dst) (hBd : B ≠ dst) (hAB : A ≠ B)
    (OP KA KB : Fin nr) (hKAO : KA ≠ OP) (hKBO : KB ≠ OP) (hKAB : KA ≠ KB)
    (u v restA restB : List Bool) (σ : WState ns nr) (hA : σ.st A = u ++ restA) (hAh : σ.sh A = 0)
    (hB : σ.st B = v ++ restB) (hBh : σ.sh B = 0) (hd : σ.sh dst = (σ.st dst).length)
    (hKA : σ.val KA = u.length) (hKB : σ.val KB = v.length) (hu : u.length ≤ cap) (hv : v.length ≤ cap)
    (hc : σ.val OP + 2 * u.length + 2 * v.length + 1 ≤ cap) :
    ∃ τ : WState ns nr, WExec cap (pairFrame A B dst OP KA KB) σ τ (22 * u.length + 22 * v.length + 11) ∧
      τ.st dst = σ.st dst ++ RepairOrdinary.frame (u ++ v) ∧ τ.sh dst = (τ.st dst).length ∧
      τ.val OP = σ.val OP + (RepairOrdinary.frame (u ++ v)).length ∧ τ.val KA = 0 ∧ τ.val KB = 0 ∧
      τ.sh A = u.length ∧ τ.sh B = v.length ∧ SameExcept σ τ [A, B, dst] [OP, KA, KB] := by
  have e1 := frameStream_spec cap A dst hAd OP KA hKAO u [] restA σ (by simpa using hA) (by simpa using hAh) hd hKA hu
    (by omega)
  set σ1 := ((appendO σ dst OP (marks u)).setv KA 0).seth A (([] : List Bool).length + u.length) with hσ1
  have h1B : σ1.st B = [] ++ v ++ restB := by simp [hσ1, Function.update_apply, hBd, hB]
  have h1Bh : σ1.sh B = ([] : List Bool).length := by
    simp [hσ1, Function.update_of_ne (Ne.symm hAB), Function.update_of_ne hBd, hBh]
  have h1d : σ1.sh dst = (σ1.st dst).length := by
    simp [hσ1, Function.update_of_ne (Ne.symm hAd), hd]
  have h1K : σ1.val KB = v.length := by
    simp [hσ1, Function.update_of_ne hKAB.symm, Function.update_of_ne hKBO, hKB]
  have h1O : σ1.val OP = σ.val OP + 2 * u.length := by
    simp [hσ1, Function.update_of_ne hKAO.symm, marks_length]
  have e2 := frameStream_spec cap B dst hBd OP KB hKBO v [] restB σ1 h1B h1Bh h1d h1K hv (by omega)
  set σ2 := ((appendO σ1 dst OP (marks v)).setv KB 0).seth B (([] : List Bool).length + v.length) with hσ2
  have h2d : σ2.sh dst = (σ2.st dst).length := by
    simp [hσ2, Function.update_of_ne (Ne.symm hBd), h1d]
  have h2O : σ2.val OP = σ.val OP + 2 * u.length + 2 * v.length := by
    simp [hσ2, Function.update_of_ne hKBO.symm, marks_length, h1O]
  have e3 := emitC_spec (cap := cap) dst OP false σ2 h2d (by omega)
  have hne := And.intro hAd (And.intro hBd (And.intro hAB (And.intro hKAO (And.intro hKBO hKAB))))
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hσ2, hσ1, Function.update_apply, hAd, hBd, hAd.symm, hBd.symm, frame_eq_marks, marksApp]
  · simp [hσ2, hσ1, Function.update_apply, hAd, hBd, hAd.symm, hBd.symm, hd, marks_length]; omega
  · simp [hσ2, hσ1, Function.update_apply, hKAO, hKBO, hKAO.symm, hKBO.symm, frame_eq_marks, marksApp,
      marks_length]; omega
  · simp [hσ2, hσ1, Function.update_apply, hKAO, hKAB, hKBO, hKAB.symm]
  · simp [hσ2, Function.update_apply, hKBO]
  · simp [hσ2, hσ1, Function.update_apply, hAB, hAd, hBd.symm, hAB.symm, hAd.symm]
  · simp [hσ2, Function.update_apply, hBd]
  · refine ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [hσ2, hσ1, Function.update_apply, hx.1, hx.2.1, hx.2.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hσ2, hσ1, Function.update_apply, hr.1, hr.2.1, hr.2.2]
    · simp [hσ2, hσ1]

/-- Frame one raw witness field (`countWord k ++ bits`, the guess format) onto `dst`: read the count into `K`, copy
the `k` bits as marks, close with `false`, so `dst` gains `frame bits` (`k = |bits|`). -/
def fieldFrameW (W dst : Fin (ns + 1)) (OP K : Fin nr) : WM ns nr :=
  .seq (countW W K) (.seq (frameStream W dst OP K) (emitC dst OP false))

theorem fieldFrameW_spec (W dst : Fin (ns + 1)) (hWd : W ≠ dst) (OP K : Fin nr) (hKO : K ≠ OP)
    (pre bits rest : List Bool) (σ : WState ns nr) (hst : σ.st W = pre ++ (Worker.Format.countWord bits.length ++ bits) ++ rest)
    (hsh : σ.sh W = pre.length) (hd : σ.sh dst = (σ.st dst).length) (hK : σ.val K = 0)
    (hc : σ.val OP + 2 * bits.length + 1 ≤ cap) (hb : bits.length ≤ cap) :
    WExec cap (fieldFrameW W dst OP K) σ
      ((appendO (σ.seth W (pre.length + bits.length + 1 + bits.length)) dst OP (RepairOrdinary.frame bits)))
      (7 * bits.length + 3 + 1 + (22 * bits.length + 1 + 1 + 7)) := by
  have hrc : Worker.Format.readCount ((σ.st W).drop (σ.sh W)) = (bits.length, bits ++ rest) := by
    rw [hst, hsh, List.append_assoc, List.drop_left, List.append_assoc]
    exact Worker.Format.readCount_word bits.length (bits ++ rest)
  have e1 := countW_spec cap W K σ (by rw [hrc, hK]; simp; exact hb)
  rw [hrc, hK, hsh] at e1
  simp only [Nat.zero_add] at e1
  set σ1 := (σ.seth W (pre.length + bits.length + 1)).setv K bits.length with hσ1
  have e2 := frameStream_spec cap W dst hWd OP K hKO bits (pre ++ Worker.Format.countWord bits.length) rest σ1
    (by simp [hσ1, hst, List.append_assoc])
    (by simp [hσ1, Worker.Format.countWord]; omega)
    (by simp [hσ1, Function.update_apply, hWd.symm, hd])
    (by simp [hσ1]) hb
    (by simp [hσ1, Function.update_of_ne hKO.symm]; omega)
  set σ2 := ((appendO σ1 dst OP (marks bits)).setv K 0).seth W ((pre ++ Worker.Format.countWord bits.length).length +
    bits.length) with hσ2
  have e3 := emitC_spec (cap := cap) dst OP false σ2
    (by simp [hσ2, hσ1, Function.update_apply, hWd.symm, hd, marks_length])
    (by simp [hσ2, hσ1, Function.update_of_ne hKO.symm, marks_length]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl
  apply WState.eq
  · funext y; by_cases hy : y = W
    · subst hy; simp [hσ2, hσ1, appendO, Function.update_apply, hWd, Worker.Format.countWord]; omega
    · by_cases hyd : y = dst
      · subst hyd; simp [hσ2, hσ1, appendO, Function.update_apply, hy, hd, marks_length, frame_eq_marks]; omega
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
  · funext y; by_cases hyd : y = dst
    · subst hyd; simp [hσ2, hσ1, appendO, Function.update_apply, hWd.symm, frame_eq_marks]
    · simp [hσ2, hσ1, appendO, Function.update_of_ne hyd]
  · funext r
    by_cases hr : r = OP
    · subst hr; simp [hσ2, hσ1, appendO, Function.update_apply, hKO.symm, frame_eq_marks, marks_length]; omega
    · by_cases hrK : r = K
      · subst hrK; simp [hσ2, hσ1, appendO, Function.update_apply, hr, hK]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hr, Function.update_of_ne hrK]
  · rfl

end NearCubicGates.Close.Codec
