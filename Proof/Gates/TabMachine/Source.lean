import Proof.Gates.TabMachine.Points
import Proof.Gates.Codec.Frame

/-! # The source assembly: the printer's framed source

The shared request writer (`EquationRowFramed.machine`, the back end `back_spec`) reads `frame (EquationRowRaw.source r)`
with `source r = natWord d ++ natWord p ++ natWord g ++ odd :: EquationRowCuts.stream p cuts`. After the point loop the
cut stream `Z 34` holds `allCuts` (open, length in `Y 56`); **`srcP_spec`** writes `marks (natWord d)`,
`marks (natWord p)`, `marks (natWord g)` (the shared `writeNatM`), `marks [odd]`, then the cut stream marked
(`Codec.frameStream`) and the closing `false` onto a fresh stream `O`, and rewinds. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (writeNatM writeNatM_spec appendO appendO_append)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec (frameStream frameStream_spec emitMarks emitMarks_spec)
open StablePartition.Workspace (overlay)
open NearCubicGates.Close.Tabulator

variable {ns nr : ℕ}

section Source
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

/-- `writeNatM`'s registers: the value register, six scratch registers (`0` at rest), the output counter `Y 108`. -/
def rW (v : Fin 112) (hv : v ∈ [(105 : Fin 112), 106, 74]) : Fin 8 ↪ Fin nr :=
  (⟨![v, 91, 92, 93, 95, 96, 97, 108], by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> decide⟩ : Fin 8 ↪ Fin 112).trans Y

theorem rW_zero (v : Fin 112) (hv : v ∈ [(105 : Fin 112), 106, 74]) : rW Y v hv 0 = Y v := rfl
theorem rW_seven (v : Fin 112) (hv : v ∈ [(105 : Fin 112), 106, 74]) : rW Y v hv 7 = Y 108 := rfl
theorem rW_scratch (v : Fin 112) (hv : v ∈ [(105 : Fin 112), 106, 74]) (j : Fin 8) (h0 : j ≠ 0) (h7 : j ≠ 7) :
    ∃ r ∈ ([91, 92, 93, 95, 96, 97] : List (Fin 112)), rW Y v hv j = Y r := by
  refine ⟨![v, 91, 92, 93, 95, 96, 97, 108] j, ?_, rfl⟩
  fin_cases j <;> simp_all

def srcHead (O : Fin (ns + 1)) : WMX ns nr :=
  .seq (addR (Y 56) (Y 104) (Y 99))
  (.seq (addR (Y 56) (Y 109) (Y 99))
  (.seq (closeOutX (Z 34) (Y 56))
  (.seq (.wm (writeNatM O (rW Y 105 (by simp))))
  (.seq (.wm (writeNatM O (rW Y 106 (by simp))))
  (.seq (.wm (writeNatM O (rW Y 74 (by simp))))
    (.ifr (Y 107) (.wm (emitMarks O (Y 108) [true])) (.wm (emitMarks O (Y 108) [false]))))))))

def srcTail (O : Fin (ns + 1)) : WMX ns nr :=
  .seq (.wm (frameStream (Z 34) O (Y 108) (Y 104)))
  (.seq (.wm (emitC O (Y 108) false))
  (.seq (.wm (WM.rewind O (Y 108))) (.wm (WM.rewind (Z 34) (Y 109)))))

def srcP (O : Fin (ns + 1)) : WMX ns nr := .seq (srcHead Z Y O) (srcTail Z Y O)

def wnCost (v : ℕ) : ℕ := (natBitLength v + 10) * (100 * v + 200)

def srcHeadCost (n d p g : ℕ) : ℕ :=
  18 * n + 3 + 1 + (18 * n + 3 + 1 + (5 * n + 3 + 1 + (wnCost d + 1 + (wnCost p + 1 + (wnCost g + 1 + (16 + 1))))))

def srcTailCost (n m : ℕ) : ℕ := 22 * n + 1 + 1 + (7 + 1 + (5 * m + 1 + 1 + (5 * n + 1)))

/-- The source's header part. -/
def srcHdr (d p g : ℕ) (odd : Bool) : List Bool :=
  natWord d ++ natWord p ++ natWord g ++ [odd]

theorem natWord_len (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := by
  simp [natWord]

theorem natBitLength_le' (v : ℕ) : natBitLength v ≤ v + 1 := by
  have h1 := Nat.log_lt_self 2 (show v + 1 ≠ 0 by omega)
  have h2 := Nat.log_mono_right (show v ≤ v + 1 by omega) (b := 2)
  unfold natBitLength; omega

theorem srcHead_spec (cap W s k : ℕ) (O : Fin (ns + 1)) (hO : ∀ i, O ≠ Z i) (xs : List ℕ) (out L0 : List Bool)
    (g d p : ℕ) (odd : Bool) (σ : WState ns nr) (h : CutRest Z Y cap W s k xs out L0 g 0 σ)
    (hOs : σ.st O = []) (hOh : σ.sh O = 0) (h104 : σ.val (Y 104) = 0) (h108 : σ.val (Y 108) = 0)
    (h109 : σ.val (Y 109) = 0) (h105 : σ.val (Y 105) = d) (h106 : σ.val (Y 106) = p)
    (h107 : σ.val (Y 107) = odd.toNat)
    (hcap : 2 * out.length + 10 * (d + p + g) + 2 * (marks (srcHdr d p g odd)).length + 40 ≤ cap) :
    Runs cap (srcHead Z Y O) σ (srcHeadCost out.length d p g) (fun τ =>
      τ.st O = marks (srcHdr d p g odd) ∧ τ.sh O = (marks (srcHdr d p g odd)).length ∧
      τ.val (Y 108) = (marks (srcHdr d p g odd)).length ∧
      (∃ junk, τ.st (Z 34) = out ++ [false] ++ junk) ∧ τ.sh (Z 34) = 0 ∧
      τ.val (Y 104) = out.length ∧ τ.val (Y 109) = out.length ∧ τ.val (Y 56) = 0 ∧
      SameExcept σ τ [O, Z 34] [Y 56, Y 104, Y 109, Y 108]) := by
  have hz := h.rest.zero
  have hOut := h.cut
  have hgc := h.gc
  have hl : ∀ v : ℕ, natBitLength v ≤ v + 1 := fun v => natBitLength_le' v
  have hmlen : (marks (srcHdr d p g odd)).length =
      2 * ((2 * natBitLength d + 1) + (2 * natBitLength p + 1) + (2 * natBitLength g + 1) + 1) := by
    simp [marks, srcHdr, natWord_len, List.length_flatMap]; ring
  -- (1, 2) copy the cut stream's length
  have e1 := addR_spec cap (A := Y 56) (B := Y 104) (T := Y 99) (Y.injective.ne (by decide))
    (Y.injective.ne (by decide)) (Y.injective.ne (by decide)) σ h.r99 (by rw [hOut.2.2, h104]; omega)
  rw [hOut.2.2, h104, Nat.zero_add] at e1
  refine Runs.seqE e1 ?_
  set σ1 := σ.setv (Y 104) out.length with hσ1
  have n104 : ∀ r : Fin 112, r ≠ 104 → Y r ≠ Y 104 := fun r hr => Y.injective.ne hr
  have e2 := addR_spec cap (A := Y 56) (B := Y 109) (T := Y 99) (Y.injective.ne (by decide))
    (Y.injective.ne (by decide)) (Y.injective.ne (by decide)) σ1
    (by rw [hσ1, WState.setv_val, Function.update_of_ne (n104 99 (by decide))]; exact h.r99)
    (by rw [hσ1, WState.setv_val, Function.update_of_ne (n104 109 (by decide)),
          Function.update_of_ne (n104 56 (by decide)), h109, hOut.2.2]; omega)
  have v56 : σ1.val (Y 56) = out.length := by
    rw [hσ1, WState.setv_val, Function.update_of_ne (n104 56 (by decide))]; exact hOut.2.2
  have v109 : σ1.val (Y 109) = 0 := by
    rw [hσ1, WState.setv_val, Function.update_of_ne (n104 109 (by decide))]; exact h109
  rw [v56, v109, Nat.zero_add] at e2
  refine Runs.seqE e2 ?_
  set σ2 := σ1.setv (Y 109) out.length with hσ2
  -- (3) close the cut stream
  have hO2 : OutOn σ2 (Z 34) (Y 56) out L0 :=
    ⟨by simp [hσ2, hσ1]; exact hOut.1, by simp [hσ2, hσ1]; exact hOut.2.1,
      by rw [hσ2, WState.setv_val, Function.update_of_ne (Y.injective.ne (show (56 : Fin 112) ≠ 109 by decide)), v56]⟩
  have e3 := closeOut_spec cap σ2 out L0 hO2 (by omega)
  refine Runs.seqE (WXExec.wm e3) ?_
  set σ3 := ((σ2.sets (Z 34) (overlay (out ++ [false]) L0)).seth (Z 34) 0).setv (Y 56) 0 with hσ3
  have v3 : ∀ r : Fin 112, r ∉ ([104, 109, 56] : List (Fin 112)) → σ3.val (Y r) = σ.val (Y r) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hσ3, hσ2, hσ1, Function.update_of_ne (Y.injective.ne hr.1), Function.update_of_ne (Y.injective.ne hr.2.1),
      Function.update_of_ne (Y.injective.ne hr.2.2)]
  have hO3s : σ3.st O = [] := by simp [hσ3, hσ2, hσ1, Function.update_of_ne (hO 34), hOs]
  have hO3h : σ3.sh O = 0 := by simp [hσ3, hσ2, hσ1, Function.update_of_ne (hO 34), hOh]
  -- appending to `O` keeps every other register and stream
  have apv : ∀ (τ : WState ns nr) (u : List Bool) (r : Fin 112), r ≠ 108 →
      (appendO τ O (Y 108) u).val (Y r) = τ.val (Y r) := fun τ u r hr => by
    simp [Function.update_of_ne (Y.injective.ne hr)]
  have scr : ∀ (τ : WState ns nr), (∀ r ∈ ([91, 92, 93, 95, 96, 97] : List (Fin 112)), τ.val (Y r) = 0) →
      ∀ (v : Fin 112) (hv : v ∈ [(105 : Fin 112), 106, 74]) (j : Fin 8), j ≠ 0 → j ≠ 7 → τ.val (rW Y v hv j) = 0 := by
    intro τ hτ v hv j h0 h7
    obtain ⟨r, hr, e⟩ := rW_scratch Y v hv j h0 h7
    rw [e]; exact hτ r hr
  have z3 : ∀ r ∈ ([91, 92, 93, 95, 96, 97] : List (Fin 112)), σ3.val (Y r) = 0 := by
    intro r hr
    rw [v3 r (by revert r; decide)]; exact hz r (by revert r; decide)
  -- (4) natWord d
  have e4 := writeNatM_spec cap O (rW Y 105 (by simp)) σ3
    (scr σ3 z3 105 (by simp) 1 (by decide) (by decide)) (scr σ3 z3 105 (by simp) 2 (by decide) (by decide))
    (scr σ3 z3 105 (by simp) 3 (by decide) (by decide)) (scr σ3 z3 105 (by simp) 4 (by decide) (by decide))
    (scr σ3 z3 105 (by simp) 5 (by decide) (by decide)) (scr σ3 z3 105 (by simp) 6 (by decide) (by decide))
    (by rw [hO3s, hO3h]; rfl)
    (by rw [rW_zero, rW_seven, v3 105 (by decide), v3 108 (by decide), h105, h108]; have := hl d; omega)
  rw [rW_zero, rW_seven, v3 105 (by decide), h105] at e4
  refine Runs.seqE (WXExec.wm e4) ?_
  set σ4 := appendO σ3 O (Y 108) (marks (natWord d)) with hσ4
  have z4 : ∀ r ∈ ([91, 92, 93, 95, 96, 97] : List (Fin 112)), σ4.val (Y r) = 0 := by
    intro r hr; rw [apv σ3 _ r (by revert r; decide)]; exact z3 r hr
  have o4 : σ4.sh O = (σ4.st O).length := by simp [hσ4, hO3s, hO3h]
  have q4 : σ4.val (Y 108) = (marks (natWord d)).length := by simp [hσ4, v3 108 (by decide), h108]
  -- (5) natWord p
  have e5 := writeNatM_spec cap O (rW Y 106 (by simp)) σ4
    (scr σ4 z4 106 (by simp) 1 (by decide) (by decide)) (scr σ4 z4 106 (by simp) 2 (by decide) (by decide))
    (scr σ4 z4 106 (by simp) 3 (by decide) (by decide)) (scr σ4 z4 106 (by simp) 4 (by decide) (by decide))
    (scr σ4 z4 106 (by simp) 5 (by decide) (by decide)) (scr σ4 z4 106 (by simp) 6 (by decide) (by decide)) o4
    (by rw [rW_zero, rW_seven, apv σ3 _ 106 (by decide), v3 106 (by decide), h106, q4]
        have := hl p; have : (marks (natWord d)).length ≤ (marks (srcHdr d p g odd)).length := by
          simp [marks, srcHdr, List.length_flatMap]
        omega)
  rw [rW_zero, rW_seven, apv σ3 _ 106 (by decide), v3 106 (by decide), h106] at e5
  refine Runs.seqE (WXExec.wm e5) ?_
  set σ5 := appendO σ4 O (Y 108) (marks (natWord p)) with hσ5
  have z5 : ∀ r ∈ ([91, 92, 93, 95, 96, 97] : List (Fin 112)), σ5.val (Y r) = 0 := by
    intro r hr; rw [apv σ4 _ r (by revert r; decide)]; exact z4 r hr
  have o5 : σ5.sh O = (σ5.st O).length := by simp [hσ5, o4]
  have q5 : σ5.val (Y 108) = (marks (natWord d)).length + (marks (natWord p)).length := by simp [hσ5, q4]
  -- (6) natWord g
  have g4 : σ4.val (Y 74) = g := by rw [apv σ3 _ 74 (by decide), v3 74 (by decide)]; exact hgc
  have e6 := writeNatM_spec cap O (rW Y 74 (by simp)) σ5
    (scr σ5 z5 74 (by simp) 1 (by decide) (by decide)) (scr σ5 z5 74 (by simp) 2 (by decide) (by decide))
    (scr σ5 z5 74 (by simp) 3 (by decide) (by decide)) (scr σ5 z5 74 (by simp) 4 (by decide) (by decide))
    (scr σ5 z5 74 (by simp) 5 (by decide) (by decide)) (scr σ5 z5 74 (by simp) 6 (by decide) (by decide)) o5
    (by rw [rW_zero, rW_seven, apv σ4 _ 74 (by decide), g4, q5]
        have := hl g; have : (marks (natWord d)).length + (marks (natWord p)).length ≤
            (marks (srcHdr d p g odd)).length := by
          simp [marks, srcHdr, List.length_flatMap]
        omega)
  rw [rW_zero, rW_seven, apv σ4 _ 74 (by decide), g4] at e6
  refine Runs.seqE (WXExec.wm e6) ?_
  set σ6 := appendO σ5 O (Y 108) (marks (natWord g)) with hσ6
  have o6 : σ6.sh O = (σ6.st O).length := by simp [hσ6, o5]
  have q6 : σ6.val (Y 108) + 2 * [odd].length ≤ cap := by
    simp [hσ6, q5]
    have : (marks (natWord d)).length + (marks (natWord p)).length + (marks (natWord g)).length + 2 ≤
        (marks (srcHdr d p g odd)).length := by simp [marks, srcHdr, List.length_flatMap]; omega
    simp [marks] at this; omega
  have v107 : σ6.val (Y 107) = odd.toNat := by
    rw [hσ6, apv σ5 _ 107 (by decide), hσ5, apv σ4 _ 107 (by decide), hσ4, apv σ3 _ 107 (by decide),
      v3 107 (by decide)]; exact h107
  -- (7) the odd flag
  have e7 : Runs cap (.ifr (Y 107) (.wm (emitMarks O (Y 108) [true])) (.wm (emitMarks O (Y 108) [false]))) σ6
      (16 + 1) (fun τ => τ = appendO σ6 O (Y 108) (marks [odd])) := by
    cases odd
    · exact Runs.ifrF (by rw [v107]; rfl) (Runs.of (WXExec.wm (emitMarks_spec cap O (Y 108) [false] σ6 o6 q6)) rfl)
    · exact Runs.ifrT (by rw [v107]; decide) (Runs.of (WXExec.wm (emitMarks_spec cap O (Y 108) [true] σ6 o6 q6)) rfl)
  refine e7.post fun τ hτ => ?_
  subst hτ
  have eapp : appendO σ6 O (Y 108) (marks [odd]) = appendO σ3 O (Y 108) (marks (srcHdr d p g odd)) := by
    rw [hσ6, hσ5, hσ4, appendO_append, appendO_append, appendO_append]
    simp [srcHdr, NearCubicWires.RepairOrdinary.Streaming.marks_append, List.append_assoc]
  rw [eapp]
  have n34 : O ≠ Z 34 := hO 34
  refine ⟨by simp [hO3s], by simp [hO3h], by simp [v3 108 (by decide), h108], ⟨L0.drop (out ++ [false]).length, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne n34.symm, hσ3, overlay]
  · simp [Function.update_of_ne n34.symm, hσ3]
  · rw [apv σ3 _ 104 (by decide)]; simp [hσ3, hσ2, hσ1, Function.update_of_ne (Y.injective.ne
      (show (104 : Fin 112) ≠ 56 by decide)), Function.update_of_ne (Y.injective.ne (show (104 : Fin 112) ≠ 109 by decide))]
  · rw [apv σ3 _ 109 (by decide)]; simp [hσ3, hσ2, Function.update_of_ne (Y.injective.ne
      (show (109 : Fin 112) ≠ 56 by decide))]
  · rw [apv σ3 _ 56 (by decide)]; simp [hσ3]
  · refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hσ3, hσ2, hσ1]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [Function.update_of_ne hx.1, Function.update_of_ne hx.2, hσ3, hσ2, hσ1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [Function.update_of_ne hr.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2.1,
        Function.update_of_ne hr.2.2.2, hσ3, hσ2, hσ1]

theorem frame_eq_marks (w : List Bool) : frame w = marks w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, ih, marks]

theorem srcTail_spec (cap : ℕ) (O : Fin (ns + 1)) (hO : ∀ i, O ≠ Z i) (out junk hdr : List Bool) (τ : WState ns nr)
    (hOs : τ.st O = marks hdr) (hOh : τ.sh O = (marks hdr).length) (h108 : τ.val (Y 108) = (marks hdr).length)
    (h34 : τ.st (Z 34) = out ++ [false] ++ junk) (h34h : τ.sh (Z 34) = 0) (h104 : τ.val (Y 104) = out.length)
    (h109 : τ.val (Y 109) = out.length) (hcap : (marks hdr).length + 2 * out.length + 2 ≤ cap) :
    Runs cap (srcTail Z Y O) τ (srcTailCost out.length ((marks hdr).length + 2 * out.length + 1)) (fun ρ =>
      ρ.st O = frame (hdr ++ out) ∧ ρ.sh O = 0 ∧ ρ.st (Z 34) = τ.st (Z 34) ∧ ρ.sh (Z 34) = 0 ∧
      ρ.val (Y 104) = 0 ∧ ρ.val (Y 108) = 0 ∧ ρ.val (Y 109) = 0 ∧
      SameExcept τ ρ [O, Z 34] [Y 104, Y 108, Y 109]) := by
  have n34 : Z 34 ≠ O := (hO 34).symm
  have e1 := frameStream_spec cap (Z 34) O n34 (Y 108) (Y 104) (Y.injective.ne (by decide)) out [] ([false] ++ junk) τ
    (by rw [h34]; simp) (by rw [h34h]; rfl) (by rw [hOh, hOs]) h104 (by omega) (by rw [h108]; omega)
  refine Runs.seqE (WXExec.wm e1) ?_
  set τ1 := ((appendO τ O (Y 108) (marks out)).setv (Y 104) 0).seth (Z 34) (([] : List Bool).length + out.length)
    with hτ1
  have n108 : Y 108 ≠ Y 104 := Y.injective.ne (by decide)
  have o1 : τ1.sh O = (τ1.st O).length := by
    simp [hτ1, Function.update_of_ne n34.symm, hOh, hOs]
  have c1 : τ1.val (Y 108) < cap := by
    simp [hτ1, Function.update_of_ne n108, h108, Streaming.marks_length]; simp [marks] at hcap ⊢; omega
  have e2 := emitC_spec cap O (Y 108) false τ1 o1 c1
  refine Runs.seqE (WXExec.wm e2) ?_
  set τ2 := ((τ1.sets O (τ1.st O ++ [false])).seth O (τ1.sh O + 1)).setv (Y 108) (τ1.val (Y 108) + 1) with hτ2
  have v2 : τ2.val (Y 108) = (marks hdr).length + 2 * out.length + 1 := by
    simp [hτ2, hτ1, Function.update_of_ne n108, h108]
  have e3 := wrewind_spec (cap := cap) O (Y 108) _ τ2 v2 (by rw [v2]; omega)
  refine Runs.seqE (WXExec.wm e3) ?_
  set τ3 := (τ2.setv (Y 108) 0).seth O (τ2.sh O - ((marks hdr).length + 2 * out.length + 1)) with hτ3
  have v3 : τ3.val (Y 109) = out.length := by
    simp [hτ3, hτ2, hτ1, Function.update_of_ne (Y.injective.ne (show (109 : Fin 112) ≠ 108 by decide)),
      Function.update_of_ne (Y.injective.ne (show (109 : Fin 112) ≠ 104 by decide)), h109]
  have e4 := wrewind_spec (cap := cap) (Z 34) (Y 109) _ τ3 v3 (by rw [v3]; omega)
  refine Runs.of (WXExec.wm e4) ?_
  have sh34 : τ3.sh (Z 34) = out.length := by
    simp [hτ3, hτ2, hτ1, Function.update_of_ne n34]
  have shO : τ2.sh O = (marks hdr).length + 2 * out.length + 1 := by
    simp [hτ2, hτ1, Function.update_of_ne n34.symm, hOh]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hτ3, hτ2, hτ1, Function.update_of_ne n34.symm, hOs, frame_eq_marks, Streaming.marks_append]
  · simp [hτ3, Function.update_of_ne n34.symm, shO]
  · simp [hτ3, hτ2, hτ1, Function.update_of_ne n34, Function.update_of_ne n34.symm]
  · simp [sh34]
  · simp [hτ3, hτ2, hτ1, Function.update_of_ne (Y.injective.ne (show (104 : Fin 112) ≠ 109 by decide)),
      Function.update_of_ne (Y.injective.ne (show (104 : Fin 112) ≠ 108 by decide))]
  · simp [hτ3, Function.update_of_ne (Y.injective.ne (show (108 : Fin 112) ≠ 109 by decide))]
  · simp
  · refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [hτ3, hτ2, hτ1]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [hτ3, hτ2, hτ1, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hτ3, hτ2, hτ1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2]

theorem srcP_spec (cap W s k : ℕ) (O : Fin (ns + 1)) (hO : ∀ i, O ≠ Z i) (xs : List ℕ) (out L0 : List Bool)
    (g d p : ℕ) (odd : Bool) (σ : WState ns nr) (h : CutRest Z Y cap W s k xs out L0 g 0 σ)
    (hOs : σ.st O = []) (hOh : σ.sh O = 0) (h104 : σ.val (Y 104) = 0) (h108 : σ.val (Y 108) = 0)
    (h109 : σ.val (Y 109) = 0) (h105 : σ.val (Y 105) = d) (h106 : σ.val (Y 106) = p)
    (h107 : σ.val (Y 107) = odd.toNat)
    (hcap : 2 * out.length + 10 * (d + p + g) + 2 * (marks (srcHdr d p g odd)).length + 40 ≤ cap) :
    Runs cap (srcP Z Y O) σ (srcHeadCost out.length d p g + 1 +
        srcTailCost out.length ((marks (srcHdr d p g odd)).length + 2 * out.length + 1)) (fun τ =>
      τ.st O = frame (srcHdr d p g odd ++ out) ∧ τ.sh O = 0 ∧ τ.sh (Z 34) = 0 ∧ τ.val (Y 56) = 0 ∧
      SameExcept σ τ [O, Z 34] [Y 56]) := by
  refine Runs.seq (srcHead_spec Z Y cap W s k O hO xs out L0 g d p odd σ h hOs hOh h104 h108 h109 h105 h106 h107
    hcap) fun τ ⟨a1, a2, a3, ⟨j, a4⟩, a5, a6, a7, a8, f1⟩ => ?_
  refine (srcTail_spec Z Y cap O hO out j (srcHdr d p g odd) τ a1 a2 a3 a4 a5 a6 a7 (by omega)).post
    fun ρ ⟨b1, b2, b3, b4, b5, b6, b7, f2⟩ => ⟨b1, b2, b4, ?_, ?_⟩
  · have hn : Y 56 ∉ [Y 104, Y 108, Y 109] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨Y.injective.ne (by decide), Y.injective.ne (by decide), Y.injective.ne (by decide)⟩
    rw [f2.val hn]; exact a8
  · refine ⟨fun x hx => ?_, fun r hr => ?_, by rw [f2.2.2, f1.2.2]⟩
    · rw [f2.st hx, f2.sh hx]; exact f1.1 x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      by_cases a : r = Y 104
      · subst a; rw [b5]; exact h104.symm
      · by_cases b : r = Y 108
        · subst b; rw [b6]; exact h108.symm
        · by_cases c : r = Y 109
          · subst c; rw [b7]; exact h109.symm
          · rw [f2.val (by simp [a, b, c])]; exact f1.2.1 r (by simp [a, b, c, hr])

/-! ## The source of the printer request -/

theorem srcHdr_source (r : EquationRow.Input) :
    srcHdr r.d r.p r.cuts.length r.odd ++ EquationRowCuts.stream r.p r.cuts = EquationRowRaw.source r := by
  simp [srcHdr, EquationRowRaw.source, EquationHeaderRead.word, EquationHeaderRead.header, List.append_assoc]

theorem stream_allCuts {n k s G V : ℕ} (T : Tabulation n k s G V) (Wd : ℕ) :
    EquationRowCuts.stream Wd T.exactCuts = allCuts Wd s (hList (code T)) (code T).terms := by
  have e := allCuts_code Wd (code T)
  change allCuts Wd s (hList (code T)) (code T).terms = _ at e
  rw [e, ← exactCuts_fields]
  unfold EquationRowCuts.stream
  rw [List.flatMap_map]
  congr 1; funext c
  unfold MatrixScoreBatch.cutWord fieldRec
  congr 1; funext z
  rw [SInt.signMagnitude_eq]

theorem count_allCount {n k s G V : ℕ} (T : Tabulation n k s G V) :
    T.exactCuts.length = allCount (hList (code T)) (code T).terms := by
  rw [allCount_code, ← exactCuts_fields, List.length_map]

end Source

end NearCubicGates.Close.TabMachine
