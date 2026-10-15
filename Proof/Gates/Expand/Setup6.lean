import Proof.Gates.Expand.Setup5

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

theorem setv_setv' (σ : WState NS NR) (r : Fin NR) (a b : ℕ) : (σ.setv r a).setv r b = σ.setv r b := by
  apply WState.eq <;> simp

theorem clrR_spec (cap : ℕ) (r : Fin NR) (σ : WState NS NR) (hcap : σ.val r ≤ cap) :
    WXExec cap (clrR r) σ (σ.setv r 0) (σ.val r * (1 + 2) + 1) := by
  obtain ⟨τ, e, hτ⟩ := Runs.whr (cap := cap) (r := r) (P := WMX.dec r)
    (fun k τ => k ≤ σ.val r ∧ τ = σ.setv r k) 1 (fun τ => τ = σ.setv r 0)
    (fun τ ⟨_, h⟩ => ⟨by rw [h]; simp, h⟩)
    (fun k τ ⟨hk, h⟩ => ⟨by rw [h]; simp, Runs.of (WXExec.dec cap r τ (by rw [h]; simp; omega))
      ⟨by omega, by rw [h]; simp [setv_setv']⟩⟩)
    (σ.val r) σ ⟨le_rfl, by rw [wsetv_same]⟩
  rw [hτ] at e; exact e

/-! ## Register steps as postconditions -/

theorem rIncR (cap : ℕ) (r : Fin NR) (τ : WState NS NR) (h : τ.val r < cap) :
    Runs cap (WMX.inc r) τ 3 (fun ρ => SameExcept τ ρ [] [r] ∧ ρ.val r = τ.val r + 1) :=
  Runs.of (WXExec.inc cap r τ h) ⟨sameExcept_setv τ (by simp) _, by simp⟩

theorem rClrR (cap : ℕ) (r : Fin NR) (τ : WState NS NR) (h : τ.val r ≤ cap) :
    Runs cap (clrR r) τ (τ.val r * (1 + 2) + 1) (fun ρ => SameExcept τ ρ [] [r] ∧ ρ.val r = 0) :=
  Runs.of (clrR_spec cap r τ h) ⟨sameExcept_setv τ (by simp) _, by simp⟩

theorem rAddR (cap : ℕ) {A B T : Fin NR} (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T) (τ : WState NS NR)
    (hT : τ.val T = 0) (h : τ.val B + τ.val A ≤ cap) :
    Runs cap (addR A B T) τ (18 * τ.val A + 3) (fun ρ => SameExcept τ ρ [] [B] ∧ ρ.val B = τ.val B + τ.val A) :=
  Runs.of (addR_spec cap hAB hAT hBT τ hT h) ⟨sameExcept_setv τ (by simp) _, by simp⟩

theorem rMulR (cap : ℕ) {A A2 B C T : Fin NR} (hR : [A, A2, B, C, T].Nodup) (τ : WState NS NR)
    (hA2 : τ.val A2 = 0) (hT : τ.val T = 0) (h : τ.val C + τ.val A * τ.val B ≤ cap) (hA : 2 * τ.val A ≤ cap) :
    Runs cap (mulR A A2 B C T) τ (τ.val A * (18 * τ.val B + 3 + 8) + 7 * τ.val A + 3)
      (fun ρ => SameExcept τ ρ [] [C] ∧ ρ.val C = τ.val C + τ.val A * τ.val B) :=
  Runs.of (mulR_spec cap hR τ hA2 hT h hA) ⟨sameExcept_setv τ (by simp) _, by simp⟩

def regB1 : WMX NS NR :=
  .seq (WMX.inc (GR 1)) (.seq (WMX.inc (GR 1)) (.seq (clrR (GR 2)) (.seq (WMX.inc (GR 3))
    (.seq (addR (GR 1) (GR 3) (GR 7)) (mulR (GR 3) (GR 5) (GR 4) (GR 2) (GR 7))))))

def regB2 : WMX NS NR :=
  .seq (clrR (GR 3)) (.seq (addR (RF 8) (GR 3) (GR 7)) (.seq (WMX.inc (GR 3))
    (.seq (mulR (GR 3) (GR 5) (RF 10) (GR 2) (GR 7)) (.seq (addR (RF 8) (GR 2) (GR 7)) (.seq (WMX.inc (GR 2))
      (.seq (WMX.inc (GR 2)) (.seq (WMX.inc (GR 2)) (WMX.inc (GR 2)))))))))

def regB : WMX NS NR := .seq regB1 regB2

/-- The second width. -/
def wb2 (W L V D : ℕ) : ℕ := (W + L + 2) * (L + 2) + V * (D + 1) + D + 4

def regB1Cost (wt L : ℕ) : ℕ :=
  3 + 1 + (3 + 1 + (((L + 2) * (L + 2) * (1 + 2) + 1) + 1 + (3 + 1 + ((18 * (wt + 2) + 3) + 1 +
    ((wt + 2 + L + 2) * (18 * (L + 2) + 3 + 8) + 7 * (wt + 2 + L + 2) + 3)))))

def regB2Cost (wt L V D : ℕ) : ℕ :=
  ((wt + 2 + L + 2) * (1 + 2) + 1) + 1 + ((18 * D + 3) + 1 + (3 + 1 + (((D + 1) * (18 * V + 3 + 8) + 7 * (D + 1) + 3)
    + 1 + ((18 * D + 3) + 1 + (3 + 1 + (3 + 1 + (3 + 1 + 3)))))))

def regBCost (wt L V D : ℕ) : ℕ := regB1Cost wt L + 1 + regB2Cost wt L V D

theorem gr_ne_rf (i : Fin 8) (j : Fin 14) : GR i ≠ RF j := rne (by have := i.isLt; have := j.isLt; simp; omega)

theorem regB1_spec (cap wt L : ℕ) (σ : WState NS NR) (h1 : σ.val (GR 1) = wt)
    (h2 : σ.val (GR 2) = (L + 2) * (L + 2)) (h3 : σ.val (GR 3) = L + 1) (h4 : σ.val (GR 4) = L + 2)
    (h5 : σ.val (GR 5) = 0) (h7 : σ.val (GR 7) = 0)
    (hcap : 2 * ((wt + 2 + L + 2) * (L + 2)) + 2 * (wt + 2 + L + 2) + (L + 2) * (L + 2) ≤ cap) :
    Runs cap regB1 σ (regB1Cost wt L) (fun τ => SameExcept σ τ [] [GR 1, GR 2, GR 3] ∧
      τ.val (GR 1) = wt + 2 ∧ τ.val (GR 2) = (wt + 2 + L + 2) * (L + 2) ∧ τ.val (GR 3) = wt + 2 + L + 2) := by
  refine Runs.seq (rIncR cap (GR 1) σ (by rw [h1]; nlinarith)) (fun τ1 ⟨f1, v1⟩ => ?_)
  refine Runs.seq (rIncR cap (GR 1) τ1 (by rw [v1, h1]; nlinarith)) (fun τ2 ⟨f2, v2⟩ => ?_)
  have u22 : τ2.val (GR 2) = (L + 2) * (L + 2) := by rw [f2.val (by simp), f1.val (by simp), h2]
  refine Runs.seq ((rClrR cap (GR 2) τ2 (by rw [u22]; omega)).cost (le_of_eq (by rw [u22])))
    (fun τ3 ⟨f3, v3⟩ => ?_)
  have u33 : τ3.val (GR 3) = L + 1 := by rw [f3.val (by simp), f2.val (by simp), f1.val (by simp), h3]
  refine Runs.seq (rIncR cap (GR 3) τ3 (by rw [u33]; nlinarith)) (fun τ4 ⟨f4, v4⟩ => ?_)
  have u41 : τ4.val (GR 1) = wt + 2 := by rw [f4.val (by simp), f3.val (by simp), v2, v1, h1]
  have u43 : τ4.val (GR 3) = L + 2 := by rw [v4, u33]
  have u47 : τ4.val (GR 7) = 0 := by
    rw [f4.val (by simp), f3.val (by simp), f2.val (by simp), f1.val (by simp), h7]
  refine Runs.seq ((rAddR cap (A := GR 1) (B := GR 3) (T := GR 7) (grN (by decide)) (grN (by decide))
    (grN (by decide)) τ4 u47 (by rw [u41, u43]; nlinarith)).cost (le_of_eq (by rw [u41]))) (fun τ5 ⟨f5, v5⟩ => ?_)
  have u53 : τ5.val (GR 3) = wt + 2 + L + 2 := by rw [v5, u41, u43]; ring
  have u52 : τ5.val (GR 2) = 0 := by rw [f5.val (by simp), f4.val (by simp), v3]
  have u54 : τ5.val (GR 4) = L + 2 := by
    rw [f5.val (by simp), f4.val (by simp), f3.val (by simp), f2.val (by simp), f1.val (by simp), h4]
  have u55 : τ5.val (GR 5) = 0 := by
    rw [f5.val (by simp), f4.val (by simp), f3.val (by simp), f2.val (by simp), f1.val (by simp), h5]
  have u57 : τ5.val (GR 7) = 0 := by rw [f5.val (by simp), u47]
  refine ((rMulR cap (A := GR 3) (A2 := GR 5) (B := GR 4) (C := GR 2) (T := GR 7) (by decide) τ5 u55 u57
    (by rw [u52, u53, u54]; nlinarith) (by rw [u53]; nlinarith)).cost (le_of_eq (by rw [u53, u54]))).post
    (fun τ6 ⟨f6, v6⟩ => ⟨?_, ?_, ?_, ?_⟩)
  · refine ⟨fun x _ => ?_, fun q hq => ?_, ?_⟩
    · exact ⟨by rw [f6.st (by simp), f5.st (by simp), f4.st (by simp), f3.st (by simp), f2.st (by simp),
        f1.st (by simp)], by rw [f6.sh (by simp), f5.sh (by simp), f4.sh (by simp), f3.sh (by simp), f2.sh (by simp),
        f1.sh (by simp)]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      rw [f6.val (by simp [hq.2.1]), f5.val (by simp [hq.2.2]), f4.val (by simp [hq.2.2]), f3.val (by simp [hq.2.1]),
        f2.val (by simp [hq.1]), f1.val (by simp [hq.1])]
    · rw [f6.cell, f5.cell, f4.cell, f3.cell, f2.cell, f1.cell]
  · rw [f6.val (by simp), f5.val (by simp), u41]
  · rw [v6, u52, u53, u54]; ring
  · rw [f6.val (by simp), u53]

theorem regB2_spec (cap wt L V D : ℕ) (σ : WState NS NR) (h2 : σ.val (GR 2) = (wt + 2 + L + 2) * (L + 2))
    (h3 : σ.val (GR 3) = wt + 2 + L + 2) (h5 : σ.val (GR 5) = 0) (h7 : σ.val (GR 7) = 0) (hD : σ.val (RF 8) = D)
    (hV : σ.val (RF 10) = V) (hcap : 2 * wb2 (wt + 2) L V D + 2 * (wt + 2 + L + 2) + 2 * (D + 1) ≤ cap) :
    Runs cap regB2 σ (regB2Cost wt L V D) (fun τ => SameExcept σ τ [] [GR 2, GR 3] ∧
      τ.val (GR 2) = wb2 (wt + 2) L V D ∧ τ.val (GR 3) = D + 1) := by
  have hW1 : wb2 (wt + 2) L V D = (wt + 2 + L + 2) * (L + 2) + (D + 1) * V + D + 4 := by unfold wb2; ring
  refine Runs.seq ((rClrR cap (GR 3) σ (by rw [h3]; omega)).cost (le_of_eq (by rw [h3]))) (fun τ1 ⟨f1, v1⟩ => ?_)
  have u1D : τ1.val (RF 8) = D := by rw [f1.val (by simp [(gr_ne_rf 3 8).symm]), hD]
  have u17 : τ1.val (GR 7) = 0 := by rw [f1.val (by simp), h7]
  refine Runs.seq ((rAddR cap (A := RF 8) (B := GR 3) (T := GR 7) (gr_ne_rf 3 8).symm (gr_ne_rf 7 8).symm
    (grN (by decide)) τ1 u17 (by rw [u1D, v1]; omega)).cost (le_of_eq (by rw [u1D]))) (fun τ2 ⟨f2, v2⟩ => ?_)
  refine Runs.seq (rIncR cap (GR 3) τ2 (by rw [v2, v1, u1D]; omega)) (fun τ3 ⟨f3, v3⟩ => ?_)
  have u33 : τ3.val (GR 3) = D + 1 := by rw [v3, v2, v1, u1D]; omega
  have u32 : τ3.val (GR 2) = (wt + 2 + L + 2) * (L + 2) := by
    rw [f3.val (by simp), f2.val (by simp), f1.val (by simp), h2]
  have u35 : τ3.val (GR 5) = 0 := by rw [f3.val (by simp), f2.val (by simp), f1.val (by simp), h5]
  have u37 : τ3.val (GR 7) = 0 := by rw [f3.val (by simp), f2.val (by simp), u17]
  have u3V : τ3.val (RF 10) = V := by
    rw [f3.val (by simp [(gr_ne_rf 3 10).symm]), f2.val (by simp [(gr_ne_rf 3 10).symm]),
      f1.val (by simp [(gr_ne_rf 3 10).symm]), hV]
  refine Runs.seq ((rMulR cap (A := GR 3) (A2 := GR 5) (B := RF 10) (C := GR 2) (T := GR 7)
    (by simp [List.nodup_cons, gr_ne_rf, (gr_ne_rf _ _).symm, Fin.ext_iff]) τ3 u35 u37
    (by rw [u32, u33, u3V]; omega) (by rw [u33]; omega)).cost (le_of_eq (by rw [u33, u3V])))
    (fun τ4 ⟨f4, v4⟩ => ?_)
  have u42 : τ4.val (GR 2) = (wt + 2 + L + 2) * (L + 2) + (D + 1) * V := by rw [v4, u32, u33, u3V]
  have u4D : τ4.val (RF 8) = D := by
    rw [f4.val (by simp [(gr_ne_rf 2 8).symm]), f3.val (by simp [(gr_ne_rf 3 8).symm]),
      f2.val (by simp [(gr_ne_rf 3 8).symm]), u1D]
  have u47 : τ4.val (GR 7) = 0 := by rw [f4.val (by simp), u37]
  refine Runs.seq ((rAddR cap (A := RF 8) (B := GR 2) (T := GR 7) (gr_ne_rf 2 8).symm (gr_ne_rf 7 8).symm
    (grN (by decide)) τ4 u47 (by rw [u42, u4D]; omega)).cost (le_of_eq (by rw [u4D]))) (fun τ5 ⟨f5, v5⟩ => ?_)
  have u52 : τ5.val (GR 2) = (wt + 2 + L + 2) * (L + 2) + (D + 1) * V + D := by rw [v5, u42, u4D]
  refine Runs.seq (rIncR cap (GR 2) τ5 (by rw [u52]; omega)) (fun τ6 ⟨f6, v6⟩ => ?_)
  refine Runs.seq (rIncR cap (GR 2) τ6 (by rw [v6, u52]; omega)) (fun τ7 ⟨f7, v7⟩ => ?_)
  refine Runs.seq (rIncR cap (GR 2) τ7 (by rw [v7, v6, u52]; omega)) (fun τ8 ⟨f8, v8⟩ => ?_)
  refine (rIncR cap (GR 2) τ8 (by rw [v8, v7, v6, u52]; omega)).post (fun τ9 ⟨f9, v9⟩ => ⟨?_, ?_, ?_⟩)
  · refine ⟨fun x _ => ?_, fun q hq => ?_, ?_⟩
    · exact ⟨by rw [f9.st (by simp), f8.st (by simp), f7.st (by simp), f6.st (by simp), f5.st (by simp),
        f4.st (by simp), f3.st (by simp), f2.st (by simp), f1.st (by simp)],
        by rw [f9.sh (by simp), f8.sh (by simp), f7.sh (by simp), f6.sh (by simp), f5.sh (by simp),
        f4.sh (by simp), f3.sh (by simp), f2.sh (by simp), f1.sh (by simp)]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      rw [f9.val (by simp [hq.1]), f8.val (by simp [hq.1]), f7.val (by simp [hq.1]), f6.val (by simp [hq.1]),
        f5.val (by simp [hq.1]), f4.val (by simp [hq.1]), f3.val (by simp [hq.2]), f2.val (by simp [hq.2]),
        f1.val (by simp [hq.2])]
    · rw [f9.cell, f8.cell, f7.cell, f6.cell, f5.cell, f4.cell, f3.cell, f2.cell, f1.cell]
  · rw [v9, v8, v7, v6, u52, hW1]
  · rw [f9.val (by simp), f8.val (by simp), f7.val (by simp), f6.val (by simp), f5.val (by simp),
      f4.val (by simp), u33]

end NearCubicGates.Close.Expand.Layout
