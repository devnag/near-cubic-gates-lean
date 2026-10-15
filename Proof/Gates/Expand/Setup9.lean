import Proof.Gates.Expand.Setup8

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

/-- The block values after the constants. -/
def wB (V W : ℕ) (j : Fin 53) : ℕ :=
  if j = 5 ∨ j = 34 ∨ j = 49 then 2 ^ W else if j = 6 ∨ j = 33 then 2 ^ W - 1 else
  if j = 7 ∨ j = 13 ∨ j = 35 ∨ j = 50 then 1 else if j = 14 ∨ j = 37 then 2 ^ V else
  if j = 16 ∨ j = 36 then 2 ^ V - 1 else if j = 31 then (2 ^ V - 1) * 2 ^ W else
  if j = 32 ∨ j = 48 then 2 ^ V * 2 ^ W else if j = 51 then 2 ^ (W - 1) else 0

section Consts
variable {cap Wb V W : ℕ} {σ : WState NS NR}

theorem constB3_spec {τ : WState NS NR} {w : Fin 53 → ℕ} (c : CB Wb σ τ w) (hF : σ.val F0 = 0)
    (hR : σ.val R0 = 0) (w31 : w 31 = (2 ^ V - 1) * 2 ^ W) (w32 : w 32 = 2 ^ V * 2 ^ W) (w33 : w 33 = 2 ^ W - 1)
    (w34 : w 34 = 2 ^ W) (w35 : w 35 = 1) (w36 : w 36 = 2 ^ V - 1) (w37 : w 37 = 2 ^ V) (w51 : w 51 = 2 ^ (W - 1))
    (wz : ∀ j, j ∉ ([31, 32, 33, 34, 35, 36, 37, 51] : List (Fin 53)) → w j = 0) (hcap : 2 * Wb + 1 ≤ cap) :
    Runs cap constB3 τ (constB3Cost Wb) (fun ρ => ∃ w', CB Wb σ ρ w' ∧ (∀ j, w' j = wB V W j) ∧
      SameExcept τ ρ nbList []) := by
  have hFR : F0 ≠ R0 := grN (by decide)
  refine Runs.seq (mCopy cap Wb 7 35 (by decide) hFR c.mv (c.zF hF) (c.zR hR) hcap) (fun τ1 ⟨m1, f1⟩ => ?_)
  have c1 := c.step m1 f1 (nbS 7)
  refine Runs.seq (mCopy cap Wb 5 34 (by decide) hFR c1.mv (c1.zF hF) (c1.zR hR) hcap) (fun τ2 ⟨m2, f2⟩ => ?_)
  have c2 := c1.step m2 f2 (nbS 5)
  refine Runs.seq (mCopy cap Wb 6 33 (by decide) hFR c2.mv (c2.zF hF) (c2.zR hR) hcap) (fun τ3 ⟨m3, f3⟩ => ?_)
  have c3 := c2.step m3 f3 (nbS 6)
  refine Runs.seq (mCopy cap Wb 13 35 (by decide) hFR c3.mv (c3.zF hF) (c3.zR hR) hcap) (fun τ4 ⟨m4, f4⟩ => ?_)
  have c4 := c3.step m4 f4 (nbS 13)
  refine Runs.seq (mCopy cap Wb 14 37 (by decide) hFR c4.mv (c4.zF hF) (c4.zR hR) hcap) (fun τ5 ⟨m5, f5⟩ => ?_)
  have c5 := c4.step m5 f5 (nbS 14)
  refine Runs.seq (mCopy cap Wb 16 36 (by decide) hFR c5.mv (c5.zF hF) (c5.zR hR) hcap) (fun τ6 ⟨m6, f6⟩ => ?_)
  have c6 := c5.step m6 f6 (nbS 16)
  refine Runs.seq (mCopy cap Wb 48 32 (by decide) hFR c6.mv (c6.zF hF) (c6.zR hR) hcap) (fun τ7 ⟨m7, f7⟩ => ?_)
  have c7 := c6.step m7 f7 (nbS 48)
  refine Runs.seq (mCopy cap Wb 49 34 (by decide) hFR c7.mv (c7.zF hF) (c7.zR hR) hcap) (fun τ8 ⟨m8, f8⟩ => ?_)
  have c8 := c7.step m8 f8 (nbS 49)
  refine (mCopy cap Wb 50 35 (by decide) hFR c8.mv (c8.zF hF) (c8.zR hR) hcap).post (fun τ9 ⟨m9, f9⟩ => ?_)
  have c9 := c8.step m9 f9 (nbS 50)
  refine ⟨_, c9, fun j => ?_, ?_⟩
  · have hz : ∀ j : Fin 53, j ∉ ([31, 32, 33, 34, 35, 36, 37, 51] : List (Fin 53)) → w j = 0 := wz
    fin_cases j <;> simp [wB, Function.update_apply, w31, w32, w33, w34, w35, w36, w37, w51] <;>
      first | rfl | exact hz _ (by decide)
  · have w1 := se_sub f1 (fun x hx => nbS 7 x hx) (List.Subset.refl [])
    have w2 := se_sub f2 (fun x hx => nbS 5 x hx) (List.Subset.refl [])
    have w3 := se_sub f3 (fun x hx => nbS 6 x hx) (List.Subset.refl [])
    have w4 := se_sub f4 (fun x hx => nbS 13 x hx) (List.Subset.refl [])
    have w5 := se_sub f5 (fun x hx => nbS 14 x hx) (List.Subset.refl [])
    have w6 := se_sub f6 (fun x hx => nbS 16 x hx) (List.Subset.refl [])
    have w7 := se_sub f7 (fun x hx => nbS 48 x hx) (List.Subset.refl [])
    have w8 := se_sub f8 (fun x hx => nbS 49 x hx) (List.Subset.refl [])
    have w9 := se_sub f9 (fun x hx => nbS 50 x hx) (List.Subset.refl [])
    exact (((((((w1.trans w2).trans w3).trans w4).trans w5).trans w6).trans w7).trans w8).trans w9

theorem constB_spec (D : ℕ) (h0 : MV NB Wb (fun _ => 0) σ) (hF : σ.val F0 = 0)
    (hR : σ.val R0 = 0) (h5 : σ.val (GR 5) = 0) (h3 : σ.val (GR 3) = D + 1) (hV : σ.val (RF 10) = V)
    (h1 : σ.val (GR 1) = W) (hW : 2 ≤ W) (hTW : 2 * 2 ^ V * 2 ^ W ≤ 2 ^ Wb) (hcap : 2 * Wb + 1 ≤ cap)
    (hcV : 2 * (V + W + D + 2) ≤ cap) :
    Runs cap constB σ (constBCost Wb V W D) (fun τ => CB Wb σ τ (wB V W) ∧ τ.val (GR 3) = 0) := by
  have hV0 : 0 < 2 ^ V := Nat.two_pow_pos V
  have hW0 : 4 ≤ 2 ^ W := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hVW : 2 ^ V * 2 ^ W < 2 ^ Wb := by nlinarith
  have hVb : 2 ^ V < 2 ^ Wb := by nlinarith
  refine Runs.seq (constB1_spec D h0 hF hR h5 h3 hV h1 hVb hcap hcV) (fun τ1 ⟨⟨w1, c1, a34, a35, a37, az⟩, g1⟩ => ?_)
  refine Runs.seq (constB2_spec c1 hF hR h5 a34 a35 a37 az hW hVW hcap)
    (fun τ2 ⟨w2, c2, b31, b32, b33, b34, b35, b36, b37, b51, bz, f2⟩ => ?_)
  refine (constB3_spec c2 hF hR b31 b32 b33 b34 b35 b36 b37 b51 bz hcap).post
    (fun τ3 ⟨w3, c3, e3, f3⟩ => ⟨?_, ?_⟩)
  · have : w3 = wB V W := funext e3
    rw [← this]; exact c3
  · rw [f3.val (by simp), f2.val (by simp), g1]

end Consts

end NearCubicGates.Close.Expand.Layout
