import Proof.Gates.CellsSys.CallE

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (cellN bitN)

section P
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ)

/-- The point `(a, b)` of the box. -/
def ptAB (a b : ℕ) : Role c → ℤ := ptOf c p wt y κ ([a, b].take (roleCount c.kind))

theorem ptAB_0 (a b : ℕ) : ptAB c p wt y κ a b ⟨0, roleCount_pos _⟩ = loR c p wt y κ 0 + a := by
  have h := congrArg (fun l => l.getD 0 0) (ofFn_ptOf c p wt y κ a b)
  rw [List.getD_eq_getElem _ _ (by simp; exact roleCount_pos _), List.getElem_ofFn] at h
  rw [ptAB, h]; simp

theorem ptAB_1 (a b : ℕ) (h1 : 1 < roleCount c.kind) : ptAB c p wt y κ a b ⟨1, h1⟩ = loR c p wt y κ 1 + b := by
  have h := congrArg (fun l => l.getD 1 0) (ofFn_ptOf c p wt y κ a b)
  rw [List.getD_eq_getElem _ _ (by simp; exact h1), List.getElem_ofFn] at h
  rw [ptAB, h]; simp [h1]

theorem lo_le_pt (r : ℕ) (hr : r < roleCount c.kind) (a' : ℕ) (ha : a' < lenR c p wt y κ r) :
    -((circ c r).topWeight : ℤ) ≤ loR c p wt y κ r + a' ∧ loR c p wt y κ r + a' ≤ (circ c r).topWeight := by
  unfold lenR at ha; unfold loR
  rw [dif_pos hr] at ha ⊢
  have h1 := boxLo_ge c p wt y κ ⟨r, hr⟩
  have h2 := boxHi_le c p wt y κ ⟨r, hr⟩
  simp only at h1 h2
  omega

/-- The table bit of role `r` at the coordinate `lo_r + a'`. -/
theorem bit_eq {T : ℕ} (r : ℕ) (hr : r < roleCount c.kind)
    (hT : (cellN c p wt).drop T = (circ c r).table.map bitN ++ (cellN c p wt).drop (T + (circ c r).table.length))
    (hwf : (circ c r).table.length = 2 * (circ c r).topWeight + 1) (a' : ℕ) (ha : a' < lenR c p wt y κ r) :
    (loR c p wt y κ r).toNat + 0 ≤ (loR c p wt y κ r).toNat ∧
    (-loR c p wt y κ r).toNat ≤ T + (circ c r).topWeight + (loR c p wt y κ r).toNat + a' ∧
    T + (circ c r).topWeight + (loR c p wt y κ r).toNat + a' - (-loR c p wt y κ r).toNat < (cellN c p wt).length ∧
    (cellN c p wt).getD (T + (circ c r).topWeight + (loR c p wt y κ r).toNat + a' - (-loR c p wt y κ r).toNat) 0 =
      bitN (topLookup (circ c r) (loR c p wt y κ r + a')) := by
  obtain ⟨h1, h2⟩ := lo_le_pt c p wt y κ r hr a' ha
  set W := (circ c r).topWeight
  set X := (loR c p wt y κ r).toNat
  set Y := (-loR c p wt y κ r).toNat
  have hXY : (X : ℤ) - Y = loR c p wt y κ r := by simp only [X, Y]; omega
  have hY : Y ≤ W + X + a' := by omega
  have hidx : W + X + a' - Y < ((circ c r).table.map bitN).length := by rw [List.length_map, hwf]; omega
  obtain ⟨g1, g2⟩ := drop_getD hT (W + X + a' - Y) hidx
  have e : T + W + X + a' - Y = T + (W + X + a' - Y) := by omega
  refine ⟨le_rfl, by omega, by rw [e]; exact g2, ?_⟩
  rw [e, g1]
  have hlt : W + X + a' - Y < (circ c r).table.length := by rw [hwf]; omega
  rw [List.getD_eq_getElem _ _ hidx, List.getElem_map]
  unfold topLookup
  have : (loR c p wt y κ r + a' + (W : ℤ)).toNat = W + X + a' - Y := by omega
  rw [this, List.getD_eq_getElem _ _ hlt]

end P

theorem bitN_le (B : Bool) : bitN B ≤ 1 := by cases B <;> simp [bitN]

end NearCubicGates.Close.Cells.SystemsPhase
