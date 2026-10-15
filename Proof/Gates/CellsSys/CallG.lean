import Proof.Gates.CellsSys.CallF

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

theorem bitN_mod (B : Bool) : (bitN B % 2 = 1) = (B = true) := by cases B <;> simp [bitN]

theorem predW_eq (part : Option Bool) (hpart : part ∈ parts c) (a b : ℕ) (ha : a < lenR c p wt y κ 0)
    (hb : b < lenR c p wt y κ 1) {T0 T1 : ℕ}
    (hT0 : (cellN c p wt).drop T0 = (circ c 0).table.map bitN ++ (cellN c p wt).drop (T0 + (circ c 0).table.length))
    (hT1 : (cellN c p wt).drop T1 = (circ c 1).table.map bitN ++ (cellN c p wt).drop (T1 + (circ c 1).table.length))
    (hwf0 : (circ c 0).table.length = 2 * (circ c 0).topWeight + 1)
    (hwf1 : (circ c 1).table.length = 2 * (circ c 1).topWeight + 1) :
    predW c wt y part (ptAB c p wt y κ a b) =
      if pbf (cellN c p wt) (kindTag c.kind) (if outerParity c wt y then 1 else 0) (if part = some true then 1 else 0)
        (loR c p wt y κ 0).toNat (-loR c p wt y κ 0).toNat (loR c p wt y κ 1).toNat (-loR c p wt y κ 1).toNat
        T0 (circ c 0).topWeight T1 (circ c 1).topWeight a b = 1 then 1 else 0 := by
  have hrc0 := roleCount_pos c.kind
  have e0 := (bit_eq c p wt y κ 0 hrc0 hT0 hwf0 a ha).2.2.2
  have hc0 : coord0 (ptAB c p wt y κ a b) = loR c p wt y κ 0 + a := ptAB_0 c p wt y κ a b
  unfold predW pbf b0f
  rw [e0]
  have hcirc0 : circ c 0 = c.first := by simp [circ]
  have hcirc1 : circ c 1 = c.second := by simp [circ]
  rcases hk : c.kind with _ | _ | _
  · -- single
    simp only [scorePredicate, hk, hc0, hcirc0, kindTag]
    cases topLookup c.first (loR c p wt y κ 0 + ↑a) <;> simp [bitN]
  · -- pair
    have h2 : 1 < roleCount c.kind := by rw [hk]; decide
    have e1 := (bit_eq c p wt y κ 1 h2 hT1 hwf1 b hb).2.2.2
    have hc1 : coord1 (ptAB c p wt y κ a b) = loR c p wt y κ 1 + b := by
      unfold coord1; rw [dif_pos h2]; exact ptAB_1 c p wt y κ a b h2
    rw [e1]
    simp only [scorePredicate, hk, hc0, hc1, hcirc0, hcirc1, kindTag]
    cases topLookup c.first (loR c p wt y κ 0 + ↑a) <;> cases topLookup c.second (loR c p wt y κ 1 + ↑b) <;>
      simp [bitN]
  · -- parity
    have hp : part = some false ∨ part = some true := by
      simp [parts, hk] at hpart; exact hpart
    simp only [scorePredicate, hk, hc0, hcirc0, kindTag]
    rcases hp with rfl | rfl <;> cases topLookup c.first (loR c p wt y κ 0 + ↑a) <;>
      cases outerParity c wt y <;> simp [bitN]

end P

end NearCubicGates.Close.Cells.SystemsPhase
