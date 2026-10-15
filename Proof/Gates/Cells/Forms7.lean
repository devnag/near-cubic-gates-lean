import Proof.Gates.Cells.Forms6

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

theorem posPart_take : ∀ (ws : List ℤ) (zs : List ℕ), posPart ws (zs.take ws.length) = posPart ws zs ∧
    negPart ws (zs.take ws.length) = negPart ws zs
  | [], zs => by cases zs <;> simp [posPart, negPart]
  | w :: ws, [] => by simp [posPart, negPart]
  | w :: ws, z :: zs => by
    have ih := posPart_take ws zs
    simp only [List.length_cons, List.take_succ_cons, posPart, negPart]
    rw [ih.1, ih.2]; exact ⟨rfl, rfl⟩

section Val
variable (c : Call) (p : Params) (wt : Wit c.n) (i : ℕ)

/-- The gate bits of role `r` on cell `i`. -/
def gbOf (r : ℕ) : List ℕ := (circ c r).gates.map (gbit · (zbL wt.I i))

theorem zy_bits : ∀ j : Fin c.n, extend wt.I (cellOf wt.I i) (zeroPoint wt.I) j =
    decide ((zbL wt.I i).getD j.val 0 = 1) := fun j => zbL_point wt.I i j

theorem zbL_length : (zbL wt.I i).length = c.n := by simp [zbL]

theorem stage_val (r s : ℕ) :
    ((kpOf wt.coef (gbOf c wt i r) r s : ℕ) : ℤ) - knOf wt.coef (gbOf c wt i r) r s =
      stageForm c wt r s (extend wt.I (cellOf wt.I i) (zeroPoint wt.I)) := by
  unfold kpOf knOf stageForm
  rw [(posPart_take _ _).1, (posPart_take _ _).2, ← wsum_parts,
    linForm_eq _ (zbL wt.I i) (zy_bits c wt i) (zbL_length c wt i)]
  rfl

theorem score_val (r : ℕ) :
    ((posPart (circ c r).coeffs (gbOf c wt i r) : ℕ) : ℤ) - negPart (circ c r).coeffs (gbOf c wt i r) =
      scoreForm c r (extend wt.I (cellOf wt.I i) (zeroPoint wt.I)) := by
  unfold scoreForm
  rw [← wsum_parts, score_eq_linForm, linForm_eq _ (zbL wt.I i) (zy_bits c wt i) (zbL_length c wt i)]
  rfl

theorem eVal_eq (r : Role c) (j : ℕ) :
    eVal (kpOf wt.coef (gbOf c wt i r.val) r.val) (knOf wt.coef (gbOf c wt i r.val) r.val) p.factors j =
      digit c p wt r.val j (extend wt.I (cellOf wt.I i) (zeroPoint wt.I)) := by
  unfold eVal digit
  congr 1
  funext s
  exact stage_val c wt i r.val s

theorem flatMap_finRange {α : Type} (J : ℕ) (g : ℕ → List α) :
    (List.finRange J).flatMap (fun j : Fin J => g j.val) = (List.range J).flatMap g := by
  have h : (List.finRange J).map Fin.val = List.range J := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  rw [← h, List.flatMap_map]

/-- **The role's digit-centre pairs are its segment of `ctrL`.** -/
theorem ePairs_eq (r : Role c) :
    ePairs (kpOf wt.coef (gbOf c wt i r.val) r.val) (knOf wt.coef (gbOf c wt i r.val) r.val) p.factors p.J =
      (List.finRange p.J).flatMap fun j => pairOf (ctr c p wt (cellOf wt.I i) (r, j)) := by
  unfold ePairs
  rw [← flatMap_finRange p.J (fun j => pairOf (eVal (kpOf wt.coef (gbOf c wt i r.val) r.val)
    (knOf wt.coef (gbOf c wt i r.val) r.val) p.factors j))]
  congr 1
  funext j
  rw [eVal_eq]; rfl

/-- **The role's `sX` entries are its segment of `kxL`.** -/
theorem kx_eq (r : Role c) (hJ : 1 ≤ p.J) :
    pairOf ((prevV (kpOf wt.coef (gbOf c wt i r.val) r.val) p.J : ℤ) -
        prevV (knOf wt.coef (gbOf c wt i r.val) r.val) p.J) ++
      pairOf ((posPart (circ c r.val).coeffs (gbOf c wt i r.val) : ℤ) -
        negPart (circ c r.val).coeffs (gbOf c wt i r.val)) =
    pairOf (stageForm c wt r.val (p.J - 1) (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))) ++
      pairOf (scoreForm c r.val (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))) := by
  have h0 : p.J ≠ 0 := by omega
  simp only [prevV, h0, if_false]
  rw [stage_val, score_val]

end Val

end NearCubicGates.Close.Cells
