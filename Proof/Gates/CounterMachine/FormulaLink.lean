import Proof.Gates.CounterMachine.FormulaMom

/-! # RG machine, part 19: the printed tokens are the requested formulas

`fdata c p wt q ρs`: the formula printer's data for a call (per role the gates' count, the stage coefficient lists of
the witness, the top coefficients; the rates followed by `M₁`, `A`; the residues `ρs = κ ++ σ`). **`tToks_link`**:
the residue printer's tokens are `toks` of table (a)'s formula `resFormula c p wt q κ σ` (lem:residue-count, v2
1503–1529). **`mdToks_link`**, **`mpToks_link`**: the moment printers' tokens are `toks` of table (b)'s formulas
(1660–1672). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

theorem digToks_congr (o : ℕ) (A A' : ℕ → List ℤ) (rate rate' : ℕ → ℤ) (j : ℕ) (hA : ∀ s ≤ j, A s = A' s)
    (hr : ∀ i < j, rate i = rate' i) : digToks o A rate j = digToks o A' rate' j := by
  cases j with
  | zero => simp [digToks, hA 0 le_rfl]
  | succ j => simp [digToks, hA (j + 1) le_rfl, hA j (by omega), hr j (by omega)]

section Link
variable (c : Call) (p : Params) (wt : Wit c.n)

/-- The formula printer's data of a call and a residue vector. -/
def fdata (q : ℕ) (ρs : List ℕ) : FData where
  pair := decide (c.kind = .pair)
  J := p.J
  q := q
  e := p.e
  k := p.k
  G0 := c.first.gates.length
  G1 := c.second.gates.length
  B0 := (List.range p.J).map fun s => wt.coef s 0
  B1 := (List.range p.J).map fun s => wt.coef s 1
  C0 := c.first.coeffs
  C1 := c.second.coeffs
  L := p.factors ++ [p.M1, p.A]
  ρs := ρs
  M1 := p.M1
  A := p.A

theorem fdata_rc (q : ℕ) (ρs : List ℕ) : (fdata c p wt q ρs).rc = roleCount c.kind := by
  unfold FData.rc fdata roleCount; cases c.kind <;> simp

theorem getD_B (r s : ℕ) (hs : s < p.J) :
    ((List.range p.J).map fun s => wt.coef s r).getD s [] = wt.coef s r := by
  rw [List.getD_eq_getElem _ _ (by simpa using hs)]; simp

theorem getD_L (hL : p.factors.length = p.J - 1) (i : ℕ) (hi : i < p.J - 1) :
    ((p.factors ++ [p.M1, p.A]).getD i 0 : ℤ) = rateOf p i := by
  unfold rateOf; rw [List.getD_append _ _ _ _ (by omega)]

theorem digFacs_link (hL : p.factors.length = p.J - 1) (o base q r : ℕ) (ρs : List ℕ) :
    digFacs o base q p.J ((List.range p.J).map fun s => wt.coef s r) (p.factors ++ [p.M1, p.A]) ρs =
      (List.range p.J).map fun j => facToks (digToks o (fun s => wt.coef s r) (rateOf p) j)
        (ρs.getD (base + j) 0 : ℤ) q := by
  unfold digFacs
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  rw [digToks_congr o _ (fun s => wt.coef s r) _ (rateOf p) j (fun s hs => getD_B c p wt r s (by omega))
    (fun i hi => getD_L p hL i (by omega))]

/-- **The residue printer prints table (a)'s formula.** -/
theorem tToks_link (hL : p.factors.length = p.J - 1) (q : ℕ) (κ σ : List ℕ)
    (hκ : κ.length = roleCount c.kind * p.J) (hok : CoefOK c p wt) :
    toks (resFormula c p wt q κ σ) = ampToks p.e (tToks (fdata c p wt q (κ ++ σ))) := by
  rw [toks_resFormula c p wt q κ σ hκ hok]
  congr 2
  unfold tFacs resFacs
  rw [fdata_rc]
  simp only [fdata]
  rw [digFacs_link c p wt hL 0 0 q 0, digFacs_link c p wt hL _ p.J q 1]
  cases hk : c.kind with
  | pair =>
    simp only [roleCount, decide_true, if_true]
    simp [List.range_succ, offR, circ, List.flatMap_append, List.append_assoc]
  | single =>
    simp only [roleCount, decide_false, if_false, reduceCtorEq]
    simp [offR, circ, List.append_assoc]
  | parity =>
    simp only [roleCount, decide_false, if_false, reduceCtorEq]
    simp [offR, circ, List.append_assoc]

@[simp] theorem fdata_J (q : ℕ) (ρs : List ℕ) : (fdata c p wt q ρs).J = p.J := rfl
@[simp] theorem fdata_k (q : ℕ) (ρs : List ℕ) : (fdata c p wt q ρs).k = p.k := rfl

theorem fdata_Br (q : ℕ) (ρs : List ℕ) (r : ℕ) (hr : r < 2) :
    (fdata c p wt q ρs).Br r = (List.range p.J).map fun s => wt.coef s r := by
  unfold FData.Br fdata; rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> simp

theorem fdata_Gr (q : ℕ) (ρs : List ℕ) (r : ℕ) (hr : r < 2) : (fdata c p wt q ρs).Gr r = (circ c r).gates.length := by
  unfold FData.Gr fdata circ; rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> simp

theorem fdata_Cr (q : ℕ) (ρs : List ℕ) (r : ℕ) (hr : r < 2) : (fdata c p wt q ρs).Cr r = (circ c r).coeffs := by
  unfold FData.Cr fdata circ; rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> simp

/-- **The digit-moment printer prints table (b)'s formula.** -/
theorem mdToks_link (hL : p.factors.length = p.J - 1) (q : ℕ) (ρs : List ℕ) (r j : ℕ) (hr : r < 2) (hj : j < p.J) :
    momToks c p wt r (some j) = mdToks (fdata c p wt q ρs) r j := by
  simp only [momToks, mdToks, fdata_k]
  rw [fdata_Br c p wt q ρs r hr, fdata_Gr c p wt q ρs r hr]
  have hd : ∀ o, digToks o (fun s => wt.coef s r) (rateOf p) j =
      digToks o (fun s => ((List.range p.J).map fun s => wt.coef s r).getD s [])
        (fun i => ((fdata c p wt q ρs).L.getD i 0 : ℤ)) j := fun o =>
    digToks_congr o _ _ _ _ j (fun s hs => (getD_B c p wt r s (by omega)).symm)
      (fun i hi => (getD_L p hL i (by omega)).symm)
  rw [hd 0, hd]

/-- **The `Φ`-moment printer prints table (b)'s formula.** -/
theorem mpToks_link (hL : p.factors.length = p.J - 1) (hJ : 1 ≤ p.J) (q : ℕ) (ρs : List ℕ) (r : ℕ) (hr : r < 2) :
    momToks c p wt r none = mpToks (fdata c p wt q ρs) r := by
  simp only [momToks, mpToks, phToks, phiToks, fdata_J, fdata_k]
  rw [fdata_Br c p wt q ρs r hr, fdata_Gr c p wt q ρs r hr, fdata_Cr c p wt q ρs r hr,
    getD_B c p wt r (p.J - 1) (by omega)]
  have h1 : (fdata c p wt q ρs).L.getD (p.J - 1) 0 = p.M1 := by
    simp only [fdata]; rw [List.getD_append_right _ _ _ _ (by omega), hL]; simp
  have h2 : (fdata c p wt q ρs).L.getD p.J 0 = p.A := by
    simp only [fdata]; rw [List.getD_append_right _ _ _ _ (by omega), hL, show p.J - (p.J - 1) = 1 by omega]; simp
  rw [h1, h2]

end Link

end NearCubicGates.Close.CounterMachine
