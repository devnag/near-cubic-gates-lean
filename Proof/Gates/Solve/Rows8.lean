import Proof.Gates.Solve.Rows7

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open StablePartition.Workspace (overlay)
open NearCubicGates.Close.Interfaces.Formats (inClass SysReq)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM)

/-- The records of system row `i`. -/
theorem rowRec_eq (s : SysReq) {i : ℕ} (hi : i < s.rows.length) :
    (List.range (s.pts.length + 1)).map (fun j => encS (amat s i j)) =
      entVals s.rows[i].1 s.rows[i].2.1 s.pts s.pts.length ++ [encS (s.rows[i].2.2 : ℤ)] := by
  rw [List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    rw [amat_sys s hi (List.mem_range.mp hj), List.getD_eq_getElem _ _ hi]
    simp [coef]
  · simp [amat_rhs s hi, List.getElem?_eq_getElem hi]

/-- The row-loop invariant after `i` rows. -/
def RInv (σB : MS) (W : ℕ) (s : SysReq) (p0 : ℕ) (L0 : List Bool) (i : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.st sRAW = σB.st sRAW ∧ σ1.sh sRAW = p0 + ((s.rows.take i).flatMap rowW).length ∧
    OutOn σ1 sMAT rCM (recBits W (matV i (s.pts.length + 1) (amat s))) L0 ∧ (∀ r ∈ rowRegs, σ1.val r = 0) ∧
    σ1.val rLS = 0 ∧ σ1.val rCSG = 0 ∧ σ1.sh sSG = 0 ∧
    SameExcept σB σ1 [sRAW, sSG, sMAT] (rCM :: rLR :: rLS :: rCSG :: rowRegs) ∧ v1 wZ = 0 ∧ v1 wTWO = 2

/-- The bounds of the request entries. -/
structure ReqBound (s : SysReq) (ℓ : ℕ) : Prop where
  pts : ∀ u ∈ s.pts, u.length ≤ ℓ ∧ ∀ z ∈ u, z.natAbs < 2 ^ ℓ
  rows : ∀ row ∈ s.rows, row.1 < 2 ^ ℓ ∧ (∀ x ∈ row.2.1, x < 2 ^ ℓ) ∧ row.2.1.length ≤ ℓ ∧ row.2.2 < 2 ^ ℓ

/-- The cost bound of one row. -/
def rowCost (n ℓ W U : ℕ) : ℕ := rowACost ℓ W U + 1 + rowBCost n ℓ U

theorem rows_step (cap : ℕ) {σB : MS} {W ℓ : ℕ} {word : List Bool} (hc : RawCtx σB W word) (s : SysReq)
    (hrb : ReqBound s ℓ) {pre0 rest0 : List Bool} (hword : word = pre0 ++ s.rows.flatMap rowW ++ rest0)
    {jP : List Bool} (hPT : σB.st sPT = recStream ((s.pts.flatMap (ptVals ℓ)).map (binary (W + 1))) ++ jP)
    (hPTh : σB.sh sPT = 0) (hNN : σB.val rNN = s.pts.length) (hLL : σB.val rLL = ℓ) (hℓW : ℓ + 2 ≤ W)
    (hℓ1 : 1 ≤ ℓ) {L0 : List Bool} (hcap : capC (s.pts.length * ℓ + ℓ) W ≤ cap)
    (hcapO : (s.rows.length + 1) * (s.pts.length + 2) * (2 * (W + 1) + 1) + (ℓ + 2) * (2 * (W + 1) + 1) + 8 * ℓ + 8 ≤ cap)
    (i : ℕ) (hi : i < s.rows.length) (τ : MS) (hI : RInv σB W s pre0.length L0 i τ) :
    Runs cap (.seq rowA rowB) (τ.setv rLR (s.rows.length - i - 1))
      (rowCost s.pts.length ℓ W (ucost W (s.pts.length * ℓ + ℓ)))
      (fun ρ => RInv σB W s pre0.length L0 (i + 1) ρ ∧ ρ.val rLR = s.rows.length - i - 1) := by
  obtain ⟨σ1, v1, h1, hraw1, hsh1, hout1, hz1, hLS1, hCSG1, hSGh1, hfr1, hZ1, hT1⟩ := hI
  set row := s.rows[i] with hrow
  obtain ⟨hq, hσb, hσl, hb⟩ := hrb.rows row (List.getElem_mem hi)
  have htk : s.rows.take (i + 1) = s.rows.take i ++ [row] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  have hsplit : word = (pre0 ++ (s.rows.take i).flatMap rowW) ++ rowW row ++
      ((s.rows.drop (i + 1)).flatMap rowW ++ rest0) := by
    rw [hword]
    conv_lhs => rw [← List.take_append_drop (i + 1) s.rows]
    rw [htk]; simp [List.flatMap_append, List.append_assoc]
  have h1' := h1.setv (r := rLR) (by decide) (s.rows.length - i - 1)
  set σ2 := σ1.setv rLR (s.rows.length - i - 1) with hσ2
  have hfr2 : SameExcept σB σ2 [sRAW, sSG, sMAT] (rCM :: rLR :: rLS :: rCSG :: rowRegs) :=
    SameExcept.trans hfr1 (sameExcept_setv σ1 (by simp) _)
  have hc2 : RawCtx σ2 W word := hc.same hfr2 (by simp [hσ2, hraw1]) (by decide) (by decide)
  have hN0 : 0 ≤ s.pts.length * ℓ := Nat.zero_le _
  have hQ := Nat.le_mul_of_pos_left (2 * (W + 1) + 1) (show 0 < ℓ + 2 by omega)
  -- the head of the row
  have hA := rowA_spec cap h1' (N := s.pts.length * ℓ + ℓ) hc2 row.1 row.2.1 (pre0 ++ (s.rows.take i).flatMap rowW)
    (natWord row.2.2 ++ ((s.rows.drop (i + 1)).flatMap rowW ++ rest0))
    (by rw [hsplit]; simp [rowW, List.append_assoc]) (by simp [hσ2, hsh1])
    (by simp [hσ2, hSGh1])
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simp (config := {decide := true}) [hσ2]; exact hz1 rNZQ (by decide)
      · simp (config := {decide := true}) [hσ2]; exact hz1 rSLN (by decide)
      · simp (config := {decide := true}) [hσ2, hLS1]
      · simp (config := {decide := true}) [hσ2, hCSG1]) hq hσb hσl hℓW (by omega)
    (by have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (Nat.zero_le ((s.rows.length + 1) * (s.pts.length + 2)))
        omega)
  refine Runs.seq hA (fun τ3 ⟨σ3, v3, h3, hraw3, hsh3, hvq3, hNZQ3, hSLN3, hLS3, hCSG3, ⟨jS, hSG3⟩, hSGh3, hfr3,
    hkeep3⟩ => ?_)
  -- the tail of the row
  have hcc3 : CellCtx σ3 W ℓ s.pts row.2.1 jS jP :=
    ⟨hSG3, hSGh3, by rw [hfr3.st (by decide), hfr2.st (by decide), hPT], by rw [hfr3.sh (by decide), hfr2.sh (by decide),
      hPTh]⟩
  have hvZ3 : v3 wZ = 0 := by rw [hkeep3 wZ (by decide) (by decide), hZ1]
  have hvT3 : v3 wTWO = 2 := by rw [hkeep3 wTWO (by decide) (by decide), hT1]
  have hlenO : (recBits W (matV i (s.pts.length + 1) (amat s))).length + (s.pts.length + 2) * (2 * (W + 1) + 1) + 2
      ≤ cap := by
    rw [recBits_length, matV_length]
    have h1 : i * (s.pts.length + 1) + (s.pts.length + 2) ≤ (s.rows.length + 1) * (s.pts.length + 2) := by nlinarith
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) h1
    rw [Nat.add_mul] at this
    have := Nat.le_mul_of_pos_left (2 * (W + 1) + 1) (show 0 < ℓ + 2 by omega)
    nlinarith
  have hB := rowB_spec cap h3 (hc2.same hfr3 hraw3 (by decide) (by decide)) hcc3 row.1 row.2.2
    (pre0 ++ (s.rows.take i).flatMap rowW ++ (natWord row.1 ++ Interfaces.listWord natWord row.2.1))
    ((s.rows.drop (i + 1)).flatMap rowW ++ rest0) (by rw [hsplit]; simp [rowW, List.append_assoc])
    (by rw [hsh3]; exact List.length_append.symm) hNZQ3 hvq3 hvT3 hvZ3 hSLN3
    (by rw [hfr3.val (by decide), hfr2.val (by decide), hLL]) (by rw [hfr3.val (by decide), hfr2.val (by decide), hNN])
    (by rw [hfr3.val (by decide)]; simp (config := {decide := true}) [hσ2]; exact hz1 rPB (by decide))
    (by rw [hfr3.val (by decide)]; simp (config := {decide := true}) [hσ2]; exact hz1 rLP2 (by decide))
    (fun r hr => by
      simp only [cellRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hfr3.val (by decide)]; simp (config := {decide := true}) [hσ2]; exact hz1 rFL (by decide)
      · rw [hfr3.val (by decide)]; simp (config := {decide := true}) [hσ2]; exact hz1 rIXP (by decide)
      · rw [hfr3.val (by decide)]; simp (config := {decide := true}) [hσ2]; exact hz1 rISG (by decide)
      · exact hLS3
      · rw [hfr3.val (by decide)]; simp (config := {decide := true}) [hσ2]; exact hz1 rSGN (by decide)
      · rw [hfr3.val (by decide)]; simp (config := {decide := true}) [hσ2]; exact hz1 rT4 (by decide))
    hσl hσb (fun u hu => (hrb.pts u hu).2) hq hb hℓW hℓ1
    (OutOn.same hout1 (SameExcept.trans (sameExcept_setv σ1 (S := [sSG, sRAW]) (Rg := [rLR, rNZQ, rSLN, rLS, rCSG])
      (by simp) _) (hfr3.weaken (by simp) (by simp))) (by decide) (by decide)) hcap hlenO
  refine hB.post (fun τ4 ⟨σ4, v4, h4, hraw4, hsh4, hout4, hz4, hfr4, hZ4, hT4⟩ =>
    ⟨⟨σ4, v4, h4, ?_, ?_, ?_, hz4, ?_, ?_, ?_, ?_, hZ4, hT4⟩, ?_⟩)
  · rw [hraw4, hraw3, hc2.raw, hc.raw]
  · rw [hsh4, htk]; simp [List.flatMap_append, rowW, Interfaces.listWord]; ring
  · have e : matV (i + 1) (s.pts.length + 1) (amat s) = matV i (s.pts.length + 1) (amat s) ++
        (entVals row.1 row.2.1 s.pts s.pts.length ++ [encS (row.2.2 : ℤ)]) := by
      rw [matV, flat_succ, ← rowRec_eq s hi]; rfl
    rw [e, recBits_append]; exact hout4
  · exact hz4 rLS (by decide)
  · rw [hfr4.val (by decide)]; exact hCSG3
  · rw [hfr4.sh (by decide)]; exact hSGh3
  · refine SameExcept.trans hfr2 (SameExcept.trans (hfr3.weaken (by simp) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
      (hfr4.weaken (by simp) (by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | h
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))))
  · rw [h4.val (by decide), hfr4.val (by decide), hfr3.val (by decide)]; simp (config := {decide := true}) [hσ2]

end NearCubicGates.Close.Solve
