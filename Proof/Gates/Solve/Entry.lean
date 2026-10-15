import Proof.Gates.Solve.Lay

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

/-! ## Row-major lists -/

/-- The entries `f i j`, rows `i < R`, columns `j < C`, row-major. -/
def flat (R C : ℕ) (f : ℕ → ℕ → ℕ) : List ℕ := (List.range R).flatMap fun i => (List.range C).map (f i)

theorem flat_succ (R C : ℕ) (f : ℕ → ℕ → ℕ) : flat (R + 1) C f = flat R C f ++ (List.range C).map (f R) := by
  simp [flat, List.range_succ, List.flatMap_append]

theorem flat_length (R C : ℕ) (f : ℕ → ℕ → ℕ) : (flat R C f).length = R * C := by
  induction R with
  | zero => simp [flat]
  | succ R ih => rw [flat_succ, List.length_append, ih]; simp; ring

theorem idx_lt {R C i j : ℕ} (hi : i < R) (hj : j < C) : i * C + j < R * C := by
  have : (i + 1) * C ≤ R * C := Nat.mul_le_mul_right _ hi
  nlinarith

theorem flat_get (R C : ℕ) (f : ℕ → ℕ → ℕ) {i j : ℕ} (hi : i < R) (hj : j < C) :
    (flat R C f)[i * C + j]'(by rw [flat_length]; exact idx_lt hi hj) = f i j := by
  induction R with
  | zero => omega
  | succ R ih =>
    simp only [flat_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
    · rw [List.getElem_append_left (by rw [flat_length]; exact idx_lt hi' hj)]
      exact ih hi'
    · subst hi'
      rw [List.getElem_append_right (by rw [flat_length]; omega)]
      simp [flat_length]

/-- The record bits of a list of values (width `W + 1`). -/
def recBits (W : ℕ) (xs : List ℕ) : List Bool := xs.flatMap fun x => frame (binary (W + 1) x)

theorem recStream_eq (W : ℕ) (xs : List ℕ) : recStream (xs.map (binary (W + 1))) = recBits W xs ++ [false] := by
  simp [recStream, recBits, List.flatMap_map]

theorem recBits_append (W : ℕ) (xs ys : List ℕ) : recBits W (xs ++ ys) = recBits W xs ++ recBits W ys := by
  simp [recBits, List.flatMap_append]

theorem recBits_length (W : ℕ) (xs : List ℕ) : (recBits W xs).length = xs.length * (2 * (W + 1) + 1) := by
  induction xs with
  | nil => simp [recBits]
  | cons x xs ih =>
    simp only [recBits, List.flatMap_cons, List.length_append, frame_length, binary_length] at ih ⊢
    rw [ih]; simp; ring

/-! ## The cost unit -/

/-- One unit: any word operation of width `W + 1`, any `getAt` on at most `N` records. -/
def ucost (W N : ℕ) : ℕ := 1000 * (N + 2) * (W + 2) ^ 2

theorem sq_ge (W : ℕ) : W + 2 ≤ (W + 2) ^ 2 := by
  rw [pow_two]; exact Nat.le_mul_of_pos_left _ (by omega)

theorem ucost_ge (W N : ℕ) : 2000 * (W + 2) ^ 2 ≤ ucost W N := by
  unfold ucost
  have := Nat.mul_le_mul_right ((W + 2) ^ 2) (show 1000 * 2 ≤ 1000 * (N + 2) by omega)
  omega

theorem ucost_geN (W N : ℕ) : 4000 * (N + 2) ≤ ucost W N := by
  unfold ucost
  have h4 : 4 ≤ (W + 2) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul (show 2 ≤ W + 2 by omega) (show 2 ≤ W + 2 by omega)
  calc 4000 * (N + 2) = 1000 * (N + 2) * 4 := by ring
    _ ≤ 1000 * (N + 2) * (W + 2) ^ 2 := Nat.mul_le_mul_left _ h4

theorem one_le_ucost (W N : ℕ) : 16 ≤ ucost W N := by
  have := ucost_ge W N; have := sq_ge W; omega

theorem lin_le_ucost (W N : ℕ) : 500 * W + 700 ≤ ucost W N := by
  have := ucost_ge W N; have := sq_ge W; omega

theorem smul_le (W N : ℕ) : smulCost W ≤ ucost W N := by
  have := ucost_ge W N; have := sq_ge W; unfold smulCost; omega

theorem sdiv_le (W N : ℕ) : sdivCost W ≤ ucost W N := by
  have := ucost_ge W N; have := sq_ge W; unfold sdivCost; omega

theorem div_le (W N : ℕ) : BinW.divCost (W + 1) ≤ ucost W N := by
  have := ucost_ge W N; have h := BinW.divCost_le (W + 1)
  rw [show W + 1 + 1 = W + 2 by ring] at h
  omega

theorem getAt_le (W N i : ℕ) (hi : i < N) :
    (i + 1) * (40 * (W + 1) + 40) + 10 * (i + 1) * (2 * (W + 1) + 1) + 10 ≤ ucost W N := by
  unfold ucost
  have h1 : i + 1 ≤ N + 2 := by omega
  have h2 : (i + 1) * (40 * (W + 1) + 40) ≤ (N + 2) * (40 * (W + 2)) := Nat.mul_le_mul h1 (by omega)
  have h3 : 10 * (i + 1) * (2 * (W + 1) + 1) ≤ 10 * (N + 2) * (2 * (W + 2)) := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1)
    (by omega)
  have h4 : (N + 2) * (40 * (W + 2)) + 10 * (N + 2) * (2 * (W + 2)) + 10 ≤ 1000 * (N + 2) * (W + 2) := by
    have : 1 ≤ (N + 2) * (W + 2) := Nat.mul_le_mul (by omega : 1 ≤ N + 2) (by omega : 1 ≤ W + 2)
    nlinarith
  have h5 : 1000 * (N + 2) * (W + 2) ≤ 1000 * (N + 2) * (W + 2) ^ 2 := Nat.mul_le_mul_left _ (sq_ge W)
  omega

/-! ## Registers and words of the elimination -/

abbrev rNZ : Reg := 14
abbrev rFD : Reg := 15
abbrev rNN : Reg := 16
abbrev rMM : Reg := 17
abbrev rRR : Reg := 18
abbrev rCC : Reg := 19
abbrev rV : Reg := 20
abbrev rRB : Reg := 21
abbrev rSB : Reg := 22
abbrev rSIX : Reg := 23
abbrev rIJ : Reg := 24
abbrev rRJ : Reg := 25
abbrev rIV : Reg := 26
abbrev rLI : Reg := 27
abbrev rLJ : Reg := 28
abbrev rSL : Reg := 29
abbrev rCN : Reg := 30
abbrev rCM : Reg := 31
abbrev rLV : Reg := 32

abbrev wX1 : Str := 10
abbrev wX2 : Str := 11
abbrev wM : Str := 14
abbrev wN : Str := 15
abbrev wC : Str := 16
abbrev wD : Str := 17
abbrev wE : Str := 18
abbrev wPW : Str := 20
abbrev wDD : Str := 21
abbrev wAV : Str := 22

/-! ## One entry -/

/-- `NEW += tdiv (a_ij·P − a_rj·A) D`; `IJ += 1`, `RJ += 1`. -/
def entryP : WMX NS NR :=
  .seq (getAt sMAT wK rCA rCW rIJ rK2) (.seq (BinW.copy wX1 wK rF rR) (.seq (smul wX1 wPW wM wN wC wD rS rT rF rR rG)
  (.seq (getAt sMAT wK rCA rCW rRJ rK2) (.seq (BinW.copy wX2 wK rF rR) (.seq (smul wX2 wAV wM wN wC wD rS rT rF rR rG)
  (.seq (ssub wX1 wX2 wM wN rS rT rF rR) (.seq (sdiv wX1 wDD wM wN wC wD wE rS rT rF rR rK rT2)
  (.seq (appendRecX wX1 sNEW rCS rCN) (.seq (WMX.inc rIJ) (WMX.inc rRJ))))))))))

/-- The bound hypotheses of one entry: every value at most `Bd`, `2·Bd² < 2^W`. -/
structure EBound (W Bd : ℕ) (aij arj P A D : ℤ) : Prop where
  hij : aij.natAbs ≤ Bd
  hrj : arj.natAbs ≤ Bd
  hP : P.natAbs ≤ Bd
  hA : A.natAbs ≤ Bd
  hD : D.natAbs ≤ Bd
  hW : 2 * Bd * Bd + 1 < 2 ^ W

theorem le_sq2 (Bd : ℕ) : Bd ≤ 2 * Bd * Bd + 1 := by
  rcases Nat.eq_zero_or_pos Bd with h0 | h0
  · omega
  · have : Bd ≤ Bd * Bd := Nat.le_mul_of_pos_left _ h0
    have e : 2 * Bd * Bd = Bd * Bd + Bd * Bd := by ring
    omega

theorem EBound.lt {W Bd : ℕ} {aij arj P A D : ℤ} (hb : EBound W Bd aij arj P A D) {z : ℤ} (hz : z.natAbs ≤ Bd) :
    z.natAbs < 2 ^ W := by
  have := hb.hW; have := le_sq2 Bd; omega

theorem natAbs_mul_le {Bd : ℕ} {x y : ℤ} (hx : x.natAbs ≤ Bd) (hy : y.natAbs ≤ Bd) : (x * y).natAbs ≤ Bd * Bd := by
  rw [Int.natAbs_mul]; exact Nat.mul_le_mul hx hy

theorem EBound.prodlt {W Bd : ℕ} {aij arj P A D : ℤ} (hb : EBound W Bd aij arj P A D) {x y : ℤ} (hx : x.natAbs ≤ Bd)
    (hy : y.natAbs ≤ Bd) : (x * y).natAbs < 2 ^ W := by
  have h1 := natAbs_mul_le hx hy
  have := hb.hW
  have e : 2 * Bd * Bd = Bd * Bd + Bd * Bd := by ring
  omega

theorem EBound.diff {W Bd : ℕ} {aij arj P A D : ℤ} (hb : EBound W Bd aij arj P A D) :
    (aij * P - arj * A).natAbs < 2 ^ W := by
  have h1 := natAbs_mul_le hb.hij hb.hP
  have h2 := natAbs_mul_le hb.hrj hb.hA
  have h3 : (aij * P - arj * A).natAbs ≤ (aij * P).natAbs + (arj * A).natAbs := Int.natAbs_sub_le _ _
  have := hb.hW
  have e : 2 * Bd * Bd = Bd * Bd + Bd * Bd := by ring
  omega

theorem entry_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) (xs : List ℕ) (junk : List Bool)
    (hmat : σ0.st sMAT = recStream (xs.map (binary (W + 1))) ++ junk) (hmath : σ0.sh sMAT = 0)
    (hIJ : σ0.val rIJ < xs.length) (hRJ : σ0.val rRJ < xs.length) {aij arj P A D : ℤ}
    (hxij : xs[σ0.val rIJ] = encS aij) (hxrj : xs[σ0.val rRJ] = encS arj) (hP : v wPW = encS P)
    (hA : v wAV = encS A) (hD : v wDD = encS D) (hD0 : D ≠ 0) {Bd : ℕ} (hb : EBound W Bd aij arj P A D)
    {out L0 : List Bool} (hout : OutOn σ0 sNEW rCN out L0)
    (hcap : (xs.length + 1) * (2 * (W + 1) + 1) + 2 * xs.length + out.length + 2 * (W + 1) + 2 ≤ cap)
    (hcapr : σ0.val rIJ + 1 < cap ∧ σ0.val rRJ + 1 < cap) :
    Runs cap entryP σ (12 * ucost W xs.length) (fun τ => ∃ σ1 v', At σ1 τ W v' ∧
      OutOn σ1 sNEW rCN (out ++ frame (binary (W + 1) (encS (Int.tdiv (aij * P - arj * A) D)))) L0 ∧
      σ1.val rIJ = σ0.val rIJ + 1 ∧ σ1.val rRJ = σ0.val rRJ + 1 ∧ SameExcept σ0 σ1 [sNEW] [rCN, rIJ, rRJ] ∧
      v' wPW = v wPW ∧ v' wAV = v wAV ∧ v' wDD = v wDD) := by
  have hP1W : 2 * (W + 1) + 1 ≤ (xs.length + 1) * (2 * (W + 1) + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hc2 : 2 * (W + 1) + 1 ≤ cap := by omega
  have hcG1 : (xs.length + 1) * (2 * (W + 1) + 1) + 2 * σ0.val rIJ ≤ cap := by omega
  have hcG2 : (xs.length + 1) * (2 * (W + 1) + 1) + 2 * σ0.val rRJ ≤ cap := by omega
  have hcA : out.length + 2 * (W + 1) + 2 ≤ cap := by omega
  have hU := one_le_ucost W xs.length
  have hL := lin_le_ucost W xs.length
  have hg1 := getAt_le W xs.length _ hIJ
  have hg2 := getAt_le W xs.length _ hRJ
  have hsm := smul_le W xs.length
  have hsd := sdiv_le W xs.length
  have hij := hb.lt hb.hij
  have hrj := hb.lt hb.hrj
  have hPl := hb.lt hb.hP
  have hAl := hb.lt hb.hA
  have hDl := hb.lt hb.hD
  -- 1. `wK := a_ij`
  refine Runs.seq' ((opGetAt cap h (by decide) (by decide) xs junk hmat hmath hIJ hcG1).cost hg1)
    (fun τ1 h1 => ?_) (c2 := 12 * ucost W xs.length - 1 * (ucost W xs.length + 1)) (by omega)

  refine Runs.seq' ((opCopy cap h1 (X := wX1) (Y := wK) (by decide) (by decide) (by decide) hc2).cost
    (show 41 * (W + 1) + 3 ≤ ucost W xs.length by omega)) (fun τ2 h2 => ?_) (c2 := 12 * ucost W xs.length - 2 * (ucost W xs.length + 1)) (by omega)
  set v2 := Function.update (Function.update v wK xs[σ0.val rIJ]) wX1
    ((Function.update v wK xs[σ0.val rIJ]) wK) with hv2

  refine Runs.seq' ((opSmul cap h2 (X := wX1) (Y := wPW) (M := wM) (N := wN) (C := wC) (D := wD) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (x := aij) (y := P)
    (by simp [hv2, hxij]) (by simp (config := {decide := true}) [hv2, hP]) hij hPl (hb.prodlt hb.hij hb.hP) hc2).cost hsm) (fun τ3 h3 => ?_)
    (c2 := 12 * ucost W xs.length - 3 * (ucost W xs.length + 1)) (by omega)
  obtain ⟨v3, h3, hv3X, hv3o⟩ := h3
  -- 4. `wK := a_rj`
  refine Runs.seq' ((opGetAt cap h3 (by decide) (by decide) xs junk hmat hmath hRJ hcG2).cost hg2)
    (fun τ4 h4 => ?_) (c2 := 12 * ucost W xs.length - 4 * (ucost W xs.length + 1)) (by omega)

  refine Runs.seq' ((opCopy cap h4 (X := wX2) (Y := wK) (by decide) (by decide) (by decide) hc2).cost
    (show 41 * (W + 1) + 3 ≤ ucost W xs.length by omega)) (fun τ5 h5 => ?_) (c2 := 12 * ucost W xs.length - 5 * (ucost W xs.length + 1)) (by omega)
  set v5 := Function.update (Function.update v3 wK xs[σ0.val rRJ]) wX2
    ((Function.update v3 wK xs[σ0.val rRJ]) wK) with hv5
  have hv5A : v5 wAV = encS A := by
    have e1 : v5 wAV = v3 wAV := by simp (config := {decide := true}) [hv5]
    rw [e1, hv3o wAV (by decide)]; simp (config := {decide := true}) [hv2, hA]

  refine Runs.seq' ((opSmul cap h5 (X := wX2) (Y := wAV) (M := wM) (N := wN) (C := wC) (D := wD) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (x := arj) (y := A)
    (by simp [hv5, hxrj]) hv5A hrj hAl (hb.prodlt hb.hrj hb.hA) hc2).cost hsm)
    (fun τ6 h6 => ?_) (c2 := 12 * ucost W xs.length - 6 * (ucost W xs.length + 1)) (by omega)
  obtain ⟨v6, h6, hv6X, hv6o⟩ := h6
  have hv6X1 : v6 wX1 = encS (aij * P) := by
    rw [hv6o wX1 (by decide)]
    have e1 : v5 wX1 = v3 wX1 := by simp (config := {decide := true}) [hv5]
    rw [e1, hv3X]

  refine Runs.seq' ((opSsub cap h6 (X := wX1) (Y := wX2) (M := wM) (N := wN) (by decide) (by decide) (by decide)
    (by decide) (by decide) hv6X1 hv6X (hb.prodlt hb.hij hb.hP) (hb.prodlt hb.hrj hb.hA) hb.diff hc2).cost
    (show 420 * W + 610 ≤ ucost W xs.length by omega)) (fun τ7 h7 => ?_) (c2 := 12 * ucost W xs.length - 7 * (ucost W xs.length + 1)) (by omega)
  obtain ⟨v7, h7, hv7X, hv7o⟩ := h7
  have hv7D : v7 wDD = encS D := by
    rw [hv7o wDD (by decide), hv6o wDD (by decide)]
    have e1 : v5 wDD = v3 wDD := by simp (config := {decide := true}) [hv5]
    rw [e1, hv3o wDD (by decide)]; simp (config := {decide := true}) [hv2, hD]

  refine Runs.seq' ((opSdiv cap h7 (X := wX1) (Y := wDD) (M := wM) (N := wN) (Q := wC) (Rm := wD) (E := wE)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv7X hv7D
    hb.diff hDl hD0 hc2).cost hsd) (fun τ8 h8 => ?_) (c2 := 12 * ucost W xs.length - 8 * (ucost W xs.length + 1)) (by omega)
  obtain ⟨v8, h8, hv8X, hv8o⟩ := h8
  -- 9. append
  refine Runs.seq' ((opAppend cap h8 (X := wX1) (O := sNEW) (CO := rCN) (by decide) (by decide) (by decide) hout
    hcA).cost (show 40 * (W + 1) + 11 ≤ ucost W xs.length by omega)) (fun τ9 h9 => ?_) (c2 := 12 * ucost W xs.length - 9 * (ucost W xs.length + 1)) (by omega)
  rw [hv8X] at h9
  set σ1 := ((σ0.sets sNEW (overlay (out ++ frame (binary (W + 1) (encS (Int.tdiv (aij * P - arj * A) D)))) L0)).seth
    sNEW (out ++ frame (binary (W + 1) (encS (Int.tdiv (aij * P - arj * A) D)))).length).setv rCN
    (out ++ frame (binary (W + 1) (encS (Int.tdiv (aij * P - arj * A) D)))).length with hσ1
  have hσ1IJ : σ1.val rIJ = σ0.val rIJ := by simp (config := {decide := true}) [hσ1]
  have hσ1RJ : σ1.val rRJ = σ0.val rRJ := by simp (config := {decide := true}) [hσ1]
  -- 10. `IJ += 1`, `RJ += 1`
  refine Runs.seq' (opIncR cap h9 (r := rIJ) (by decide) (by rw [hσ1IJ]; omega)) (fun τ10 h10 => ?_)
    (c2 := 3) (by omega)
  refine (opIncR cap h10 (r := rRJ) (by decide) (by simp (config := {decide := true}) [hσ1RJ]; omega)).post (fun τ11 h11 => ?_)
  refine ⟨_, v8, h11, ⟨by simp (config := {decide := true}) [hσ1], by simp (config := {decide := true}) [hσ1], by simp (config := {decide := true}) [hσ1]⟩, by simp (config := {decide := true}) [hσ1], by simp (config := {decide := true}) [hσ1], ?_, ?_, ?_, ?_⟩
  · refine ⟨fun x hx => ?_, fun r hr => ?_, by simp (config := {decide := true}) [hσ1]⟩
    · have : x ≠ sNEW := fun e => hx (by simp [e])
      simp (config := {decide := true}) [hσ1, Function.update_of_ne this]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (config := {decide := true}) [hσ1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2]
  · rw [hv8o wPW (by decide), hv7o wPW (by decide), hv6o wPW (by decide)]
    have e1 : v5 wPW = v3 wPW := by simp (config := {decide := true}) [hv5]
    rw [e1, hv3o wPW (by decide)]; simp (config := {decide := true}) [hv2]
  · rw [hv8o wAV (by decide), hv7o wAV (by decide), hv6o wAV (by decide), hv5A, hA]
  · rw [hv8o wDD (by decide), hv7D, hD]

end NearCubicGates.Close.Solve
