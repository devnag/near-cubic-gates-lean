import SourceAdapters.Williams.Loader

/-!
# W04, assembled: the loader program and its specification

`loader IA IB SIM x` reads `natWord N ++ rowMajor A` from stream `IA` and `rowMajor B` from `IB` (no end markers),
computes `W = natBitLength N`, `N` in unary, `k = N^{1/10}` by search, `P = k·N`, and writes the leaf's input word
`inputWord A B` (`PublishedStatements/Williams.lean`) block by block on `SIM`, head back on cell 0
(`loader_spec`). Registers (concrete): DG 0, REM 1, WD 2, T 3, RN 4, POW 5, T2 6, WD2 7, KC 8, PC 9, PC2 10,
TMP 11, DIFF 12, PP 13, PP2 14. Consumer `MultitapeMultiplier.multiplies` (`Statement.lean:1129`).
-/

namespace NearCubicGates.Adapters.Williams.Load

open NearCubicGates.Published.Williams NearCubicGates.Adapters.Williams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WilliamsLoaderForms (rowMajorBitMatrix)

set_option autoImplicit false
set_option linter.unusedSimpArgs false

variable {ns : ℕ}

/-- **The loader** (W04). -/
def loader (IA IB SIM : Fin (ns + 1)) (x : ℕ) : WMX ns 16 :=
  .seq (countOnes IA 2) (.seq (WMX.fwd IA) (.seq (toUnary IA 4 5 3 6 2 7)
    (.seq (rootSearch 8 9 10 11 12 3 4) (.seq (mulR 8 10 4 13 3)
    (.seq (copyBits IA SIM 13 14 (fun b => blockOf (Symbol.digit b : Symbol x)))
    (.seq (writeBits SIM (blockOf (Symbol.separator : Symbol x)))
    (.seq (copyBits IB SIM 13 14 (fun b => blockOf (Symbol.digit b : Symbol x)))
    (.seq (backBlocks SIM 13 14 (x + 4)) (.seq (backBlocks SIM 13 14 (x + 4)) (bwdN SIM (x + 4)))))))))))

/-- The register capacity the loader needs at dimension `k`. -/
def loaderCap (k : ℕ) : ℕ := 4 * (k ^ 10) ^ 2 + 2 ^ (natBitLength (k ^ 10) + 2) + 4 * natBitLength (k ^ 10) + 16

/-- The loader's exact step count. -/
def loaderCost (x k : ℕ) : ℕ :=
  (natBitLength (k ^ 10) * 7 + 1) + 1 + (1 + 1 + ((3 + 1 + (natBitLength (k ^ 10) *
    (toUnaryCost (natBitLength (k ^ 10)) + 8) + 7 * natBitLength (k ^ 10) + 3)) + 1 +
  ((3 + 1 + (powDiffCost (k ^ 10) + 1 + (k * (roundCost (k ^ 10) + 2) + 1))) + 1 +
  ((k * (18 * k ^ 10 + 3 + 8) + 7 * k + 3) + 1 +
  ((k ^ 10 * k * (4 * (x + 4) + 3 + 8) + 7 * (k ^ 10 * k) + 3) + 1 + (4 * (x + 4) + 1 +
  ((k * k ^ 10 * (4 * (x + 4) + 3 + 8) + 7 * (k * k ^ 10) + 3) + 1 +
  ((k * k ^ 10 * (2 * (x + 4) + 8) + 7 * (k * k ^ 10) + 3) + 1 +
  ((k * k ^ 10 * (2 * (x + 4) + 8) + 7 * (k * k ^ 10) + 3) + 1 + 2 * (x + 4))))))))))

theorem rowMajor_length {α : Type} {n m : ℕ} (A : Fin n → Fin m → α) : (rowMajor A).length = n * m := by
  simp [rowMajor, List.length_flatten, List.sum_ofFn]

theorem natWord_eq' (n : ℕ) : natWord n = List.replicate (natBitLength n) true ++ false ::
    WilliamsPublishedForm.fixedWidthNatBits (natBitLength n) n := rfl

theorem flatMap_digit_length {x : ℕ} : ∀ (l : List Bool),
    (l.flatMap fun b => blockOf (Symbol.digit b : Symbol x)).length = l.length * (x + 4)
  | [] => by simp
  | b :: l => by rw [List.flatMap_cons, List.length_append, blockOf_length, flatMap_digit_length l]; simp; ring

theorem natWord_length (n : ℕ) : (natWord n).length = 2 * natBitLength n + 1 := by
  rw [natWord_eq']; simp [WilliamsPublishedForm.fixedWidthNatBits]; omega

theorem natBitLength_le {N : ℕ} (hN : 1 ≤ N) : natBitLength N ≤ N := by
  unfold natBitLength
  have := Nat.log_lt_self 2 (show N ≠ 0 by omega)
  omega

theorem two_pow_natBitLength_le {N : ℕ} (hN : 1 ≤ N) : 2 ^ natBitLength N ≤ 2 * N := by
  unfold natBitLength
  rw [pow_succ]
  have := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
  omega

/-- **W04.** The loader writes the leaf's input word in blocks on `SIM`, head on cell 0, with `WD = natBitLength N`
and `DG = REM = T = 0`, touching no stream other than `IA`, `IB`, `SIM`. -/
theorem loader_spec {cap : ℕ} (IA IB SIM : Fin (ns + 1)) (hAB : IA ≠ IB) (hAS : IA ≠ SIM) (hBS : IB ≠ SIM)
    (x k : ℕ) (hk : 1 ≤ k) (A : Fin (k ^ 10) → Fin k → Bool) (B : Fin k → Fin (k ^ 10) → Bool)
    (σ : WState ns 16) (hIA : σ.st IA = natWord (k ^ 10) ++ rowMajorBitMatrix A) (hIAh : σ.sh IA = 0)
    (hIB : σ.st IB = rowMajorBitMatrix B) (hIBh : σ.sh IB = 0) (hS : σ.st SIM = []) (hSh : σ.sh SIM = 0)
    (hv : ∀ r, σ.val r = 0) (hcap : loaderCap k ≤ cap) :
    ∃ τ, WXExec cap (loader IA IB SIM x) σ τ (loaderCost x k) ∧
      τ.st SIM = (inputWord A B : List (Symbol x)).flatMap blockOf ∧ τ.sh SIM = 0 ∧
      τ.val 2 = natBitLength (k ^ 10) ∧ τ.val 0 = 0 ∧ τ.val 1 = 0 ∧ τ.val 3 = 0 ∧
      ∀ j, j ≠ IA → j ≠ IB → j ≠ SIM → τ.st j = σ.st j ∧ τ.sh j = σ.sh j := by
  have hN1 : 1 ≤ k ^ 10 := Nat.one_le_pow _ _ hk
  have hNW : k ^ 10 < 2 ^ natBitLength (k ^ 10) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hWN := natBitLength_le hN1
  have h2W := two_pow_natBitLength_le hN1
  have hkN : k ≤ k ^ 10 := Nat.le_self_pow (by norm_num) k
  have hkk : k * k ^ 10 ≤ k ^ 10 * k ^ 10 := Nat.mul_le_mul_right _ hkN
  unfold loaderCap at hcap
  rw [show 2 ^ (natBitLength (k ^ 10) + 2) = 4 * 2 ^ natBitLength (k ^ 10) by rw [pow_add]; ring] at hcap
  have hsq : k ^ 10 ≤ (k ^ 10) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hkk2 : k ^ 10 * k ≤ (k ^ 10) ^ 2 := by nlinarith
  have hkk3 : k * k ^ 10 ≤ (k ^ 10) ^ 2 := by nlinarith
  have hcap' : k ^ 10 * k ^ 10 = (k ^ 10) ^ 2 := by ring
  have hLlen : (natWord (k ^ 10)).length = 2 * natBitLength (k ^ 10) + 1 := natWord_length _
  -- phase a: the header width
  have ra : ∀ i < natBitLength (k ^ 10), readTapeBit (σ.st IA) (σ.sh IA + i) = true := by
    intro i hi
    rw [hIA, hIAh, Nat.zero_add, readTapeBit, natWord_eq', List.append_assoc,
      List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi]
  have rb : readTapeBit (σ.st IA) (σ.sh IA + natBitLength (k ^ 10)) = false := by
    rw [hIA, hIAh, Nat.zero_add, readTapeBit, natWord_eq', List.append_assoc,
      List.getD_append_right _ _ _ _ (by simp)]
    simp
  have e1 := countOnes_spec (cap := cap) IA 2 (natBitLength (k ^ 10)) σ ra rb (by rw [hv]; omega)
    (natBitLength (k ^ 10)) (natBitLength (k ^ 10)) (by rw [hv]; omega) (by rw [hIAh]; omega)
  have e2 := WXExec.fwd (cap := cap) IA ((σ.setv 2 (natBitLength (k ^ 10))).seth IA (natBitLength (k ^ 10)))
  have v2 : ∀ r, r ≠ 2 → (((σ.setv 2 (natBitLength (k ^ 10))).seth IA (natBitLength (k ^ 10))).seth IA
      (natBitLength (k ^ 10) + 1)).val r = 0 := by
    intro r hr; simp [Function.update_of_ne hr, hv]
  obtain ⟨W, hW⟩ : ∃ W, natBitLength (k ^ 10) = W := ⟨_, rfl⟩
  rw [hW] at e1 e2 v2 hLlen hNW hWN h2W hcap
  -- phase b: N in unary
  have hbits : ∀ j < W, readTapeBit (natWord (k ^ 10) ++ rowMajorBitMatrix A) (W + 1 + j) = (k ^ 10).testBit j := by
    intro j hj
    rw [readTapeBit, natWord_eq', hW, List.append_assoc, List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_replicate, show W + 1 + j - W = j + 1 by omega, List.cons_append,
      List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simp [WilliamsPublishedForm.fixedWidthNatBits]; omega)]
    simp [WilliamsPublishedForm.fixedWidthNatBits, List.getD_eq_getElem?_getD, hj]
  obtain ⟨σ3, e3, b1, b2, b3, b4, b5, b6, b7, b8⟩ := toUnary_spec (cap := cap) IA (RN := 4) (POW := 5) (T := 3)
    (T2 := 6) (WD := 2) (WD2 := 7) (by decide) _ (W + 1) W (k ^ 10) hNW hbits _ (by simp [hIA])
    (by simp) (by simp) (v2 7 (by decide)) (v2 4 (by decide)) (v2 5 (by decide))
    (v2 3 (by decide)) (v2 6 (by decide)) (by rw [show 2 ^ (W + 2) = 4 * 2 ^ W by rw [pow_add]; ring]; omega)
  have v3 : ∀ r, r ∉ [(4 : Fin 16), 5, 6, 2, 7] → σ3.val r = 0 := by
    intro r hr; rw [b8.2.1 r hr]; exact v2 r (by intro h; exact hr (by simp [h]))
  -- phase c: k
  have e4 := rootSearch_spec (cap := cap) (KC := 8) (PC := 9) (PC2 := 10) (TMP := 11) (DIFF := 12) (T := 3)
    (RN := 4) (by decide) σ3 k (k ^ 10) hk rfl (v3 8 (by decide)) (v3 9 (by decide)) (v3 10 (by decide))
    (v3 11 (by decide)) (v3 12 (by decide)) b2 b1 (by omega)
  -- phase d: P = k · N
  have e5 := mulR_spec cap (A := (8 : Fin 16)) (A2 := 10) (B := 4) (C := 13) (T := 3) (by decide) (σ3.setv 8 k)
    (by simp [v3 10 (by decide)]) (by simp [b2])
    (by simp [v3 13 (by decide), b1]; omega) (by simp; omega)
  have r5 : (σ3.setv 8 k).val 13 + (σ3.setv 8 k).val 8 * (σ3.setv 8 k).val 4 = (rowMajor A).length := by
    simp [v3 13 (by decide), b1, rowMajor_length]; ring
  have c5 : (σ3.setv 8 k).val 8 * (18 * (σ3.setv 8 k).val 4 + 3 + 8) + 7 * (σ3.setv 8 k).val 8 + 3 =
      k * (18 * k ^ 10 + 3 + 8) + 7 * k + 3 := by simp [b1]
  rw [r5, c5] at e5
  -- phase e: A, block by block
  have hS3 : σ3.st SIM = [] ∧ σ3.sh SIM = 0 := by
    have := b8.1 SIM (by simp [Ne.symm hAS]); simp at this; rw [this.1, this.2]; simp [Ne.symm hAS, hS, hSh]
  have hbitsA : ∀ j (hj : j < (rowMajor A).length),
      readTapeBit (natWord (k ^ 10) ++ rowMajorBitMatrix A) (W + 1 + W + j) = (rowMajor A)[j] := by
    intro j hj
    rw [readTapeBit, List.getD_append_right _ _ _ _ (by rw [hLlen]; omega), hLlen,
      show W + 1 + W + j - (2 * W + 1) = j by omega, show rowMajorBitMatrix A = rowMajor A from rfl,
      List.getD_eq_getElem _ _ hj]
  obtain ⟨σ6, e6, f1, f2, f3, f4, f5, f6, f7⟩ := copyBits_spec (cap := cap) (IX := IA) (SIM := SIM) (PP := 13)
    (PP2 := 14) hAS (by decide) (fun b => blockOf (Symbol.digit b : Symbol x)) (x + 4) (fun b => blockOf_length _)
    _ (W + 1 + W) (rowMajor A) hbitsA ((σ3.setv 8 k).setv 13 (rowMajor A).length) (by simpa using b4)
    (by simpa using b5) (by simp [hS3.1, hS3.2]) (by simp) (by simp [v3 14 (by decide)])
    (by rw [rowMajor_length]; omega)
  -- phase f: the separator
  have e7 := writeBits_spec (cap := cap) SIM (blockOf (Symbol.separator : Symbol x)) σ6 f2
  -- phase g: B, block by block
  have hB6 : σ6.st IB = rowMajorBitMatrix B ∧ σ6.sh IB = 0 := by
    have h7 := f7.1 IB (by simp [hBS, Ne.symm hAB])
    have h8 := b8.1 IB (by simp [Ne.symm hAB])
    simp only [WState.setv_st, WState.setv_sh] at h7
    rw [h7.1, h7.2, h8.1, h8.2]; simp [Ne.symm hAB, hIB, hIBh]
  have hbitsB : ∀ j (hj : j < (rowMajor B).length), readTapeBit (rowMajorBitMatrix B) (0 + j) = (rowMajor B)[j] := by
    intro j hj
    rw [Nat.zero_add, readTapeBit, show rowMajorBitMatrix B = rowMajor B from rfl, List.getD_eq_getElem _ _ hj]
  obtain ⟨σ8, e8, g1, g2, g3, g4, g5, g6, g7⟩ := copyBits_spec (cap := cap) (IX := IB) (SIM := SIM) (PP := 13)
    (PP2 := 14) hBS (by decide) (fun b => blockOf (Symbol.digit b : Symbol x)) (x + 4) (fun b => blockOf_length _)
    _ 0 (rowMajor B) hbitsB ((σ6.sets SIM (σ6.st SIM ++ blockOf (Symbol.separator : Symbol x))).seth SIM
      ((σ6.st SIM).length + (blockOf (Symbol.separator : Symbol x)).length))
    (by simp [hBS, hB6.1]) (by simp [hBS, hB6.2]) (by simp)
    (by simp [f5, rowMajor_length, Nat.mul_comm]) (by simp [f6]) (by rw [rowMajor_length]; omega)
  -- phase h: back to cell 0
  obtain ⟨σ9, e9, h1, h1s, h2, h3, h4⟩ := backBlocks_spec (cap := cap) (S := SIM) (PP := 13) (PP2 := 14)
    (by decide) (x + 4) _ σ8 g5 g6 (by rw [rowMajor_length]; omega)
  obtain ⟨σ10, e10, i1, i1s, i2, i3, i4⟩ := backBlocks_spec (cap := cap) (S := SIM) (PP := 13) (PP2 := 14)
    (by decide) (x + 4) _ σ9 h2 h3 (by rw [rowMajor_length]; omega)
  have e11 := bwdN_spec (cap := cap) SIM (x + 4) σ10
  have e2' := WXExec.cast cap e2 (τ' := ((σ.setv 2 W).seth IA W).seth IA (W + 1)) (by simp) le_rfl
  -- streams other than IA, IB, SIM
  have fr3 : ∀ j, j ≠ IA → j ≠ IB → j ≠ SIM → σ3.st j = σ.st j ∧ σ3.sh j = σ.sh j := by
    intro j h1 _ _
    have := b8.1 j (by simp [h1]); rw [this.1, this.2]; simp [Function.update_of_ne h1]
  have fr8 : ∀ j, j ≠ IA → j ≠ IB → j ≠ SIM → σ8.st j = σ.st j ∧ σ8.sh j = σ.sh j := by
    intro j h1 h2 h3
    have a := g7.1 j (by simp [h2, h3]); have b := f7.1 j (by simp [h1, h3])
    simp only [WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh, WState.setv_st,
      WState.setv_sh, Function.update_of_ne h3] at a b
    rw [a.1, a.2, b.1, b.2]; exact fr3 j h1 h2 h3
  have rg3 : σ3.val 0 = 0 ∧ σ3.val 1 = 0 ∧ σ3.val 2 = W ∧ σ3.val 3 = 0 :=
    ⟨v3 0 (by decide), v3 1 (by decide), b6, b2⟩
  have rg8 : ∀ r : Fin 16, r ∉ [(13 : Fin 16), 14, 8] → σ8.val r = σ3.val r := by
    intro r hr
    rw [g7.2.1 r (by intro h; exact hr (by simp_all))]
    simp only [WState.seth_val, WState.sets_val]
    rw [f7.2.1 r (by intro h; exact hr (by simp_all))]
    have h13 : r ≠ 13 := fun h => hr (by simp [h])
    have h8 : r ≠ 8 := fun h => hr (by simp [h])
    simp [Function.update_of_ne h13, Function.update_of_ne h8]
  have rg10 : ∀ r : Fin 16, r ∉ [(13 : Fin 16), 14, 8] → σ10.val r = σ3.val r := by
    intro r hr
    rw [i4.2.1 r (by intro h; exact hr (by simp_all)), h4.2.1 r (by intro h; exact hr (by simp_all))]
    exact rg8 r hr
  have hlenA : (rowMajor A).length = k ^ 10 * k := rowMajor_length A
  have hlenB : (rowMajor B).length = k * k ^ 10 := rowMajor_length B
  have hcomm : k * k ^ 10 = k ^ 10 * k := Nat.mul_comm _ _
  refine ⟨σ10.seth SIM (σ10.sh SIM - (x + 4)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e := WXExec.seq e1 (WXExec.seq e2' (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
      (WXExec.seq e7 (WXExec.seq e8 (WXExec.seq e9 (WXExec.seq e10 e11)))))))))
    refine WXExec.mono e ?_
    rw [hlenA, hlenB, blockOf_length]
    subst hW
    unfold loaderCost
    omega
  · simp only [WState.seth_st]
    rw [i1s, h1s, g1]
    simp only [WState.seth_st, WState.sets_st, Function.update_self]
    rw [f1]
    simp only [WState.setv_st]
    rw [hS3.1]
    simp [inputWord, List.flatMap_append, List.flatMap_map, Function.comp_def]
  · simp only [WState.seth_sh, Function.update_self]
    rw [i1, h1, g2, g1]
    simp only [WState.seth_st, WState.sets_st, Function.update_self, List.length_append]
    rw [f1]
    simp only [WState.setv_st, List.length_append]
    rw [hS3.1, flatMap_digit_length, flatMap_digit_length, blockOf_length, hlenA, hlenB, hcomm]
    simp only [List.length_nil, Nat.zero_add]
    have : k ^ 10 * k * (x + 4) + (x + 4) + k ^ 10 * k * (x + 4) =
        k ^ 10 * k * (x + 4) + k ^ 10 * k * (x + 4) + (x + 4) := by ring
    omega
  · simp only [WState.seth_val]; rw [rg10 2 (by decide)]; rw [← hW] at rg3; exact rg3.2.2.1
  · simp only [WState.seth_val]; rw [rg10 0 (by decide)]; exact rg3.1
  · simp only [WState.seth_val]; rw [rg10 1 (by decide)]; exact rg3.2.1
  · simp only [WState.seth_val]; rw [rg10 3 (by decide)]; exact rg3.2.2.2
  · intro j h1 h2 h3
    have a := i4.1 j (by simp [h3]); have b := h4.1 j (by simp [h3])
    simp only [WState.seth_st, WState.seth_sh, Function.update_of_ne h3]
    rw [a.1, a.2, b.1, b.2]; exact fr8 j h1 h2 h3

end NearCubicGates.Adapters.Williams.Load
