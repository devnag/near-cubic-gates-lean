import Proof.Gates.Solve.Read

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
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM)
open NearCubicWires.RepairRepresentation (natWord)

abbrev rSGN : Reg := 38
abbrev rUL : Reg := 39
abbrev rPAD : Reg := 40
abbrev rCP : Reg := 41
abbrev rLP : Reg := 42
abbrev wU : Str := 12

theorem two_pow_nbl_le (m : ℕ) : 2 ^ natBitLength m ≤ 2 * m + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h)
    rw [pow_succ]; omega

theorem lt_two_pow_nbl (m : ℕ) : m < 2 ^ natBitLength m := Nat.lt_pow_succ_log_self (by norm_num) m

/-- The cost of reading a count. -/
def readCost (x : ℕ) : ℕ := (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)

theorem readCost_le (x : ℕ) : readCost x ≤ 200 * (x + 2) ^ 2 := by
  unfold readCost
  have h1 := two_pow_nbl_le x
  have h2 : natBitLength x + 2 ≤ x + 3 := by
    have := lt_two_pow_nbl x
    have : natBitLength x ≤ 2 ^ natBitLength x := Nat.lt_two_pow_self.le
    unfold natBitLength at *; have := Nat.log_le_self 2 x; omega
  have : (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ (x + 3) * (80 * x + 120) :=
    Nat.mul_le_mul h2 (by omega)
  nlinarith

/-- One coordinate: `wU := 0`, sign, magnitude, `wX1 := encS z`, append, `PAD -= 1`. -/
def coordBody : WMX NS NR :=
  .seq (BinW.zero wU wZ rF rR) (.seq (.wm (readNatM false sRAW rCA rCW rSGN rK2 rG))
    (.seq (CounterMachine.natRead sRAW sRUL wU rCA rR2 rCW) (.seq (SInt.join wU wX1 rSGN rF rR)
      (.seq (appendRecX wX1 sPT rCS rCP) (WMX.dec rPAD)))))

/-- The data the reading phases keep (on the reference state). -/
structure RawCtx (σ0 : MS) (W : ℕ) (word : List Bool) : Prop where
  raw : σ0.st sRAW = word
  rul : σ0.st sRUL = false :: List.replicate (W + 1) true
  rulh : σ0.sh sRUL = 0
  R2 : σ0.val rR2 = 2 * (W + 1) + 1

theorem RawCtx.same {σ0 σ1 : MS} {W : ℕ} {word : List Bool} (h : RawCtx σ0 W word) {S : List Str} {Rg : List Reg}
    (hfr : SameExcept σ0 σ1 S Rg) (hraw : σ1.st sRAW = σ0.st sRAW) (hS : sRUL ∉ S) (hR : rR2 ∉ Rg) :
    RawCtx σ1 W word := ⟨by rw [hraw, h.raw], by rw [hfr.st hS, h.rul], by rw [hfr.sh hS, h.rulh],
  by rw [hfr.val hR, h.R2]⟩

/-- The signed records of one point, padded to `ℓ`. -/
def ptVals (ℓ : ℕ) (u : List ℤ) : List ℕ := (List.range ℓ).map fun i => encS (u.getD i 0)

theorem ptVals_eq (ℓ : ℕ) (u : List ℤ) (hu : u.length ≤ ℓ) :
    ptVals ℓ u = u.map encS ++ List.replicate (ℓ - u.length) (encS 0) := by
  apply List.ext_getElem
  · simp [ptVals]; omega
  · intro i h1 h2
    simp only [ptVals, List.getElem_map, List.getElem_range]
    by_cases hi : i < u.length
    · rw [List.getElem_append_left (by simpa using hi)]; simp [List.getElem?_eq_getElem hi]
    · rw [List.getElem_append_right (by simpa using hi)]
      simp [List.getElem?_eq_none (by omega : u.length ≤ i), encS]

/-- The invariant of the coordinate loop of point `u` after `c` coordinates. -/
def CInv (σB : MS) (W ℓ : ℕ) (p0 : ℕ) (u : List ℤ) (out : List Bool) (c : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.st sRAW = σB.st sRAW ∧ σ1.sh sRAW = p0 + ((u.take c).flatMap Interfaces.intWord).length ∧
    OutOn σ1 sPT rCP (out ++ recBits W ((u.take c).map encS)) [] ∧ σ1.val rPAD = ℓ - c ∧ σ1.val rSGN = 0 ∧
    SameExcept σB σ1 [sRAW, sPT] [rCP, rPAD, rUL, rSGN] ∧ v1 wZ = 0

theorem coord_step (cap : ℕ) {σB : MS} {W ℓ : ℕ} {word : List Bool} (hc : RawCtx σB W word) {p0 : ℕ}
    {u : List ℤ} {out : List Bool} (hp0 : ∃ pre rest, word = pre ++ (u.flatMap Interfaces.intWord) ++ rest ∧ pre.length = p0)
    (hu : ∀ z ∈ u, z.natAbs < 2 ^ W) (hW : 1 ≤ W) (hcap : out.length + (u.length + 1) * (2 * (W + 1) + 1) + 8 ≤ cap)
    (hcap2 : 4 * (W + 1) + 4 ≤ cap) (hcapl : ℓ ≤ cap) (k : ℕ) (hk : k < u.length) (τ : MS)
    (hI : CInv σB W ℓ p0 u out k τ) :
    Runs cap coordBody (τ.setv rUL (u.length - k - 1)) (1000 * (W + 2))
      (fun ρ => CInv σB W ℓ p0 u out (k + 1) ρ ∧ ρ.val rUL = u.length - k - 1) := by
  obtain ⟨σ1, v1, h1, hraw1, hsh1, hout1, hPAD1, hSGN1, hfr1, hZ1⟩ := hI
  obtain ⟨pre, rest, hword, hpre⟩ := hp0
  set z := u[k] with hz
  have huk : u.take (k + 1) = u.take k ++ [z] := by rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  have hsplit : word = (pre ++ (u.take k).flatMap Interfaces.intWord) ++ Interfaces.intWord z ++
      ((u.drop (k + 1)).flatMap Interfaces.intWord ++ rest) := by
    rw [hword]
    conv_lhs => rw [← List.take_append_drop (k + 1) u]
    rw [huk]; simp [List.flatMap_append, List.append_assoc]
  have hzW : z.natAbs < 2 ^ W := hu z (List.getElem_mem hk)
  have h1' := h1.setv (r := rUL) (by decide) (u.length - k - 1)
  set σ2 := σ1.setv rUL (u.length - k - 1) with hσ2
  have hc2 : RawCtx σ2 W word := (hc.same hfr1 hraw1 (by decide) (by decide)).same (S := []) (Rg := [rUL])
    (sameExcept_setv σ1 (by simp) _) rfl (by simp) (by decide)
  have hraw2 : σ2.st sRAW = word := hc2.raw
  have hsh2 : σ2.sh sRAW = (pre ++ (u.take k).flatMap Interfaces.intWord).length := by
    simp [hσ2, hsh1, hpre]
  -- 1. `wU := 0`
  refine Runs.seq' (opZero cap h1' (X := wU) (by decide) (by decide) (by omega)) (fun τ3 h3 => ?_)
    (c2 := 1000 * (W + 2) - (41 * (W + 1) + 4)) (by omega)
  -- 2. sign
  have hst3 : σ2.st sRAW = (pre ++ (u.take k).flatMap Interfaces.intWord) ++
      natWord (if z < 0 then 1 else 0) ++ (natWord z.natAbs ++ ((u.drop (k + 1)).flatMap Interfaces.intWord ++ rest)) := by
    rw [hraw2, hsplit]; simp [Interfaces.intWord, List.append_assoc]
  have hrc := readCost_le (if z < 0 then 1 else 0)
  have hsgn : σ2.val rSGN + 2 ^ (natBitLength (if z < 0 then 1 else 0) + 1) ≤ cap := by
    have : σ2.val rSGN = 0 := by simp (config := {decide := true}) [hσ2, hSGN1]
    have h2 := two_pow_nbl_le (if z < 0 then 1 else 0)
    split_ifs at h2 ⊢ <;> rw [this, pow_succ] <;> omega
  refine Runs.seq' ((opReadNat cap h3 (V := rSGN) (by decide) _ _ _ hst3 hsh2 hsgn).cost
    (show readCost (if z < 0 then 1 else 0) ≤ 200 * 9 by
      have : (if z < 0 then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
      have h3 : ((if z < 0 then 1 else 0 : ℕ) + 2) ^ 2 ≤ 9 := by
        have : (if z < 0 then 1 else 0 : ℕ) + 2 ≤ 3 := by omega
        calc ((if z < 0 then 1 else 0 : ℕ) + 2) ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left this 2
          _ = 9 := by norm_num
      unfold readCost at hrc ⊢; omega)) (fun τ4 h4 => ?_)
    (c2 := 1000 * (W + 2) - (41 * (W + 1) + 4) - (1800 + 1)) (by omega)
  set σ4 := (σ2.seth sRAW ((pre ++ (u.take k).flatMap Interfaces.intWord).length +
    (natWord (if z < 0 then 1 else 0)).length)).setv rSGN (σ2.val rSGN + if z < 0 then 1 else 0) with hσ4
  -- 3. magnitude
  have hst4 : σ4.st sRAW = (pre ++ (u.take k).flatMap Interfaces.intWord ++ natWord (if z < 0 then 1 else 0)) ++
      natWord z.natAbs ++ ((u.drop (k + 1)).flatMap Interfaces.intWord ++ rest) := by
    simp [hσ4, hraw2, hsplit, Interfaces.intWord, List.append_assoc]
  have hsh4 : σ4.sh sRAW = (pre ++ (u.take k).flatMap Interfaces.intWord ++ natWord (if z < 0 then 1 else 0)).length := by
    rw [hσ4]; simp only [WState.setv_sh, WState.seth_sh, Function.update_self, List.length_append]
  have hc4 : RawCtx σ4 W word := hc2.same (S := [sRAW]) (Rg := [rSGN])
    (SameExcept.trans (sameExcept_seth σ2 (by simp) _) (sameExcept_setv _ (by simp) _)) (by simp [hσ4]) (by decide)
    (by decide)
  refine Runs.seq' ((opNatRead cap h4 (X := wU) (by decide) (by simp) z.natAbs _ _ hst4 hsh4 hc4.rul hc4.rulh hc4.R2
    (by rw [pow_succ]; omega) hcap2)) (fun τ5 h5 => ?_)
    (c2 := 1000 * (W + 2) - (41 * (W + 1) + 4) - (1800 + 1) - (60 * (W + 2) + 1)) (by omega)
  set σ5 := σ4.seth sRAW ((pre ++ (u.take k).flatMap Interfaces.intWord ++ natWord (if z < 0 then 1 else 0)).length +
    (natWord z.natAbs).length) with hσ5
  -- 4. `wX1 := encS z`
  have hS5 : σ5.val rSGN = (decide (z < 0)).toNat := by
    have : σ5.val rSGN = (if z < 0 then 1 else 0) := by simp (config := {decide := true}) [hσ5, hσ4, hσ2, hSGN1]
    rw [this]; by_cases hz0 : z < 0 <;> simp [hz0]
  refine Runs.seq' ((opJoin cap h5 (M := wU) (X := wX1) (by decide) (by decide) (by decide) (S := rSGN) (by decide)
    (decide (z < 0)) hS5 (by simp; exact hzW) (by omega))) (fun τ6 h6 => ?_)
    (c2 := 1000 * (W + 2) - (41 * (W + 1) + 4) - (1800 + 1) - (60 * (W + 2) + 1) - (130 * W + 161)) (by omega)
  simp only [Function.update_self, sval_natAbs] at h6
  -- 5. append
  have hout6 : OutOn (σ5.setv rSGN 0) sPT rCP (out ++ recBits W ((u.take k).map encS)) [] := by
    exact ⟨by simp (config := {decide := true}) [hσ5, hσ4, hσ2, hout1.1],
      by simp (config := {decide := true}) [hσ5, hσ4, hσ2, hout1.2.1],
      by simp (config := {decide := true}) [hσ5, hσ4, hσ2, hout1.2.2]⟩
  have hlen : (out ++ recBits W ((u.take k).map encS)).length + 2 * (W + 1) + 2 ≤ cap := by
    rw [List.length_append, recBits_length]; simp only [List.length_map, List.length_take]
    have : min k u.length * (2 * (W + 1) + 1) ≤ u.length * (2 * (W + 1) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have e : (u.length + 1) * (2 * (W + 1) + 1) = u.length * (2 * (W + 1) + 1) + (2 * (W + 1) + 1) := by ring
    omega
  refine Runs.seq' ((opAppend cap h6 (X := wX1) (O := sPT) (CO := rCP) (by decide) (by decide) (by decide) hout6
    hlen)) (fun τ7 h7 => ?_)
    (c2 := 1000 * (W + 2) - (41 * (W + 1) + 4) - (1800 + 1) - (60 * (W + 2) + 1) - (130 * W + 161) -
      (40 * (W + 1) + 12)) (by omega)
  -- 6. `PAD -= 1`
  refine ((opDecR cap h7 (r := rPAD) (by decide) (by
    simp (config := {decide := true}) [hσ5, hσ4, hσ2, hPAD1]; omega)).cost (by omega)).post (fun τ8 h8 => ⟨⟨_, _, h8, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  · simp (config := {decide := true}) [hσ5, hσ4, hσ2, hraw1]
  · simp (config := {decide := true}) [hσ5, hσ4, hσ2, hpre, huk, List.flatMap_append, Interfaces.intWord]; omega
  · refine ⟨by simp [huk, recBits_append, recBits, List.append_assoc], by simp [huk, recBits_append, recBits, List.length_append],
      by simp (config := {decide := true}) [huk, recBits_append, recBits]⟩
  · simp (config := {decide := true}) [hσ5, hσ4, hσ2, hPAD1]; omega
  · simp (config := {decide := true})
  · refine SameExcept.trans hfr1 ⟨fun x hx => ?_, fun q hq => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [hσ5, hσ4, hσ2, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp [hσ5, hσ4, hσ2, Function.update_of_ne hq.1, Function.update_of_ne hq.2.1, Function.update_of_ne hq.2.2.1,
        Function.update_of_ne hq.2.2.2]
    · simp [hσ5, hσ4, hσ2]
  · simp (config := {decide := true}) [hZ1]
  · rw [h8.val (by decide)]; simp (config := {decide := true}) [hσ5, hσ4, hσ2]

end NearCubicGates.Close.Solve
