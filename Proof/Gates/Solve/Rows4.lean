import Proof.Gates.Solve.Rows3

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
open NearCubicGates.Close.Interfaces.Formats (inClass)
open NearCubicWires.RepairRepresentation (natWord)

/-- One `σ_i`: read it, double it (`encS σ_i`), append it to `sSG`. -/
def sgBody : WMX NS NR :=
  .seq (BinW.zero wSG wZ rF rR) (.seq (CounterMachine.natRead sRAW sRUL wSG rCA rR2 rCW)
    (.seq (BinW.shl wSG wZ rF rR) (appendRecX wSG sSG rCS rCSG)))

/-- The `σ` loop invariant after `k` entries. -/
def SgInv (σB : MS) (W : ℕ) (σl : List ℕ) (p0 : ℕ) (L0 : List Bool) (keep : Str → ℕ) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.st sRAW = σB.st sRAW ∧ σ1.sh sRAW = p0 + ((σl.take k).flatMap natWord).length ∧
    OutOn σ1 sSG rCSG (recBits W (sgVals (σl.take k))) L0 ∧ SameExcept σB σ1 [sRAW, sSG] [rCSG, rLS] ∧
    ∀ X ∈ keepW, v1 X = keep X

theorem keepW_ne {X : Str} (hX : X ∈ keepW) : X ≠ wSG ∧ X ≠ wE2 ∧ X ≠ wK ∧ X ≠ wX1 := by
  simp only [keepW, List.mem_cons, List.not_mem_nil, or_false] at hX; rcases hX with rfl | rfl | rfl | rfl <;> decide

theorem sg_step (cap : ℕ) {σB : MS} {W ℓ : ℕ} {word : List Bool} (hc : RawCtx σB W word) {σl : List ℕ} {p0 : ℕ}
    (hp0 : ∃ pre rest, word = pre ++ σl.flatMap natWord ++ rest ∧ pre.length = p0) (hσb : ∀ x ∈ σl, x < 2 ^ ℓ)
    (hℓW : ℓ + 2 ≤ W) {L0 : List Bool} (keep : Str → ℕ) (hσl : σl.length ≤ ℓ)
    (hcap : (ℓ + 2) * (2 * (W + 1) + 1) + 8 ≤ cap) (k : ℕ) (hk : k < σl.length) (τ : MS)
    (hI : SgInv σB W σl p0 L0 keep k τ) :
    Runs cap sgBody (τ.setv rLS (σl.length - k - 1)) (300 * (W + 2))
      (fun ρ => SgInv σB W σl p0 L0 keep (k + 1) ρ ∧ ρ.val rLS = σl.length - k - 1) := by
  obtain ⟨σ1, v1, h1, hraw1, hsh1, hout1, hfr1, hkeep1⟩ := hI
  obtain ⟨pre, rest, hword, hpre⟩ := hp0
  have hcW : 2 * (W + 1) + 1 ≤ cap := by
    have := Nat.le_mul_of_pos_left (2 * (W + 1) + 1) (show 0 < ℓ + 2 by omega); omega
  have hc4 : 4 * (W + 1) + 4 ≤ cap := by
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (show 2 ≤ ℓ + 2 by omega); omega
  set x := σl[k] with hx
  have htk : σl.take (k + 1) = σl.take k ++ [x] := by rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  have hsplit : word = (pre ++ (σl.take k).flatMap natWord) ++ natWord x ++ ((σl.drop (k + 1)).flatMap natWord ++ rest) := by
    rw [hword]
    conv_lhs => rw [← List.take_append_drop (k + 1) σl]
    rw [htk]; simp [List.flatMap_append, List.append_assoc]
  have hxl : x < 2 ^ ℓ := hσb x (List.getElem_mem hk)
  have hpow : 2 ^ ℓ * 4 ≤ 2 ^ W := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1' := h1.setv (r := rLS) (by decide) (σl.length - k - 1)
  set σ2 := σ1.setv rLS (σl.length - k - 1) with hσ2
  have hfr2 : SameExcept σB σ2 [sRAW, sSG] [rCSG, rLS] := SameExcept.trans hfr1 (sameExcept_setv σ1 (by simp) _)
  have hc2 : RawCtx σ2 W word := hc.same hfr2 (by simp [hσ2, hraw1]) (by decide) (by decide)
  -- 1. `wSG := 0`
  refine Runs.seq' ((opZero cap h1' (X := wSG) (by decide) (by decide) hcW)) (fun τ3 h3 => ?_)
    (c2 := 300 * (W + 2) - (41 * (W + 1) + 4)) (by omega)
  -- 2. read `σ_k`
  have hst : σ2.st sRAW = (pre ++ (σl.take k).flatMap natWord) ++ natWord x ++
      ((σl.drop (k + 1)).flatMap natWord ++ rest) := by rw [hc2.raw, hsplit]
  have hsh : σ2.sh sRAW = (pre ++ (σl.take k).flatMap natWord).length := by
    simp [hσ2, hsh1, hpre]
  refine Runs.seq' (opNatRead cap h3 (X := wSG) (by decide) (by simp) x _ _ hst hsh hc2.rul hc2.rulh hc2.R2
    (by rw [pow_succ]; omega) hc4) (fun τ4 h4 => ?_)
    (c2 := 300 * (W + 2) - (41 * (W + 1) + 4) - (60 * (W + 2) + 1)) (by omega)
  -- 3. `wSG := 2·σ_k`
  refine Runs.seq' ((opShl cap h4 (X := wSG) (by decide) (by decide) hcW)) (fun τ5 h5 => ?_)
    (c2 := 300 * (W + 2) - (41 * (W + 1) + 4) - (60 * (W + 2) + 1) - (41 * (W + 1) + 9)) (by omega)
  -- 4. append
  have hout4 : OutOn (σ2.seth sRAW ((pre ++ (σl.take k).flatMap natWord).length + (natWord x).length)) sSG rCSG
      (recBits W (sgVals (σl.take k))) L0 :=
    ⟨by simp (config := {decide := true}) [hσ2, hout1.1], by simp (config := {decide := true}) [hσ2, hout1.2.1],
      by simp (config := {decide := true}) [hσ2, hout1.2.2]⟩
  have hlenSG : (recBits W (sgVals (σl.take k))).length + 2 * (W + 1) + 2 ≤ cap := by
    rw [recBits_length]; simp only [sgVals, List.length_map, List.length_take]
    have : min k σl.length * (2 * (W + 1) + 1) ≤ ℓ * (2 * (W + 1) + 1) := Nat.mul_le_mul_right _ (by omega)
    have e : (ℓ + 2) * (2 * (W + 1) + 1) = ℓ * (2 * (W + 1) + 1) + 2 * (2 * (W + 1) + 1) := by ring
    omega
  refine (opAppend cap h5 (X := wSG) (O := sSG) (CO := rCSG) (by decide) (by decide) (by decide) hout4 hlenSG).mono
    (by omega) (fun ρ hρ => ⟨⟨_, _, hρ, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  · simp (config := {decide := true}) [hσ2, hraw1]
  · simp (config := {decide := true}) [hpre, htk, List.flatMap_append]; omega
  · have e : (Function.update (Function.update (Function.update v1 wSG 0) wSG x) wSG
        (2 * Function.update (Function.update v1 wSG 0) wSG x wSG)) wSG = encS ((x : ℕ) : ℤ) := by
      simp [encS_nat]
    rw [e]
    refine ⟨by simp [htk, sgVals, recBits_append, recBits], by simp [htk, sgVals, recBits_append, recBits],
      by simp (config := {decide := true}) [htk, sgVals, recBits_append, recBits]⟩
  · refine SameExcept.trans hfr2 ⟨fun y hy => ?_, fun r hr => ?_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [Function.update_of_ne hy.1, Function.update_of_ne hy.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [Function.update_of_ne hr.1]
  · intro X hX
    have hne := keepW_ne hX
    simp [Function.update_of_ne hne.1, hkeep1 X hX]
  · rw [hρ.val (by decide)]; simp (config := {decide := true}) [hσ2]

end NearCubicGates.Close.Solve
