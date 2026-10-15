import Proof.Gates.Solve.Points

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

/-- The word of one point. -/
def ptW (u : List ℤ) : List Bool := Interfaces.listWord Interfaces.intWord u

/-- One point: its length, `PAD := ℓ`, its coordinates, the padding zeros. -/
def pointBody : WMX NS NR :=
  .seq (.wm (readNatM false sRAW rCA rCW rUL rK2 rG)) (.seq (addR rLL rPAD rTa)
    (.seq (.whr rUL (.seq (WMX.dec rUL) coordBody)) (.whr rPAD (.seq (WMX.dec rPAD) (appendRecX wZ sPT rCS rCP)))))

/-- The cap of the reading phases. -/
def capP (n ℓ W : ℕ) : ℕ := (n + 2) * (ℓ + 2) * (2 * (W + 1) + 1) + 8 * ℓ + 100

/-- The cost bound of one point. -/
def ptCost (ℓ W : ℕ) : ℕ := 2000 * (ℓ + 2) ^ 2 * (W + 2)

/-- The padding invariant after `j` zeros. -/
def PadInv (σB : MS) (W : ℕ) (out : List Bool) (j : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ OutOn σ1 sPT rCP (out ++ recBits W (List.replicate j (encS 0))) [] ∧
    SameExcept σB σ1 [sPT] [rCP, rPAD] ∧ v1 wZ = 0

theorem pad_step (cap : ℕ) {σB : MS} {W : ℕ} {out : List Bool} {P : ℕ} (hcap : out.length + (P + 1) * (2 * (W + 1) + 1) + 1 ≤ cap)
    (j : ℕ) (hj : j < P) (τ : MS) (hI : PadInv σB W out j τ) :
    Runs cap (appendRecX wZ sPT rCS rCP) (τ.setv rPAD (P - j - 1)) (40 * (W + 1) + 11)
      (fun ρ => PadInv σB W out (j + 1) ρ ∧ ρ.val rPAD = P - j - 1) := by
  obtain ⟨σ1, v1, h1, hout1, hfr1, hZ1⟩ := hI
  have h1' := h1.setv (r := rPAD) (by decide) (P - j - 1)
  have hout1' : OutOn (σ1.setv rPAD (P - j - 1)) sPT rCP (out ++ recBits W (List.replicate j (encS 0))) [] :=
    ⟨by simp [hout1.1], by simp [hout1.2.1], by simp (config := {decide := true}) [hout1.2.2]⟩
  have hlen : (out ++ recBits W (List.replicate j (encS 0))).length + 2 * (W + 1) + 2 ≤ cap := by
    rw [List.length_append, recBits_length, List.length_replicate]
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (show j + 1 ≤ P + 1 by omega)
    rw [Nat.add_mul, one_mul] at this; omega
  refine (opAppend cap h1' (X := wZ) (O := sPT) (CO := rCP) (by decide) (by decide) (by decide) hout1' hlen).post
    (fun ρ hρ => ⟨⟨_, v1, hρ, ?_, ?_, hZ1⟩, ?_⟩)
  · rw [hZ1]
    refine ⟨by simp [List.replicate_succ', recBits_append, recBits, encS], by simp [List.replicate_succ', recBits_append,
      recBits, encS], by simp (config := {decide := true}) [List.replicate_succ', recBits_append, recBits, encS]⟩
  · refine SameExcept.trans hfr1 (SameExcept.trans (sameExcept_setv σ1 (S := [sPT]) (Rg := [rCP, rPAD]) (r := rPAD)
      (by simp) (P - j - 1)) ⟨fun x hx => ?_, fun q hq => ?_, rfl⟩)
    · have : x ≠ sPT := by simpa using hx
      simp [Function.update_of_ne this]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp [Function.update_of_ne hq.1]
  · rw [hρ.val (by decide)]; simp (config := {decide := true})

theorem ptCost_le (ℓ W ul : ℕ) (hul : ul ≤ ℓ) :
    readCost ul + 1 + (18 * ℓ + 3 + 1 + (ul * (1000 * (W + 2) + 4) + 1 + 1 + ((ℓ - ul) * (40 * (W + 1) + 11 + 4) + 1)))
      ≤ ptCost ℓ W := by
  have h1 := readCost_le ul
  have h2 : (ul + 2) ^ 2 ≤ (ℓ + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : ul * (1000 * (W + 2) + 4) ≤ ℓ * (1000 * (W + 2) + 4) := Nat.mul_le_mul_right _ hul
  have h4 : (ℓ - ul) * (40 * (W + 1) + 11 + 4) ≤ ℓ * (40 * (W + 1) + 15) := Nat.mul_le_mul_right _ (by omega)
  have h5 : ℓ + 2 ≤ (ℓ + 2) ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_left _ (by omega)
  unfold ptCost
  nlinarith

theorem point_spec (cap : ℕ) {σ0 σ : MS} {W ℓ : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {word : List Bool}
    (hc : RawCtx σ0 W word) (u : List ℤ) (pre rest : List Bool) (hword : word = pre ++ ptW u ++ rest)
    (hsh : σ0.sh sRAW = pre.length) (hu : ∀ z ∈ u, z.natAbs < 2 ^ W) (hul : u.length ≤ ℓ) (hLL : σ0.val rLL = ℓ)
    (hUL : σ0.val rUL = 0) (hPAD : σ0.val rPAD = 0) (hSGN : σ0.val rSGN = 0) (hZ : v wZ = 0) {out : List Bool}
    (hout : OutOn σ0 sPT rCP out []) (hcap : out.length + (ℓ + 2) * (2 * (W + 1) + 1) + 8 ≤ cap)
    (hcap2 : 4 * (W + 1) + 4 ≤ cap) (hcapl : 8 * ℓ + 8 ≤ cap) (hW : 1 ≤ W) :
    Runs cap pointBody σ (ptCost ℓ W) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.st sRAW = σ0.st sRAW ∧
      σ1.sh sRAW = pre.length + (ptW u).length ∧ OutOn σ1 sPT rCP (out ++ recBits W (ptVals ℓ u)) [] ∧
      σ1.val rUL = 0 ∧ σ1.val rPAD = 0 ∧ σ1.val rSGN = 0 ∧
      SameExcept σ0 σ1 [sRAW, sPT] [rCP, rPAD, rUL, rSGN] ∧ v1 wZ = 0) := by
  refine Runs.cost ?_ (ptCost_le ℓ W u.length hul)
  -- 1. `UL := |u|`
  have hst : σ0.st sRAW = pre ++ natWord u.length ++ (u.flatMap Interfaces.intWord ++ rest) := by
    rw [hc.raw, hword]; simp [ptW, Interfaces.listWord, List.append_assoc]
  have hrd : σ0.val rUL + 2 ^ (natBitLength u.length + 1) ≤ cap := by
    have := two_pow_nbl_le u.length; rw [hUL, pow_succ]; omega
  refine Runs.seq (opReadNat cap h (V := rUL) (by decide) u.length pre _ hst hsh hrd) (fun τ1 h1 => ?_)
  set σ1 := (σ0.seth sRAW (pre.length + (natWord u.length).length)).setv rUL (σ0.val rUL + u.length) with hσ1
  -- 2. `PAD := ℓ`
  have h1LL : σ1.val rLL = ℓ := by simp (config := {decide := true}) [hσ1, hLL]
  refine Runs.seq ((opAddR cap h1 (A := rLL) (B := rPAD) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ1, hPAD, hLL]; omega)).cost (show 18 * σ1.val rLL + 3 ≤ 18 * ℓ + 3 by
      rw [h1LL])) (fun τ2 h2 => ?_)
  rw [h1LL] at h2
  set σ2 := σ1.setv rPAD (σ1.val rPAD + ℓ) with hσ2
  have hfr02 : SameExcept σ0 σ2 [sRAW] [rUL, rPAD] :=
    SameExcept.trans (sameExcept_seth σ0 (by simp) _) (SameExcept.trans (sameExcept_setv _ (by simp) _)
      (sameExcept_setv _ (by simp) _))
  have hc2 : RawCtx σ2 W word := hc.same hfr02 (by simp [hσ2, hσ1]) (by decide) (by decide)
  set p0 := pre.length + (natWord u.length).length with hp0
  -- 3. the coordinates
  have hI0 : CInv σ2 W ℓ p0 u out 0 τ2 := by
    refine ⟨σ2, _, h2, rfl, by simp [hσ2, hσ1], by simpa [recBits] using OutOn.same hout hfr02 (by decide) (by decide),
      by simp (config := {decide := true}) [hσ2, hσ1, hPAD], by simp (config := {decide := true}) [hσ2, hσ1, hSGN],
      SameExcept.refl _ _ _, hZ⟩
  have hloop := Runs.count (cap := cap) (K := rUL) (body := coordBody) (1000 * (W + 2)) u.length
    (CInv σ2 W ℓ p0 u out) (by omega)
    (fun k hk τ hτ _ => coord_step cap hc2 ⟨pre ++ natWord u.length, rest, by rw [hword]; simp [ptW, Interfaces.listWord,
      List.append_assoc], by simp [hp0]⟩ hu hW (by nlinarith) hcap2 (by omega) k hk τ hτ) τ2 hI0
    (by rw [h2.val (by decide)]; simp (config := {decide := true}) [hσ2, hσ1, hUL])
  refine Runs.seq hloop (fun τ3 ⟨⟨σ3, v3, h3, hraw3, hsh3, hout3, hPAD3, hSGN3, hfr3, hZ3⟩, hK3⟩ => ?_)
  -- 4. the padding
  have hout3' : OutOn σ3 sPT rCP (out ++ recBits W (u.map encS) ++ recBits W (List.replicate 0 (encS 0))) [] := by
    simpa [recBits, List.take_length] using hout3
  have hpl := Runs.count (cap := cap) (K := rPAD) (body := appendRecX wZ sPT rCS rCP) (40 * (W + 1) + 11)
    (ℓ - u.length) (PadInv σ3 W (out ++ recBits W (u.map encS))) (by omega)
    (fun j hj τ hτ _ => pad_step cap (P := ℓ - u.length) (by
      rw [List.length_append, recBits_length, List.length_map]
      have : (u.length + (ℓ - u.length + 1)) * (2 * (W + 1) + 1) ≤ (ℓ + 2) * (2 * (W + 1) + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul] at this; omega) j hj τ hτ) τ3
    ⟨σ3, v3, h3, by simpa [recBits] using hout3', SameExcept.refl _ _ _, hZ3⟩
    (by rw [h3.val (by decide), hPAD3])
  refine hpl.post (fun τ4 ⟨⟨σ4, v4, h4, hout4, hfr4, hZ4⟩, hK4⟩ => ⟨σ4, v4, h4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hZ4⟩)
  · rw [hfr4.st (by decide), hraw3]; simp [hσ2, hσ1]
  · rw [hfr4.sh (by decide), hsh3, List.take_length, hp0]; simp [ptW, Interfaces.listWord]; ring
  · rw [ptVals_eq ℓ u hul, recBits_append, ← List.append_assoc]; exact hout4
  · rw [hfr4.val (by decide), ← h3.val (by decide)]; exact hK3
  · rw [← h4.val (by decide)]; exact hK4
  · rw [hfr4.val (by decide)]; exact hSGN3
  · exact SameExcept.trans (hfr02.weaken (by simp) (by simp)) (SameExcept.trans (hfr3.weaken (by simp) (by simp))
      (hfr4.weaken (by simp) (by simp)))

/-! ## All points -/

def pointsP : WMX NS NR :=
  .seq (.wm (readNatM false sRAW rCA rCW rNN rK2 rG)) (.seq (addR rNN rLP rTa)
    (.seq (.whr rLP (.seq (WMX.dec rLP) pointBody)) (closeOutX sPT rCP)))

/-- The point-loop invariant after `k` points. -/
def PInv (σB : MS) (W ℓ : ℕ) (n : ℕ) (pts : List (List ℤ)) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.st sRAW = σB.st sRAW ∧
    σ1.sh sRAW = (natWord n).length + ((pts.take k).flatMap ptW).length ∧
    OutOn σ1 sPT rCP (recBits W ((pts.take k).flatMap (ptVals ℓ))) [] ∧ σ1.val rUL = 0 ∧ σ1.val rPAD = 0 ∧
    σ1.val rSGN = 0 ∧ SameExcept σB σ1 [sRAW, sPT] [rCP, rPAD, rUL, rSGN, rLP] ∧ v1 wZ = 0

theorem recBits_ptVals_length (W ℓ : ℕ) (us : List (List ℤ)) :
    (recBits W (us.flatMap (ptVals ℓ))).length = us.length * ℓ * (2 * (W + 1) + 1) := by
  rw [recBits_length]
  congr 1
  induction us with
  | nil => simp
  | cons u us ih => rw [List.flatMap_cons, List.length_append, ih]; simp [ptVals]; ring

theorem points_step (cap : ℕ) {σB : MS} {W ℓ n : ℕ} {word restP : List Bool} {pts : List (List ℤ)}
    (hc : RawCtx σB W word) (hword : word = natWord n ++ pts.flatMap ptW ++ restP) (hn : pts.length = n)
    (hpts : ∀ u ∈ pts, u.length ≤ ℓ ∧ ∀ z ∈ u, z.natAbs < 2 ^ W) (hLL : σB.val rLL = ℓ) (hW : 1 ≤ W)
    (hcap : capP n ℓ W ≤ cap) (k : ℕ) (hk : k < n) (τ : MS) (hI : PInv σB W ℓ n pts k τ) :
    Runs cap pointBody (τ.setv rLP (n - k - 1)) (ptCost ℓ W)
      (fun ρ => PInv σB W ℓ n pts (k + 1) ρ ∧ ρ.val rLP = n - k - 1) := by
  obtain ⟨σ1, v1, h1, hraw1, hsh1, hout1, hUL1, hPAD1, hSGN1, hfr1, hZ1⟩ := hI
  have hkp : k < pts.length := by omega
  set u := pts[k] with hu
  have h1' := h1.setv (r := rLP) (by decide) (n - k - 1)
  set σ2 := σ1.setv rLP (n - k - 1) with hσ2
  have hfr2 : SameExcept σB σ2 [sRAW, sPT] [rCP, rPAD, rUL, rSGN, rLP] :=
    SameExcept.trans hfr1 (sameExcept_setv σ1 (by simp) _)
  have hc2 : RawCtx σ2 W word := hc.same hfr2 (by simp [hσ2, hraw1]) (by decide) (by decide)
  have htk : pts.take (k + 1) = pts.take k ++ [u] := by rw [List.take_add_one, List.getElem?_eq_getElem hkp]; rfl
  have hwordk : word = (natWord n ++ (pts.take k).flatMap ptW) ++ ptW u ++ ((pts.drop (k + 1)).flatMap ptW ++ restP) := by
    rw [hword]
    conv_lhs => rw [← List.take_append_drop (k + 1) pts]
    rw [htk]; simp [List.flatMap_append, List.append_assoc]
  have hcapP := hcap
  unfold capP at hcapP
  have hQ : 1 ≤ 2 * (W + 1) + 1 := by omega
  have hlen1 : (recBits W ((pts.take k).flatMap (ptVals ℓ))).length + (ℓ + 2) * (2 * (W + 1) + 1) + 8 ≤ cap := by
    rw [recBits_ptVals_length, List.length_take, Nat.min_eq_left hkp.le]
    have h0 : k * ℓ + (ℓ + 2) ≤ (n + 2) * (ℓ + 2) := by
      have : k * ℓ ≤ n * (ℓ + 2) := Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) h0
    rw [Nat.add_mul] at this
    omega
  have hpt := point_spec cap h1' hc2 u (natWord n ++ (pts.take k).flatMap ptW) _ hwordk
    (by simp [hσ2, hsh1]) (hpts u (List.getElem_mem hkp)).2 (hpts u (List.getElem_mem hkp)).1
    (by rw [hfr2.val (by decide), hLL]) (by simp (config := {decide := true}) [hσ2, hUL1])
    (by simp (config := {decide := true}) [hσ2, hPAD1]) (by simp (config := {decide := true}) [hσ2, hSGN1]) hZ1
    (OutOn.same hout1 (sameExcept_setv σ1 (S := []) (Rg := [rLP]) (by simp) _) (by simp) (by decide)) hlen1
    (by have h4 : 4 ≤ (n + 2) * (ℓ + 2) := by nlinarith
        have := Nat.mul_le_mul_right (2 * (W + 1) + 1) h4
        omega) (by omega) hW
  refine hpt.post (fun ρ ⟨σ3, v3, h3, hraw3, hsh3, hout3, hUL3, hPAD3, hSGN3, hfr3, hZ3⟩ =>
    ⟨⟨σ3, v3, h3, ?_, ?_, ?_, hUL3, hPAD3, hSGN3, ?_, hZ3⟩, ?_⟩)
  · rw [hraw3, hc2.raw, hc.raw]
  · rw [hsh3, htk]; simp [List.flatMap_append]; ring
  · rw [htk, List.flatMap_append, recBits_append]; simpa using hout3
  · exact SameExcept.trans hfr2 (hfr3.weaken (by simp) (by simp))
  · rw [h3.val (by decide), hfr3.val (by decide)]; simp [hσ2]

end NearCubicGates.Close.Solve
