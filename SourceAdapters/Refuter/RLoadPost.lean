import SourceAdapters.Refuter.RLoadNum

/-!
# R's loader, part 4: the constants after the clock (input 7, R: INIT)

Paper anchor: proof of `lem:multitape-refuter` (the clock `T(N)`), proof of `cor:framed-refuter` (`x_i = 1^M 0 1^{N−M−2−g} 0 w_i`, `g = ⌊N/16⌋`),
 (the search starts in the fresh state: nothing asked, `lo = hi = fuel = 0`).

`postP p` (on R's layout, `p` the time constructor) runs after the time constructor has left `T(N)` in binary on
its output stream `ko p` and the unary step count `1^s` on `TLI`: it writes `TU = 1^{T(N)}`, `GU = 1^g`,
`MU = 1^M`, `XU = 1^{N−g−M−2}`, the ten stored numbers (`0` seven times, `1`, `2^g`, `g+1`) and the flags of
the fresh state (`post_spec`, explicit final state `postSt`, cost `≤ postBound`).
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Adapters.Refuter
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem setsL_const_mem {ns nr : ℕ} (v : List Bool) : ∀ (L : List (Fin (ns + 1))) (σ : WState ns nr) (Y : Fin (ns + 1)),
    Y ∈ L → (setsL σ (L.map fun X => (X, v))).st Y = v
  | [], _, _, h => by simp at h
  | X :: L, σ, Y, h => by
    by_cases hY : Y ∈ L
    · exact setsL_const_mem v L _ Y hY
    · have hXY : Y = X := by simp at h; tauto
      subst hXY
      simp only [List.map_cons, setsL_cons]
      rw [setsL_other _ _ Y (by simpa using hY)]
      simp

section Post
variable {tc : ℕ} (p : Program) (cap : ℕ)

local notation "WSp" => WState (NS tc p.tapeCount) NR

/-- The time constructor's output stream. -/
def ko : Fin (NS tc p.tapeCount + 1) := sK p.outputTape

/-- The ten stored numbers, all written `num (g+2) 0` first. -/
def numList : List (Fin (NS tc p.tapeCount + 1)) := [sZ, sLO, sHI, sFU, sQ, sTMP, sXH, sONE, sSV, sFF]

theorem numList_nodup : (numList (tc := tc) p).Nodup := by
  simp [numList, sZ, sLO, sHI, sFU, sQ, sTMP, sXH, sONE, sSV, sFF, Fin.ext_iff]

/-- Everything after the clock. -/
noncomputable def postP : WMX (NS tc p.tapeCount) NR :=
  .seq (tuP sTLI (ko p) sTU r0 r1 rC rG)
  (.seq (guP sNU sGU r0 r1 rC)
  (.seq (muP sCODE sMU r0 rC rG)
  (.seq (xuP sGU sMU sNU sXU r0 r1 rC rG)
  (.seq (zerosP sGU r0 r1 (numList p))
  (.seq (bit0P sONE)
  (.seq (bitGP sGU sSV r0 r1)
  (.seq (ffP sGU sFF sONE r0 bF bR) (flagsP (tc := tc) (tT := p.tapeCount)))))))))

/-- The state `postP` leaves. -/
def postSt (ρ : WSp) (code : List Bool) (N n : ℕ) : WSp :=
  let g := N / 16
  let m := code.foldl idx 1
  let σ4 := (((ρ.sets sTU (List.replicate n true)).sets sGU (List.replicate g true)).sets sMU
    (List.replicate m true)).sets sXU (List.replicate (N - g - m - 2) true)
  let σ5 := setsL σ4 ((numList p).map fun X => (X, num (g + 2) 0))
  let σ8 := ((σ5.sets sONE (num (g + 2) 1)).sets sSV (num (g + 2) (2 ^ g))).sets sFF (num (g + 2) (g + 1))
  setsL σ8 ((flagList (tc := tc) (tT := p.tapeCount)).map fun q => (q.1, [q.2]))

/-- The cost bound of `postP`. -/
def postBound (c m N n s : ℕ) : ℕ :=
  40 * n + 50 * (s + 1) + 200 * (N + 1) + (c * (40 * m + 50) + 10) + 60 * (N + 1) + 10 * (50 * (N / 16 + 2) + 1) + 5 +
    60 * (N / 16 + 1) + (N / 16 + 1) * (41 * (N / 16 + 2) + 20) + 14 + 20

-- Evaluate a stream of a state built by `sets`/`setsL` on R's layout.
set_option hygiene false in
macro "ev" : tactic => `(tactic| ((try simp [Function.update_apply, Fin.ext_iff, setsL_sh, setsL_val, numList,
  flagList, ko, hsh, hv, hTLI, hKO, hTU, hNU, hGU, hCODE, hMU, hXU]) <;> (try omega)))

set_option maxHeartbeats 400000 in
theorem post_spec (ρ : WSp) (code : List Bool) (N n s : ℕ) (hsh : ∀ i, ρ.sh i = 0) (hv : ∀ r, ρ.val r = 0)
    (hTLI : ρ.st sTLI = List.replicate s true) (hKO : ρ.st (ko p) = n.bits) (hn : n < 2 ^ s)
    (hTU : ρ.st sTU = []) (hNU : ρ.st sNU = List.replicate N true) (hGU : ρ.st sGU = [])
    (hCODE : ρ.st sCODE = RepairOrdinary.frame code) (hMU : ρ.st sMU = []) (hXU : ρ.st sXU = [])
    (hnum : ∀ X ∈ numList p, ρ.st X = []) (hfl : ∀ q ∈ flagList (tc := tc) (tT := p.tapeCount), ρ.st q.1 = [])
    (hN : N / 16 + code.foldl idx 1 + 2 ≤ N)
    (hcap : 4 * (code.length + code.foldl idx 1 + N + n + s + 20) ≤ cap) :
    WXExec cap (postP p) ρ (postSt p ρ code N n) (postBound code.length (code.foldl idx 1) N n s) := by
  set g := N / 16 with hg
  set m := code.foldl idx 1 with hm
  have hko : ∀ X : Fin (NS tc p.tapeCount + 1), X.val < 41 → X ≠ ko p := fun X hX h => by
    rw [h] at hX; simp only [ko, sK_val] at hX; omega
  -- TU
  have e1 := tu_spec cap sTLI (ko p) sTU r0 r1 rC rG (hko _ (by simp)) (by ds) ((hko _ (by simp)).symm)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ρ n.bits n s (Clock.rd_bits n) hn hTLI
    (hsh _) hKO (hsh _) hTU (hsh _) (hv _) (hv _) (hv _) (hv _) (by omega)
  set σ1 := ρ.sets sTU (List.replicate n true) with hσ1
  have S1 : ∀ i, σ1.sh i = 0 := fun i => by rw [hσ1]; exact hsh i
  have V1 : ∀ r, σ1.val r = 0 := fun r => by rw [hσ1]; exact hv r
  -- GU
  have e2 := gu_spec cap sNU sGU r0 r1 rC (by ds) (by decide) (by decide) (by decide) σ1 N (by rw [hσ1]; ev)
    (S1 _) (by rw [hσ1]; ev) (S1 _) (V1 _) (V1 _) (V1 _) (by omega)
  set σ2 := σ1.sets sGU (List.replicate g true) with hσ2
  have S2 : ∀ i, σ2.sh i = 0 := fun i => by rw [hσ2]; exact S1 i
  have V2 : ∀ r, σ2.val r = 0 := fun r => by rw [hσ2]; exact V1 r
  -- MU
  have e3 := mu_spec cap sCODE sMU r0 rC rG (by ds) (by decide) (by decide) (by decide) σ2 code
    (by rw [hσ2, hσ1]; ev) (S2 _) (by rw [hσ2, hσ1]; ev) (S2 _) (V2 _) (V2 _) (V2 _) (by omega)
  set σ3 := σ2.sets sMU (List.replicate m true) with hσ3
  have S3 : ∀ i, σ3.sh i = 0 := fun i => by rw [hσ3]; exact S2 i
  have V3 : ∀ r, σ3.val r = 0 := fun r => by rw [hσ3]; exact V2 r
  -- XU
  have e4 := xu_spec cap sGU sMU sNU sXU r0 r1 rC rG (by ds) (by ds) (by ds) (by ds) (by ds) (by ds) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) σ3 g m N hN
    (by rw [hσ3, hσ2, hσ1]; ev) (by rw [hσ3, hσ2, hσ1]; ev) (by rw [hσ3, hσ2, hσ1]; ev)
    (by rw [hσ3, hσ2, hσ1]; ev) (S3 _) (S3 _) (S3 _) (S3 _) (V3 _) (V3 _) (V3 _) (V3 _) (by omega)
  set σ4 := σ3.sets sXU (List.replicate (N - g - m - 2) true) with hσ4
  have S4 : ∀ i, σ4.sh i = 0 := fun i => by rw [hσ4]; exact S3 i
  have V4 : ∀ r, σ4.val r = 0 := fun r => by rw [hσ4]; exact V3 r
  -- the ten numbers
  have e5 := zeros_spec cap sGU r0 r1 (by decide) g (by omega) (numList p) σ4 (numList_nodup p)
    (by simp [numList, sGU, sZ, sLO, sHI, sFU, sQ, sTMP, sXH, sONE, sSV, sFF, Fin.ext_iff])
    (by rw [hσ4, hσ3, hσ2, hσ1]; ev) (S4 _) (V4 _) (V4 _)
    (fun X hX => by
      have h0 := hnum X hX
      simp only [numList, List.mem_cons, List.not_mem_nil, or_false] at hX
      refine ⟨?_, S4 _⟩
      rw [hσ4, hσ3, hσ2, hσ1]
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [Function.update_apply, Fin.ext_iff] using h0)
  set σ5 := setsL σ4 ((numList p).map fun X => (X, num (g + 2) 0)) with hσ5
  have S5 : ∀ i, σ5.sh i = 0 := fun i => by rw [hσ5, setsL_sh]; exact S4 i
  have V5 : ∀ r, σ5.val r = 0 := fun r => by rw [hσ5, setsL_val]; exact V4 r
  have h5 : ∀ X : Fin (NS tc p.tapeCount + 1), X ∉ numList p → σ5.st X = σ4.st X := fun X hX =>
    setsL_other σ4 _ X (by simpa [List.map_map] using hX)
  have h5n : ∀ X ∈ numList p, σ5.st X = num (g + 2) 0 := fun X hX => by
    rw [hσ5]; exact setsL_const_mem _ _ _ X hX
  have hGU5 : σ5.st sGU = List.replicate g true := by
    rw [h5 _ (by simp [numList, sGU, sZ, sLO, sHI, sFU, sQ, sTMP, sXH, sONE, sSV, sFF, Fin.ext_iff]), hσ4, hσ3, hσ2,
      hσ1]; ev
  -- ONE, SV, FF
  have e6 := bit0_spec cap sONE σ5 g (h5n _ (by simp [numList])) (S5 _)
  set σ6 := σ5.sets sONE (num (g + 2) 1) with hσ6
  have S6 : ∀ i, σ6.sh i = 0 := fun i => by rw [hσ6]; exact S5 i
  have V6 : ∀ r, σ6.val r = 0 := fun r => by rw [hσ6]; exact V5 r
  have nG1 : (sGU : Fin (NS tc p.tapeCount + 1)) ≠ sONE := by ds
  have nG2 : (sGU : Fin (NS tc p.tapeCount + 1)) ≠ sSV := by ds
  have nG3 : (sGU : Fin (NS tc p.tapeCount + 1)) ≠ sFF := by ds
  have nS1 : (sSV : Fin (NS tc p.tapeCount + 1)) ≠ sONE := by ds
  have nF1 : (sFF : Fin (NS tc p.tapeCount + 1)) ≠ sONE := by ds
  have nF2 : (sFF : Fin (NS tc p.tapeCount + 1)) ≠ sSV := by ds
  have e7 := bitG_spec cap sGU sSV r0 r1 nG2 (by decide) σ6 g
    (by rw [hσ6, WState.sets_st, Function.update_of_ne nG1, hGU5]) (S6 _)
    (by rw [hσ6, WState.sets_st, Function.update_of_ne nS1]; exact h5n _ (by simp [numList]))
    (S6 _) (V6 _) (V6 _) (by omega)
  set σ7 := σ6.sets sSV (num (g + 2) (2 ^ g)) with hσ7
  have S7 : ∀ i, σ7.sh i = 0 := fun i => by rw [hσ7]; exact S6 i
  have V7 : ∀ r, σ7.val r = 0 := fun r => by rw [hσ7]; exact V6 r
  have e8 := ff_spec cap sGU sFF sONE r0 bF bR nG3 nG1 nF1 (by decide) (by decide) (by decide) σ7 g
    (by rw [hσ7, WState.sets_st, Function.update_of_ne nG2, hσ6, WState.sets_st, Function.update_of_ne nG1, hGU5])
    (S7 _)
    (by rw [hσ7, WState.sets_st, Function.update_of_ne nF2, hσ6, WState.sets_st, Function.update_of_ne nF1]
        exact h5n _ (by simp [numList]))
    (S7 _) (by rw [hσ7, WState.sets_st, Function.update_of_ne nS1.symm, hσ6, WState.sets_st, Function.update_self])
    (S7 _) (V7 _) (V7 _) (V7 _) (by omega)
  set σ8 := σ7.sets sFF (num (g + 2) (g + 1)) with hσ8
  have S8 : ∀ i, σ8.sh i = 0 := fun i => by rw [hσ8]; exact S7 i
  have e9 := wrs_spec cap (flagList (tc := tc) (tT := p.tapeCount)) σ8 flagList_nodup (fun q hq => by
    have h0 := hfl q hq
    simp only [flagList, List.mem_cons, List.not_mem_nil, or_false] at hq
    refine ⟨?_, S8 _⟩
    rw [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [Function.update_apply, Fin.ext_iff, setsL, numList] using h0)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6 (WXExec.seq e7
    (WXExec.seq e8 e9)))))))).mono ?_
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9
  simp only [postBound, flagList, List.length_cons, List.length_nil, numList]
  nlinarith

end Post

end NearCubicGates.Adapters.Refuter.RM
