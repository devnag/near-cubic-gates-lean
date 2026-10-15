import Proof.Gates.Expand.PolyTabStage9h

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc enc_length stp)
open StablePartition.Workspace (overlay)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-- The state after stage 9. -/
structure S9End (VT : List Bool) (σA : WSt) (O46 O56 : List Bool) (f : Fin 64 → ℕ) (τ : WSt) : Prop where
  z46 : τ.st (sZ 46) = O46 ++ [false]
  z46h : τ.sh (sZ 46) = 0
  z56 : τ.st (sZ 56) = O56 ++ [false]
  z56h : τ.sh (sZ 56) = 0
  r37 : τ.val (rX 37) = 0
  r38 : τ.val (rX 38) = 0
  x : ∀ j : Fin 64, XR j → τ.val (rX j) = f j
  vt : τ.st (sS 4) = VT
  vth : τ.sh (sS 4) = 0
  fr : SameExcept σA τ MSS RXL

def st9Cost (Wb Wc ℓ M X K Y N L46 L56 : ℕ) : ℕ :=
  readBinCost Wb ℓ + 1 + ((N * (83 * Wb + 30) + 41 * Wb + 14) + 1 + ((N * (mnCost Wb Wc ℓ M X K Y + 4) + 1) + 1 +
    ((5 * L46 + 3) + 1 + (5 * L56 + 3))))

theorem st9_spec (cap : ℕ) {Wb Wc : ℕ} {σA : WSt} (hW : 1 ≤ Wb) (hWc : 1 ≤ Wc) (ys : List ℕ) (ℓ M X K : ℕ)
    (ts : List (List ℕ × ℕ × ℕ)) (hts : ∀ t ∈ ts, MonoOKs Wb Wc ℓ M X K ys t)
    (inp : List Bool) (hinp : inp = encN (ts.length :: ts.flatMap fl) ++ [false]) (f : Fin 64 → ℕ) (hf : FZ f K)
    (hf32 : f 32 = 0) (q2 q3 : (Fin 10 → ℕ) → Prop) (L5 : List Bool) (τ : WSt)
    (h : MS Wb Wc inp (recStream (ys.map (binary Wb))) σA 0 [] [] [] L5 f q2 q3 τ)
    (hNW : ts.length < 2 ^ Wb) (hℓN : natBitLength ts.length ≤ ℓ) (hcap : capMono Wb Wc ℓ M X K ys.length ≤ cap)
    (hcap46 : (ts.flatMap (blk46 Wb K ys)).length + 2 * Wb + 2 + M * (K * (2 * Wb + 1)) + 1 ≤ cap)
    (hcap56 : (ts.flatMap (blk56 Wc)).length + 2 * Wc + 2 ≤ cap) (hcapN : ts.length + 2 * Wb + 2 ≤ cap) :
    Runs cap st9 τ (st9Cost Wb Wc ℓ M X K ys.length ts.length (ts.flatMap (blk46 Wb K ys)).length
        (ts.flatMap (blk56 Wc)).length)
      (S9End (recStream (ys.map (binary Wb))) σA (ts.flatMap (blk46 Wb K ys)) (ts.flatMap (blk56 Wc))
        (Function.update f 32 0)) := by
  set N := ts.length with hN
  have hinp1 : inp = [] ++ enc true (natWord N) ++ (encN (ts.flatMap fl) ++ [false]) := by rw [hinp, encN_cons]; simp
  obtain ⟨τ1, e1, m1⟩ := ms_read2 cap hW 0 q2 q3 τ h N [] _ hinp1 rfl (by unfold capMono at hcap; omega) (by omega)
  rw [Nat.mod_eq_of_lt hNW] at m1
  obtain ⟨τ2, e2, m2⟩ := ms_toReg2 cap _ q3 N 32 (by decide) (by decide) τ1 m1 hf.z3 hf.z4 hf.z6 hNW (by omega)
    (by rw [hf32]; omega)
  have eA : ([] : List Bool).length + 2 * (natWord N).length = (enc true (natWord N)).length := by
    rw [encT_length]; simp
  rw [eA] at m2
  obtain ⟨τ3, e3, L5', m3⟩ := monoLoop_spec cap hW hWc ys ℓ M X K ts hts (enc true (natWord N)) [false]
    (by rw [hinp, encN_cons]) _ (hf.upd 32 (by decide) _) _ _ L5 τ2 m2 (by simp [hf32, hN]) hcap hcap46 hcap56 (by omega)
  set O46 := ts.flatMap (blk46 Wb K ys) with hO46
  set O56 := ts.flatMap (blk56 Wc) with hO56
  have e4 := closeOut_spec cap τ3 O46 [] m3.out46 (by omega)
  set τ4 := ((τ3.sets (sZ 46) (overlay (O46 ++ [false]) [])).seth (sZ 46) 0).setv (rX 37) 0 with hτ4
  have hS4 : SameExcept τ3 τ4 [sZ 46] [rX 37] := se_out τ3 _ _ _ _ _
  have h56 : OutOn τ4 (sZ 56) (rX 38) O56 [] := out_tr m3.out56 hS4 (nm1 (by polyTabNe)) (nm1 (by polyTabNe))
  have e5 := closeOut_spec cap τ4 O56 [] h56 (by omega)
  set τ5 := ((τ4.sets (sZ 56) (overlay (O56 ++ [false]) [])).seth (sZ 56) 0).setv (rX 38) 0 with hτ5
  have hS5 : SameExcept τ4 τ5 [sZ 56] [rX 38] := se_out τ4 _ _ _ _ _
  have nx : ∀ j : Fin 64, XR j → ∀ k : Fin 64, k.val ∈ [37, 38] → rX j ∉ [rX k] := fun j hj k hk hm => by
    simp only [List.mem_singleton] at hm
    have := rX.injective hm; subst this
    unfold XR at hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj hk; omega
  refine ⟨τ5, WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq (WXExec.wm e4) (WXExec.wm e5)))) |>.mono ?_, ?_⟩
  · have a1 := readBinCost_mono Wb hℓN
    try simp only [hf32, Nat.zero_add]
    rw [← hN] at *
    unfold st9Cost; omega
  · refine ⟨?_, ?_, by simp [hτ5, overlay], by simp [hτ5], ?_, by simp [hτ5], ?_, ?_, ?_, ?_⟩
    · rw [hS5.st (nm1 (by polyTabNe))]; simp [hτ4, overlay]
    · rw [hS5.sh (nm1 (by polyTabNe))]; simp [hτ4]
    · rw [hS5.val (nm1 (by polyTabNe))]; simp [hτ4]
    · intro j hj
      rw [hS5.val (nx j hj 38 (by simp)), hS4.val (nx j hj 37 (by simp))]
      exact (m3.x j hj).trans (by
        by_cases j32 : j = 32
        · subst j32; simp
        · simp [Function.update_apply, j32])
    · rw [hS5.st (nm1 (by polyTabNe)), hS4.st (nm1 (by polyTabNe))]; exact m3.vt
    · rw [hS5.sh (nm1 (by polyTabNe)), hS4.sh (nm1 (by polyTabNe))]; exact m3.vth
    · exact se_ext (se_ext m3.fr hS4 (fun X hX => by simp only [List.mem_singleton] at hX; subst hX; exact mss_z46)
        (by simp [rX_mem])) hS5 (fun X hX => by simp only [List.mem_singleton] at hX; subst hX; exact mss_z56)
        (by simp [rX_mem])

end NearCubicGates.Close.Expand.PolyTab
