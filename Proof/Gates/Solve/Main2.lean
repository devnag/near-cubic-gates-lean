import Proof.Gates.Solve.Main

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
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces (intWord listWord)
open NearCubicGates.Close.Interfaces.Formats (SysReq sysWord solveWord)
open NearCubicGates.Close.Interfaces (startState)

theorem outRegs_cases {r : Reg} (hr : r ∈ outRegs) :
    r ∈ elimRegs ∨ (r ∉ elimRegs ∧ r ∉ bRegs ∧ r ≠ rR2 ∧ r ≠ rWL ∧ r ≠ rLL) := by
  revert r; decide

theorem hcap_parts (ℓ : ℕ) : setupCap ℓ ≤ capT ℓ ∧ capB ℓ ℓ ℓ (wOf ℓ) ≤ capT ℓ ∧
    capE (2 * ℓ * (ℓ + 1)) (wOf ℓ) ≤ capT ℓ ∧ ℓ + 2 * (wOf ℓ + 1) + 2 ≤ capT ℓ := by
  unfold capT; omega

theorem main_run (s : SysReq) : ∃ τ, WXExec (capT (sysWord s).length) mainP (startState NS NR (sysWord s)) τ
    (mainCost s) ∧ τ.st sOUT = solveWord (solve s) ∧ (∀ i, τ.sh i = 0) ∧ ∀ q, τ.val q = 0 := by
  have hmℓ : s.rows.length ≤ (sysWord s).length := rows_len_le s
  have hnℓ : s.pts.length ≤ (sysWord s).length := pts_len_le s
  have hℓ1 : 1 ≤ (sysWord s).length := sysWord_pos s
  have hrb : ReqBound s (sysWord s).length := reqBound_of s
  obtain ⟨hcS, hcB, hcE, hcR⟩ := hcap_parts (sysWord s).length
  set word := sysWord s with hword
  set ℓ := word.length with hℓ
  set W := wOf ℓ with hW
  set m := s.rows.length with hm
  set n := s.pts.length with hn
  set cap := capT ℓ with hcapd
  have hℓW : ℓ + 2 ≤ W := by rw [hW]; unfold wOf; nlinarith
  have hRC : (m + n) * (n + 1) ≤ 2 * ℓ * (ℓ + 1) := RC_le hmℓ hnℓ
  have hcapB : capB m n ℓ W ≤ cap := le_trans (capB_le hmℓ hnℓ) hcB
  have hcapE : capE ((m + n) * (n + 1)) W ≤ cap := le_trans (capE_le hRC) hcE
  have hcapR : n + 2 * (W + 1) + 2 ≤ cap := by omega
  -- 1. setup
  have e0 := setup_spec cap word hcS
  have hA0 := setup_at word
  obtain ⟨-, hraw, hrul, hst0⟩ := setS_st_data word
  have hc0 : RawCtx (setS word) W word := ⟨hraw, hrul, setS_sh word _, by rw [setS_val, if_pos rfl]⟩
  have hLL : (setS word).val rLL = ℓ := by rw [setS_val, if_neg (by decide), if_neg (by decide), if_pos rfl]
  have hWL0 : (setS word).val rWL = W + 1 := by rw [setS_val, if_neg (by decide), if_pos rfl]
  have hR20 : (setS word).val rR2 = 2 * (W + 1) + 1 := by rw [setS_val, if_pos rfl]
  have hzb : ∀ r ∈ bRegs, (setS word).val r = 0 := fun r hr => by
    obtain ⟨h1, h2, h3⟩ := bRegs_setS hr; exact setS_zero word h1 h2 h3
  -- 2. build
  obtain ⟨τ1, e1, σ1, v1, h1, hMAT1, hsh1, hNN1, hMM1, hRR1, hCC1, hCM1, hfr1, -, hDD1⟩ :=
    build_spec cap hA0 s hc0 hrb (setS_sh word) hLL hzb (by decide) (hst0 sPT (by decide)) (hst0 sMAT (by decide))
      hℓW hℓ1 le_rfl hcapB
  -- 3. elimination
  have hEC : ElimCtx σ1 W (m + n) (n + 1) m n (amat s) (bdOf n ℓ) [] := by
    refine ⟨⟨by omega, by omega, by omega, hRR1, hCC1, hMM1, fun k hk i j _ _ => (bareiss_bd hrb hk).1 i j,
      fun k hk => (bareiss_bd hrb hk).2, fun k _ => ?_, bd_width hnℓ⟩, by rw [hMAT1, List.append_nil],
      hsh1 sMAT (by decide), hsh1 sNEW (by decide), hsh1 sWR (by decide), ?_, hNN1, ?_⟩
    · obtain ⟨_, _, _, hI, _⟩ := run_inv (amat s) m k; exact hI.ne
    · rw [hfr1.st (by decide), hst0 sWR (by decide)]; simp
    · intro r hr
      rcases elimRegs_cases hr with rfl | ⟨h0, h1', h2, h3⟩
      · exact hCM1
      · rw [hfr1.val h0]; exact setS_zero word h1' h2 h3
  obtain ⟨τ2, e2, σ2, v2, h2, ⟨junk2, hMAT2⟩, hMATh2, hNEWh2, hWRh2, -, hz2, hfr2, hDD2⟩ :=
    elim_spec cap h1 hEC (by rw [hDD1]; decide) hcapE
  -- 4. output
  have hD0 : (final s).D ≠ 0 := by obtain ⟨_, _, _, hI, _⟩ := run_inv (amat s) m n; exact hI.ne
  have hBdW : bdOf n ℓ < 2 ^ W := by
    have h5 := bd_width hnℓ; have h6 := bdOf_pos n ℓ
    have h7 : bdOf n ℓ ≤ 2 * bdOf n ℓ * bdOf n ℓ := by nlinarith
    rw [hW]; omega
  have hpw : 2 ^ W < 2 ^ (W + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hv2 : ∀ r, r ∉ elimRegs → r ∉ bRegs → σ2.val r = (setS word).val r := fun r h h' => by
    rw [hfr2.val h, hfr1.val h']
  have hDlt : (final s).D.natAbs < 2 ^ W := lt_of_le_of_lt (bareiss_bd hrb le_rfl).2 hBdW
  have hylt : ∀ i, ((final s).a i n).natAbs < 2 ^ W := fun i => lt_of_le_of_lt ((bareiss_bd hrb le_rfl).1 i n) hBdW
  have hnW : n < 2 ^ (W + 1) := by
    have : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
    have : 2 ^ ℓ ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hOP : OPar σ2 W (m + n) (n + 1) m n (final s).a (final s).D junk2 := by
    refine ⟨⟨hMAT2, hMATh2⟩, le_rfl, by omega, by nlinarith, by rw [hfr2.val (by decide), hCC1],
      by rw [hfr2.val (by decide), hNN1], by rw [hfr2.val (by decide), hMM1],
      by rw [hv2 _ (by decide) (by decide), hWL0], by rw [hv2 _ (by decide) (by decide), hR20], ?_, ?_, ?_, hD0, hDlt,
      fun i _ => hylt i, hnW⟩
    · intro r hr
      rcases outRegs_cases hr with h | ⟨h0, h0', h1', h2', h3'⟩
      · exact hz2 r h
      · rw [hv2 r h0 h0']; exact setS_zero word h1' h2' h3'
    · rw [hfr2.st (by decide), hfr1.st (by decide), hst0 sOUT (by decide)]
    · rw [hfr2.sh (by decide)]; exact hsh1 sOUT (by decide)
  obtain ⟨τ3, e3, σ3, v3, h3, hO3, hOh3, hfr3⟩ := out_spec cap h2 hOP (by rw [hDD2]; rfl) hcapE
  -- 5. rewind the output
  have hlen := outW_length (final s).a (final s).D m n W (by omega) (fun j _ => by have := hylt (m + j); omega) hnW
  obtain ⟨τ4, e4, σ4, h4, hsh4, hst4, hfr4⟩ := rewOut_spec cap h3 (n := n)
    (by rw [hfr3.val (by decide), hv2 _ (by decide) (by decide)]; exact setS_zero word (by decide) (by decide) (by decide))
    (by rw [hfr3.val (by decide), hfr2.val (by decide), hNN1])
    (by rw [hfr3.val (by decide), hv2 _ (by decide) (by decide), hR20]) (by rw [hOh3, hO3]; exact hlen) hcapR
  -- 6. clear the registers
  have hb0 : ∀ r, (startState NS NR word).val r ≤ cap := fun r => by simp [startState]
  have hb4 : ∀ r, τ4.val r ≤ cap :=
    WXExec.val_le e4 (WXExec.val_le e3 (WXExec.val_le e2 (WXExec.val_le e1 (WXExec.val_le e0 hb0))))
  obtain ⟨τ5, e5, hsh5, hst5, hv5⟩ := clearAll_spec cap (List.finRange NR) τ4 hb4
  refine ⟨τ5, WXExec.seq e0 (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))), ?_, ?_, ?_⟩
  · rw [hst5, h4.st (by decide), hst4, hO3, solveWord_eq]; rfl
  · intro i
    rw [hsh5]
    by_cases hi : i ∈ wset
    · exact (h4.num hi).2
    · rw [h4.sh hi]
      by_cases hiO : i = sOUT
      · subst hiO; exact hsh4
      · rw [hfr4.sh (by simp [hiO]), hfr3.sh (by simp [hiO])]
        by_cases hM : i = sMAT
        · subst hM; exact hMATh2
        · by_cases hN : i = sNEW
          · subst hN; exact hNEWh2
          · by_cases hR : i = sWR
            · subst hR; exact hWRh2
            · rw [hfr2.sh (by simp [hM, hN, hR])]; exact hsh1 i hi
  · intro q; rw [hv5 q, if_pos (List.mem_finRange q)]

end NearCubicGates.Close.Solve
