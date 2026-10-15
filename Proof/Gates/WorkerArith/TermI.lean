import Proof.Gates.WorkerArith.TermH

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord ratWord NCircuit circuitWord listWord)
open NearCubicGates.Close.Codec (oneCallOf pairCallOf cwPrefix rowPrefix emptyCW)
open NearCubicGates.Close.Worker (Opd model1 model2)

variable {ns nr : ℕ}

section Two
variable {E : TermEnv ns nr} {t : ℕ} {tmap : Fin t → Fin (ns + 1)} {q : ℕ} {Cs : ℕ → NCircuit q} {N : ℕ}
  {rows : ℕ → List ℕ} {Rn : ℕ} {ω : ℚ} {w pre rest : List Bool} {Z B V : ℕ} {σ : WState ns nr}

/-- A term base with the flip register `R 39` set. -/
theorem TermBase.set39 (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (x : ℕ) :
    TermBase E tmap Cs N rows Rn w pre rest (σ.setv (E.R 39) x) := by
  have hv : ∀ k : Fin 40, k ≠ 39 → (σ.setv (E.R 39) x).val (E.R k) = σ.val (E.R k) := fun k hk => by
    simp [Function.update_of_ne (R_ne E hk)]
  exact ⟨hB.inj, hB.tdis, hB.nd, hB.cw, hB.cwh, by rw [hv 7 (by decide)]; exact hB.cwL, hB.sup, hB.suph,
    by rw [hv 8 (by decide)]; exact hB.supL, hB.b1, hB.h1, hB.b2, hB.h2, hB.bt, hB.ht, hB.bTL, hB.hTL, hB.bG, hB.hG,
    hB.bL, hB.hL, hB.wt, hB.wth, hB.vi, by rw [hv 6 (by decide)]; exact hB.hq,
    fun i a b => by rw [hv i (Fin.ne_of_val_ne (by omega))]; exact hB.z i a b⟩

theorem qS_rwS_ne (R : Fin 40 ↪ Fin nr) (i : Fin 12) (k : Fin 16) : qS R i ≠ rwS R k := by
  rw [qS_apply, rwS_apply]; intro h; have h' := R.injective h
  have : ∀ i : Fin 12, ∀ k : Fin 16, qIdx i ≠ sIdx k := by decide
  exact this i k h'

/-- The exact ending with the call stream emptied reads like the exact ending. -/
theorem exactEnd_S1 (hB : TermBase E tmap Cs N rows Rn w pre rest σ) (hW : ℕ) (entry : List Bool) :
    SimW (exactEnd E σ hW entry) (exactEnd E (σ.sets E.S1 []) hW entry) := by
  obtain ⟨-, -, ⟨h12, h1T, h1G, h1L, h1V, h1W⟩, ⟨h2T, h2G, h2L, h2V, h2W⟩, -, ⟨hGL, hGV, hGW⟩, -, -⟩ := hB.dis
  refine ⟨rfl, rfl, rfl, fun i => ?_⟩
  simp only [exactEnd, appendO, WState.setv, WState.seth, WState.sets]
  by_cases hiV : i = E.VI
  · subst hiV
    simp only [Function.update_self, Function.update_of_ne (Ne.symm hGV), Function.update_of_ne (Ne.symm h2V),
      Function.update_of_ne (Ne.symm h1V)]
    exact RdEq.refl _
  simp only [Function.update_of_ne hiV]
  by_cases iG : i = E.G
  · subst iG; simp only [Function.update_self]; exact RdEq.refl _
  simp only [Function.update_of_ne iG]
  by_cases i2 : i = E.S2
  · subst i2; simp only [Function.update_self]; exact RdEq.refl _
  simp only [Function.update_of_ne i2]
  by_cases i1 : i = E.S1
  · subst i1; simp only [Function.update_self]; exact blank_nil hB.b1
  simp only [Function.update_of_ne i1]; exact RdEq.refl _

/-- **`[sys u, sys v]`** (exact): `p = 1/2` iff the canonical support lists differ. -/
theorem tt_ideal (cap : ℕ) (hB : TermBase E tmap Cs N rows Rn w pre rest σ)
    (hFit : TermFit cap Cs N rows Rn ω w Z B V) (hu : σ.val (E.R 2) < q + Rn) (hv : σ.val (E.R 5) < q + Rn)
    (huZ : σ.val (E.R 2) ≤ Z) (hvZ : σ.val (E.R 5) ≤ Z) (h8 : σ.val (E.R 8) ≤ Z)
    (hOP : σ.val (E.R 9) + 1000 * (Z + 1) ≤ cap) :
    ∃ τ, WXExec cap (.seq (skipFieldW E) (.seq (.wm (suppEqW E.SUP E.S1 E.S2 (rwS E.R) (qS E.R)))
        (.seq (exactEntryNW E.VI (E.R 9) (E.R 39) (E.R 26)) (.wm (WM.clear (E.R 26)))))) σ τ
        (1000000 * (Z + 1) ^ 2 * (B + 1)) ∧
      SimW (termIdeal σ tmap E (pre.length + w.length + 1 + w.length)
        (bitWord (decide (σ.val (E.R 39) ≠ 0)) ++
          outputWord (halfIf (decide (sysList q rows (σ.val (E.R 2)) ≠ sysList q rows (σ.val (E.R 5)))), 0))) τ := by
  obtain ⟨⟨cS, c1, c2, cT, cG, cL, cV, cW⟩, ⟨s1, s2, sT, sG, sL, sV, sW⟩, ⟨h12, h1T, h1G, h1L, h1V, h1W⟩,
    ⟨h2T, h2G, h2L, h2V, h2W⟩, -, ⟨hGL, hGV, hGW⟩, -, hVW⟩ := hB.dis
  set hW := pre.length + w.length + 1 + w.length with hWd
  obtain ⟨τ1, e1, s1'⟩ := skipField_base cap hB hFit
  set ι1 := ((σ.seth E.WT hW).sets E.S2 []).sets E.G [] with hι1
  obtain ⟨fv, fsup, fsuph, fvih, fvis, -⟩ := skip_facts hB hW (E := E)
  obtain ⟨restS, hrs⟩ := hB.sup
  have hcV := hFit.capV
  have hqZ := hFit.qZ
  set u := σ.val (E.R 2) with hud
  set v := σ.val (E.R 5) with hvd
  obtain ⟨τ2, e2, s2'⟩ := suppEqW_spec cap E.SUP E.S1 E.S2 (rwS E.R) (qS E.R) rows Rn q u v B (σ.val (E.R 8)) restS ι1
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
        exact ⟨⟨s1, s2⟩, h12, fun h => h⟩)
    (qS_rwS_ne E.R) hu hv hFit.rowB hFit.rowfit (by omega) (by rw [fsup, hrs]) (by rw [fsuph, hB.suph]; omega) hB.supL
    (by simp only [hι1, WState.sets, WState.seth, Function.update_of_ne h1G, Function.update_of_ne h12]; exact hB.b1)
    (by simp only [hι1, WState.sets, WState.seth]; rw [Function.update_of_ne h1W]; exact hB.h1)
    (by simp only [hι1, WState.sets]; rw [Function.update_of_ne h2G, Function.update_self]; intro p; rfl)
    (by simp only [hι1, WState.sets, WState.seth]; rw [Function.update_of_ne h2W]; exact hB.h2)
    (fun k _ _ _ => by rw [fv, rwS_apply]
                       have : 10 ≤ (sIdx k).val ∧ (sIdx k).val ≤ 25 := by fin_cases k <;> simp [sIdx]
                       exact hB.z _ this.1 (by omega))
    (fun i hi => by rw [fv, qS_apply]
                    have : 26 ≤ (qIdx i).val ∧ (qIdx i).val ≤ 33 := by
                      fin_cases i <;> simp_all [qIdx]
                    exact hB.z _ (by omega) (by omega))
    (by rw [fv]; rfl) (by rw [fv]; rfl) (by rw [fv, qS_apply]; exact hB.hq) (by rw [fv]; rfl)
  set eqb := decide (sysList q rows u = sysList q rows v) with heqb
  set ι2 := suppIdeal ι1 E.SUP E.S1 E.S2 (qS E.R 4) eqb with hι2
  have i2v : ι2.val = Function.update σ.val (E.R 26) eqb.toNat := by
    simp only [hι2, suppIdeal, WState.setv, WState.seth, WState.sets, fv]; rfl
  have e3 := exactEntryNW_spec cap E.VI (E.R 9) (E.R 39) (E.R 26) (R_ne E (by decide)) ι2
    (by simp only [hι2, suppIdeal, WState.setv, WState.seth, WState.sets, Function.update_of_ne (Ne.symm h2V),
          Function.update_of_ne (Ne.symm h1V), Function.update_of_ne (Ne.symm sV)]
        rw [fvih, fvis]; exact hB.vi)
    (by rw [i2v, Function.update_of_ne (R_ne E (by decide))]; omega)
  rw [i2v, Function.update_of_ne (R_ne E (show (39 : Fin 40) ≠ 26 by decide)), Function.update_self] at e3
  have hflag : decide (eqb.toNat = 0) = decide (sysList q rows u ≠ sysList q rows v) := by
    rw [heqb]; by_cases h : sysList q rows u = sysList q rows v <;> simp [h]
  rw [hflag] at e3
  set m := marks (bitWord (decide (σ.val (E.R 39) ≠ 0)) ++
    outputWord (halfIf (decide (sysList q rows u ≠ sysList q rows v)), 0)) with hm
  have e4 := wclear_spec (cap := cap) (E.R 26) eqb.toNat (appendO ι2 E.VI (E.R 9) m)
    (by simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val]
        rw [Function.update_of_ne (R_ne E (by decide)), i2v, Function.update_self])
    (by simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val]
        rw [Function.update_of_ne (R_ne E (by decide)), i2v, Function.update_self]; cases eqb <;> simp <;> omega)
  have hend : (appendO ι2 E.VI (E.R 9) m).setv (E.R 26) 0 = exactEnd E (σ.sets E.S1 []) hW
      (bitWord (decide (σ.val (E.R 39) ≠ 0)) ++ outputWord (halfIf (decide (sysList q rows u ≠ sysList q rows v)), 0)) := by
    have k1 := hB.h1; have k2 := hB.h2; have k3 := hB.suph
    refine WState.eq ?_ ?_ ?_ rfl
    · funext i
      simp only [hι2, suppIdeal, hι1, exactEnd, appendO, WState.setv, WState.seth, WState.sets, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext i
      simp only [hι2, suppIdeal, hι1, exactEnd, appendO, WState.setv, WState.seth, WState.sets, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext r
      simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val, exactEnd]
      rw [i2v]
      by_cases r26 : r = E.R 26
      · subst r26; rw [Function.update_self, Function.update_of_ne (R_ne E (by decide))]
        exact (hB.z 26 (by decide) (by decide)).symm
      rw [Function.update_of_ne r26]
      by_cases r9 : r = E.R 9
      · subst r9; rw [Function.update_self, Function.update_self, Function.update_of_ne (R_ne E (by decide))]
      rw [Function.update_of_ne r9, Function.update_of_ne r9, Function.update_of_ne r26]
  rw [hend] at e4
  obtain ⟨τ, e, s⟩ := Worker.seq_sim e1 s1' (Worker.seq_sim e2 s2' ⟨_, WXExec.seq e3 (WXExec.wm e4), SimW.refl _⟩)
  refine ⟨τ, WXExec.mono e ?_,
    CheckedPCPP.SimW.trans (CheckedPCPP.SimW.trans (exactEnd_simW hB hW _) (exactEnd_S1 hB hW _)) s⟩
  have hb1 : eqb.toNat ≤ 1 := by cases eqb <;> simp
  have hwZ := hFit.wZ
  unfold suppCost
  have hK : (σ.val (E.R 8) + q + u + v + 1) ^ 2 * (B + 1) ≤ 16 * ((Z + 1) ^ 2 * (B + 1)) := by
    have a : σ.val (E.R 8) + q + u + v + 1 ≤ 4 * (Z + 1) := by omega
    have b : (σ.val (E.R 8) + q + u + v + 1) ^ 2 ≤ (4 * (Z + 1)) ^ 2 := Nat.pow_le_pow_left a 2
    calc (σ.val (E.R 8) + q + u + v + 1) ^ 2 * (B + 1) ≤ (4 * (Z + 1)) ^ 2 * (B + 1) := Nat.mul_le_mul_right _ b
      _ = 16 * ((Z + 1) ^ 2 * (B + 1)) := by ring
  have h2 : Z + 1 ≤ (Z + 1) ^ 2 * (B + 1) := by nlinarith
  have eq : 1000000 * (Z + 1) ^ 2 * (B + 1) = 1000000 * ((Z + 1) ^ 2 * (B + 1)) := by ring
  have eq2 : 20000 * (σ.val (E.R 8) + q + u + v + 1) ^ 2 * (B + 1) =
      20000 * ((σ.val (E.R 8) + q + u + v + 1) ^ 2 * (B + 1)) := by ring
  rw [eq]
  try rw [eq2]
  omega

end Two

end NearCubicGates.Close.WorkerArith
