import Proof.Gates.TabMachine.CompileM7

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

section Zero
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

/-- The constant child: `n` zero fields (`R 13 = n`), the field on `S T`, the end marker. -/
def zeroEq (T : Fin 24) : WMX ns nr :=
  .seq (repK (R 13) (R 19) (fieldO (S 20) (S 2) (R 15) (R 14)))
    (.seq (fieldO (S T) (S 2) (R 15) (R 14)) (emitO (S 2) (R 14) false))

theorem outSt_setv (σ : WState ns nr) (O : Fin (ns + 1)) (CO r : Fin nr) (hr : r ≠ CO) (v : ℕ) (out L0 : List Bool) :
    outSt (σ.setv r v) O CO out L0 = (outSt σ O CO out L0).setv r v := by
  apply WState.eq <;> try rfl
  funext x; by_cases h1 : x = CO
  · subst h1; simp [outSt, Function.update_of_ne (Ne.symm hr)]
  · by_cases h2 : x = r
    · subst h2; simp [outSt, Function.update_of_ne hr]
    · simp [outSt, Function.update_of_ne h1, Function.update_of_ne h2]

theorem zeroEq_spec (cap W : ℕ) (T : Fin 24) (hT : T ≠ 2) (σ : WState ns nr) (n : ℕ) (t : ℤ) (out L0 : List Bool)
    (hZR : NumOn σ (S 20) (W + 1) 0) (hTv : NumOn σ (S T) (W + 1) (encS t)) (hNR : σ.val (R 13) = n)
    (hK3 : σ.val (R 19) = 0) (hCS : σ.val (R 15) = 0) (hKD : OutOn σ (S 2) (R 14) out L0)
    (hcap : out.length + (n + 1) * (2 * (W + 1)) + 2 * n + 2 ≤ cap) :
    WXExec cap (zeroEq S R T) σ (outSt σ (S 2) (R 14) (out ++ frame (recBits W (zeroL n t))) L0)
      (n * (40 * (W + 1) + 3 + 8) + 7 * n + 3 + 1 + (40 * (W + 1) + 3 + 1 + 7)) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  set z := frameP (binary (W + 1) 0) with hz
  have hzl : z.length = 2 * (W + 1) := by rw [hz]; simp [frameP_len]
  have hzs : ∀ k, (List.replicate k z).flatten.length = k * (2 * (W + 1)) := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [List.replicate_succ', List.flatten_append, List.length_append, ih]; simp [hzl]; ring
  have hloop := Runs.repE (cap := cap) (K := R 13) (K2 := R 19) (body := fieldO (S 20) (S 2) (R 15) (R 14))
    (hner (by decide))
    (40 * (W + 1) + 3) n (fun k => outSt σ (S 2) (R 14) (out ++ (List.replicate k z).flatten) L0) (by omega)
    (fun k => by simp [outSt, Function.update_of_ne (hner (show (13 : Fin 24) ≠ 14 by decide))])
    (fun k => by simp [outSt, Function.update_of_ne (hner (show (19 : Fin 24) ≠ 14 by decide))])
    (fun k hk v1 v2 => by
      have h := fieldO_spec cap (hne (show (20 : Fin 24) ≠ 2 by decide)) (hner (show (15 : Fin 24) ≠ 14 by decide))
        (((outSt σ (S 2) (R 14) (out ++ (List.replicate k z).flatten) L0).setv (R 13) v1).setv (R 19) v2)
        (binary (W + 1) 0) [] (out ++ (List.replicate k z).flatten) L0 (by simp [outSt, emb_eq_iff, hZR.1,
          BinW.frame_frameP]) (by simp [outSt, emb_eq_iff, hZR.2])
        (by simp [outSt, emb_eq_iff, Function.update_apply, hCS])
        ⟨by simp [outSt], by simp [outSt], by simp [outSt, emb_eq_iff]⟩
        (by rw [List.length_append, hzs, binary_length]; nlinarith)
      rw [binary_length] at h
      refine h.cast cap ?_ le_rfl
      rw [outSt_setv _ _ _ _ (hner (by decide)), outSt_setv _ _ _ _ (hner (by decide)), outSt_outSt,
        List.replicate_succ', List.flatten_append, List.flatten_singleton, ← List.append_assoc])
    (by simp [outSt, emb_eq_iff, hNR]) (by simp [outSt, emb_eq_iff, hK3])
  have h0 : outSt σ (S 2) (R 14) (out ++ (List.replicate 0 z).flatten) L0 = σ := by
    simpa using outSt_self σ hKD
  rw [h0] at hloop
  have h2 := fieldO_spec cap (hne hT) (hner (show (15 : Fin 24) ≠ 14 by decide))
    (outSt σ (S 2) (R 14) (out ++ (List.replicate n z).flatten) L0) (binary (W + 1) (encS t)) []
    (out ++ (List.replicate n z).flatten) L0
    (by simp only [outSt, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne (hne hT)]
        rw [hTv.1, BinW.frame_frameP])
    (by simp only [outSt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_of_ne (hne hT)]
        exact hTv.2)
    (by simp [outSt, emb_eq_iff, hCS]) (outOn_outSt _ _ _ _ _)
    (by rw [List.length_append, hzs, binary_length]; nlinarith)
  rw [outSt_outSt, binary_length] at h2
  have h3 := emitO_spec cap _ _ L0 false (outOn_outSt σ (S 2) (R 14) (out ++ (List.replicate n z).flatten ++
    frameP (binary (W + 1) (encS t))) L0) (by simp [hzs, frameP_len]; nlinarith)
  rw [outSt_outSt] at h3
  refine (WXExec.seq hloop (WXExec.seq h2 h3)).cast cap ?_ (by omega)
  congr 1
  rw [frame_recBits, zeroL, List.flatMap_append]
  have hr : (List.replicate n (0 : ℤ)).flatMap (fun z => frameP (binary (W + 1) (encS z))) =
      (List.replicate n z).flatten := by
    rw [List.flatMap_replicate]; simp [hz]
  rw [hr]; simp [List.append_assoc]

end Zero

end NearCubicGates.Close.TabMachine
