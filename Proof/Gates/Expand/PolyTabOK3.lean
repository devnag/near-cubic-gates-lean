import Proof.Gates.Expand.PolyTabOK2

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

variable (E : ExpandMachine)

theorem monoCap_le (r : TabReq) (j i : ℕ) (hj : j < (hsK E r).length) (hi : i < (tsK E r).length) :
    monoCap E r (j, i) ≤ capk E r := by
  have := le_sum_map (idx2 E r) (monoCap E r) _ (mem_idx2 E r j i hj hi)
  unfold capk; omega

theorem stepCap_le (r : TabReq) (j i i' : ℕ) (hj : j < (hsK E r).length) (hi : i < (tsK E r).length)
    (hi' : i' < (osAt E r i).length) : stepCap E r (j, i, i') ≤ capk E r := by
  have := le_sum_map (idx3 E r) (stepCap E r) _ (mem_idx3 E r j i i' hj hi hi')
  unfold capk; omega

theorem BBk_le (r : TabReq) : BBk E r ≤ capk E r := by unfold capk; omega

theorem hs_lt (r : TabReq) (j : ℕ) (hj : j < (hsK E r).length) : (hsK E r)[j] < 2 ^ r.k := by
  have hm := List.getElem_mem hj
  simp only [hsK, hList, List.mem_filter, List.mem_range] at hm
  exact hm.1

theorem two_pow_k_le (r : TabReq) : 2 ^ r.k ≤ 2 ^ (Wk E r + 1) :=
  Nat.pow_le_pow_right (by norm_num) (by have := Wk_ge E r; omega)

/-- **The side conditions of `cutM_spec` hold at every point.** -/
theorem pointOK_all (r : TabReq) (j : ℕ) :
    PointOK (capk E r) (Wk E r) r.s r.k (Wdk E r) (CSk E r) (BBk E r) (CMk E r) (hsK E r) (tsK E r) [] 0 j := by
  intro hj
  have hc : (hsK E r)[j] < 2 ^ r.k := hs_lt E r j hj
  have ec : cAt E r j = (hsK E r)[j] := List.getD_eq_getElem _ _ hj
  refine ⟨lt_of_lt_of_le hc (two_pow_k_le E r), fun i hi => ?_, fun i hi => ?_⟩
  · -- MonoOK
    have eos : osAt E r i = (tsK E r)[i].1 := by unfold osAt; rw [List.getD_eq_getElem _ _ hi]
    have hti : (tsK E r)[i] ∈ (code (tabT E r)).terms := List.getElem_mem hi
    have hmc := monoCap_le E r j i hj hi
    obtain ⟨hp, hxp⟩ := code_count (tsK E r) i hi
    have egd : (xsK E r).getD (termStart (tsK E r) i) 0 = (tsK E r)[i].1.length := by
      unfold xsK; rw [List.getD_eq_getElem _ _ hp]; exact hxp hp
    simp only [monoCap, ec, eos, outAt, gAt] at hmc
    rw [egd] at hmc
    have hlenD := terms_length E r _ hti
    refine ⟨hp, hxp hp, ?_, ?_, fun o ho => ?_, fun i' hi' => ?_, fun i' hi' => ?_, by omega,
      mono_bound E r _ hc _ hti, ?_, BBk_le E r, by omega, by omega⟩
    · have : Dm r < 2 ^ (Wk E r + 1) :=
        lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by
          have := Wk_ge0 E r; have : Dm r ≤ Dm r * (r.s + 1) := Nat.le_mul_of_pos_right _ (by omega); omega))
      omega
    · rw [hxp hp]; unfold xsK at hmc; omega
    · obtain ⟨v, rfl⟩ := mem_terms_occ E r _ hti o ho; exact occ_outW_length E r v
    · -- StepOK
      have hi'' : i' < (osAt E r i).length := by rw [eos]; exact hi'
      have hsc := stepCap_le E r j i i' hj hi hi''
      have eo : oAt E r i i' = (tsK E r)[i].1[i'] := by unfold oAt; rw [List.getD_eq_getElem _ _ hi'', ] ; simp [eos]
      have etf : tfAt E r j i i' = tupF (hsK E r)[j] ((tsK E r)[i].1.take i') := by unfold tfAt; rw [ec, eos]
      simp only [stepCap, ec, eo, etf] at hsc
      obtain ⟨v, hv⟩ := mem_terms_occ E r _ hti _ (List.getElem_mem hi')
      have hW1 : (CB r) < 2 ^ Wk E r := CB_lt_Wk E r
      refine ⟨blk_at (tsK E r) i hi i' hi', by rw [hv]; exact occ_inW_length E r v,
        by rw [hv]; exact occ_outW_length E r v, lt_of_lt_of_le hc (two_pow_k_le E r), by rw [hv]; exact occ_bound E r v,
        by rw [hv]; exact occ_hB E r v, by rw [hv]; exact occ_ht E r v _,
        fun kid hk y hy => lt_of_le_of_lt (by rw [hv] at hk; exact occ_fit E r v _ hc kid hk y hy) hW1,
        by unfold xsK at hsc; omega, by omega, by omega, by omega, ⟨by omega, by omega, by simp at hsc ⊢; omega, by omega⟩,
        by omega, by omega⟩
    · -- the step cost
      have hi'' : i' < (osAt E r i).length := by rw [eos]; exact hi'
      have := le_foldr_max _ _ (List.mem_map_of_mem (f := stepCost E r) (mem_idx3 E r j i i' hj hi hi''))
      have eo : oAt E r i i' = (tsK E r)[i].1[i'] := by unfold oAt; rw [List.getD_eq_getElem _ _ hi'']; simp [eos]
      simpa [stepCost, ec, eo, pAt, tfAt, eos, xsK, CSk] using this
    · have := le_foldr_max _ _ (List.mem_map_of_mem (f := bbAt E r) (mem_idx2 E r j i hj hi))
      simpa [bbAt, ec, eos, BBk] using this
  · -- the monomial cost
    have eos : osAt E r i = (tsK E r)[i].1 := by unfold osAt; rw [List.getD_eq_getElem _ _ hi]
    have := le_foldr_max _ _ (List.mem_map_of_mem (f := monoCost E r) (mem_idx2 E r j i hj hi))
    simpa [monoCost, ec, eos, CMk] using this

end NearCubicGates.Close.Expand.PolyTab
