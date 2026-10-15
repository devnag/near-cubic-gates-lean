import Proof.CaseAnalysis.WitnessMassStep

/-! Reinitialize the existing mass accumulator between sums, retaining the
same paid width words and clearing driver. No policy is recomputed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassReset
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorSumFold CompetitorReusableDecision CompetitorRationalDecision
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cold_avoids (j : Fin 89) (i : Fin 94) (hi : i=6 ∨ i=84 ∨ i=88) : coldSlot j≠i:=by
  simpa only [extend,Fin.addCases_left] using cold_not_retained ((j.castAdd 1).castAdd 1) i hi

theorem clear_store (B : ℕ) (a : Estimate) (source : List Bool) (ambient : Fin 94→List Bool)
    (h : Store B a source ambient) :
    ClockJoin.ReadyRun coldClearProgram (2*capacity B+4) ambient (zeroed B source):=by
  obtain ⟨r,hr,rh,rt,rs⟩:=clear_run coldSlot cold_injective
    (fun j=>cold_avoids j 88 (Or.inr (Or.inr rfl)))
    (fun j=>(cold_not_driver j).1) (fun j=>(cold_not_driver j).2)
    (capacity B) 0 ambient h.eraseDriver h.eraseReset (by
      intro j
      by_cases hj:(coldSlot j).val<88
      · exact h.support ⟨(coldSlot j).val,hj⟩
      have he:coldSlot j=89 ∨ coldSlot j=92 ∨ coldSlot j=93:=by
        simp only [coldSlot,Fin.ext_iff] at hj ⊢
        split_ifs at hj ⊢ <;> (try simp only at hj ⊢) <;>
          first | trivial | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | omega
      rcases he with he | he | he
      · rw [he,h.loaderReset,List.length_replicate]
      · rw [he,h.copyCounter,List.length_replicate]
      · rw [he,h.copyReset,List.length_replicate])
  have hi:cfg (clearProgram coldSlot).start 0 ambient=initialConfiguration (clearProgram coldSlot) ambient:=by
    apply configuration_ext
    · rfl
    · funext i;simp only [cfg,heads,initialConfiguration,ite_self]
    · rfl
  rw [hi] at hr
  refine ⟨r,hr,rt.trans ?_,?_,rs.le⟩
  · funext i
    by_cases h6:i=6
    · subst i
      exact (clear_keep _ _ _ 6 (fun j=>cold_avoids j 6 (Or.inl rfl))).trans h.wideWidth
    by_cases h84:i=84
    · subst i
      exact (clear_keep _ _ _ 84 (fun j=>cold_avoids j 84 (Or.inr (Or.inl rfl)))).trans h.shortWidth
    by_cases h88:i=88
    · subst i
      exact (clear_keep _ _ _ 88 (fun j=>cold_avoids j 88 (Or.inr (Or.inr rfl)))).trans h.source
    by_cases h90:i=90
    · subst i
      exact (clear_keep _ _ _ 90 (fun j=>(cold_not_driver j).1)).trans h.eraseDriver
    by_cases h91:i=91
    · subst i
      exact (clear_keep _ _ _ 91 (fun j=>(cold_not_driver j).2)).trans h.eraseReset
    have hz:zeroed B source i=List.replicate (capacity B) false:=by
      simp only [zeroed,show i.val≠6 from fun e=>h6 (Fin.ext e),
        show i.val≠84 from fun e=>h84 (Fin.ext e),show i.val≠88 from fun e=>h88 (Fin.ext e),
        show i.val≠90 from fun e=>h90 (Fin.ext e),show i.val≠91 from fun e=>h91 (Fin.ext e),if_false]
    rw [hz]
    obtain ⟨j,hj⟩:=cold_image i h6 h84 h88
    rw [extend_cases] at hj
    split_ifs at hj
    · exact clear_cell _ _ _ i ⟨_,hj⟩
    · exact False.elim (h90 hj.symm)
    · exact False.elim (h91 hj.symm)
  · intro i;rw [rh];simp only [heads,ite_self]

theorem reset_run (B : ℕ) (a : Estimate) (source : List Bool) (ambient : Fin 94→List Bool)
    (h : Store B a source ambient) (hB : 1≤B) : ∃ output,
    ClockJoin.ReadyRun bootstrapProgram (bootstrapBudget B) ambient output ∧
      Store B CompetitorSumWidth.zero source output:=by
  obtain ⟨out,hr,hbound,h0,h1,h4,h6,h84⟩:=padded_constants_run B hB
  have hin:∀ j,zeroed B source (nativeSlots j)=constantInput B j:=by
    intro j;fin_cases j <;> first | rfl | exact (ZeroPadding.pad_zero _).symm
  have hf:=hr.focus nativeSlots native_injective (zeroed B source) hin
  have hall:=ClockJoin.join coldClearProgram constantsProgram _ _ _ _ _ (clear_store B a source ambient h) hf
  have hc:(2*capacity B+4)+1+(20*B+53)=bootstrapBudget B:=by unfold bootstrapBudget;omega
  rw [hc] at hall
  refine ⟨_,hall,?_⟩
  constructor
  · exact (install_slot nativeSlots native_injective _ out 0).trans h0
  · exact (install_slot nativeSlots native_injective _ out 1).trans h1
  · exact (install_slot nativeSlots native_injective _ out 4).trans h4
  · exact (install_slot nativeSlots native_injective _ out 6).trans h6
  · exact (install_slot nativeSlots native_injective _ out 84).trans h84
  · exact install_other nativeSlots _ _ 88 (fun j=>native_outside j 88 (by decide))
  · exact install_other nativeSlots _ _ 89 (fun j=>native_outside j 89 (by decide))
  · exact install_other nativeSlots _ _ 90 (fun j=>native_outside j 90 (by decide))
  · exact install_other nativeSlots _ _ 91 (fun j=>native_outside j 91 (by decide))
  · exact install_other nativeSlots _ _ 92 (fun j=>native_outside j 92 (by decide))
  · exact install_other nativeSlots _ _ 93 (fun j=>native_outside j 93 (by decide))
  · intro i
    rw [show i.castAdd 6=nativeSlots i by rfl,install_slot nativeSlots native_injective]
    exact hbound i

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassReset
