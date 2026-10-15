import Proof.CaseAnalysis.WitnessMassCompareFields

/-! The actual mass decision retains an exact bounded accumulator store,
so the checked reset can serve the next sum using the same native bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassStoredDecision
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorSumFold CompetitorThresholdAmbient
open CompetitorReusableDecision CompetitorRationalDecision
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem decision_run (B : ℕ) (q : ℚ) (a : Estimate) (source : List Bool)
    (ambient : Fin 110→List Bool) (h : Store B a source (project ambient))
    (hn : ambient 96=frame (binary (width B) (CompetitorThresholdDecision.numerator q)))
    (hz : ambient 101=frame (binary (width B) 0)) (hd : ambient 106=frame (binary B q.den))
    (ha : a.Valid B) (hq : 0≤q)
    (hp : CompetitorThresholdDecision.numerator q<2^B) (hden : q.den<2^B) : ∃ output,
    ClockJoin.ReadyRun (CompetitorThresholdAmbient.decisionProgram false) (2000*(B+1)^2)
      (cleaned B ambient) output ∧ Store B a source (project output) ∧
      (readTapeBit (output 65) 0=true ↔ a.value≤q):=by
  obtain ⟨out,hr,hbound,hshared,hflag⟩:=MassCompareFields.fields_run B a q ha hq hp hden
  have hf:=hr.focus (CompetitorThresholdAmbient.decisionSlots false) (decision_injective false)
    (cleaned B ambient) (CompetitorThresholdAmbient.decision_input false B q a source ambient h hn hz hd)
  let final:=install (CompetitorThresholdAmbient.decisionSlots false) (cleaned B ambient) out
  have get (j : Fin 67) : final (CompetitorThresholdAmbient.decisionSlots false j)=out j:=
    install_slot _ (decision_injective false) _ _ _
  have keep (i : Fin 94)
      (hi : ∀ j,CompetitorThresholdAmbient.decisionSlots false j≠native i)
      (hw : ∀ j,workSlot j≠i) : final (native i)=ambient (native i):=by
    rw [show final=install _ _ _ by rfl,install_other _ _ _ _ hi,cleaned_native]
    exact clear_keep _ _ _ i hw
  refine ⟨final,hf,?_,?_⟩
  · constructor
    · exact (get 2).trans (hshared 2)
    · exact (get 3).trans (hshared 3)
    · exact (get 5).trans (hshared 5)
    · have hh:=hshared 6
      change out 6=ZeroPadding.pad 0 (List.replicate (width B) true) at hh
      exact (get 6).trans (hh.trans (ZeroPadding.pad_zero _))
    · exact (keep 84 (by decide) (fun j=>(work_range j).2.2.2.2.2)).trans h.shortWidth
    · exact (keep 88 (by decide) (fun j=>work_outside j 88 (by decide))).trans h.source
    · exact (keep 89 (by decide) (fun j=>work_outside j 89 (by decide))).trans h.loaderReset
    · exact (keep 90 (by decide) (fun j=>work_outside j 90 (by decide))).trans h.eraseDriver
    · exact (keep 91 (by decide) (fun j=>work_outside j 91 (by decide))).trans h.eraseReset
    · exact (keep 92 (by decide) (fun j=>work_outside j 92 (by decide))).trans h.copyCounter
    · exact (keep 93 (by decide) (fun j=>work_outside j 93 (by decide))).trans h.copyReset
    · intro i
      by_cases hj:∃ j,CompetitorThresholdAmbient.decisionSlots false j=native (i.castAdd 6)
      · obtain ⟨j,hj⟩:=hj
        change (final (native (i.castAdd 6))).length ≤ _
        rw [←hj,get]
        exact hbound j
      · change (final (native (i.castAdd 6))).length ≤ _
        rw [show final=install _ _ _ by rfl,install_other _ _ _ _ (fun j he=>hj ⟨j,he⟩),cleaned_native]
        simp only [cleared]
        split
        · simp only [List.length_replicate,le_refl]
        · exact h.support i
  · change readTapeBit (final (CompetitorThresholdAmbient.decisionSlots false 65)) 0=true ↔ _
    rw [get]
    exact hflag

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassStoredDecision
