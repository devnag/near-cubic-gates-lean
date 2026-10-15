import Proof.PCP.PCPPQuerySupportReusable

/-! Literal entry and paid result-buffer erasure for repeated cached queries.
A row consumer reads exactly arity raw cells before this clearing call. -/
namespace NearCubicWires.RepairOrdinary.PCPPQuerySupportReuse
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entry_literal (source : List Bool) (arity index C : ℕ) :
    entry source arity index C=⟨machine.start,heads,data source arity index C []⟩ := by
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> rfl
  · funext j
    fin_cases j <;> simp [entry,Composition.leftConfig,TapeEmbedding.config,ZeroPadding.config,
      resultCaps,PCPPQuerySupportReset.entry,PCPPQuerySupportReset.caps,Rewind.recording,
      Rewind.config,PCPPQuerySupport.ready,Fin.addCases,data,extra,ZeroPadding.pad]

theorem arity_le_cost {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (i : Fin p.systematicBits) : r.arity ≤ PCPPQuerySupportReset.cost r p i := by
  obtain ⟨raw,hr,rs,_,hh,_,_,_,_,_⟩ := PCPPQuerySupport.lookup_retained_run r p i
  have h := SelectiveReset.prefix_head (prefix_of_run PCPPQuerySupport.machine _ _ raw hr).1 4
  rw [hh,rs] at h
  change r.arity ≤ 0+PCPPQuerySupportReset.cost r p i at h
  simpa only [Nat.zero_add] using h

def resultSlots : Fin 3 → Fin 9 := ![4,7,8]
theorem result_injective : Function.Injective resultSlots := by decide
noncomputable def clearResult := RecoveryFocus.machine resultSlots (RecoveryScratchErase.resetMachine 1)

theorem clear_result_run (source : List Bool) (arity index C : ℕ) (mask : List Bool)
    (hmask : mask.length ≤ C) :
    ∃ r,runFrom clearResult (2*C+4) ⟨clearResult.start,heads,data source arity index C mask⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=data source arity index C [] ∧ r.steps=2*C+4 := by
  have hb : ∀ j : Fin 1,(ZeroPadding.pad C mask).length ≤ C := by
    intro j
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl hmask
  have h := RecoveryScratchErase.erase_ready C (C+1) (fun _ : Fin 1 => ZeroPadding.pad C mask) hb
  obtain ⟨r,hr,rh,rt,rs⟩ := h.focus_at resultSlots result_injective heads
    (data source arity index C mask)
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,rh,rt.trans ?_,rs⟩
  funext j
  have hpick : RecoveryFocus.pick resultSlots j=
      (![none,none,none,none,some 0,none,none,some 1,some 2] : Fin 9 → Option (Fin 3)) j := by
    fin_cases j
    all_goals first
      | exact RecoveryFocus.pick_slot resultSlots result_injective 0
      | exact RecoveryFocus.pick_slot resultSlots result_injective 1
      | exact RecoveryFocus.pick_slot resultSlots result_injective 2
      | decide
  simp only [install,hpick]
  fin_cases j <;> simp [data,Fin.addCases,ZeroPadding.pad]

theorem query_mask_fits {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (i : Fin p.systematicBits) (C : ℕ) (hC : PCPPQuerySupportReset.cost r p i+1 ≤ C) :
    (PCPPQuerySupport.mask r p i).length ≤ C := by
  have h := arity_le_cost r p i
  simp only [PCPPQuerySupport.mask,List.length_ofFn]
  omega

end NearCubicWires.RepairOrdinary.PCPPQuerySupportReuse
