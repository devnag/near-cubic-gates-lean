import Proof.PCP.PCPPQueryClauseReusable

/-! Literal entry and paid result-buffer erasure for repeated cached queries.
The row consumer decodes the native pair and restores its result head before clearing. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseReuse
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
      PCPPQueryClauseReset.entry,PCPPQueryClauseReset.caps,Rewind.recording,
      Rewind.config,PCPPQueryClause.entry,PCPPQueryClauseHeader.entry,PCPPQueryClauseHeader.tapes,Fin.addCases,data,extra,ZeroPadding.pad]

def resultSlots : Fin 3 → Fin 19 := ![15,17,18]
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
      (![none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,some 0,none,some 1,some 2] : Fin 19 → Option (Fin 3)) j := by
    fin_cases j
    all_goals first
      | exact RecoveryFocus.pick_slot resultSlots result_injective 0
      | exact RecoveryFocus.pick_slot resultSlots result_injective 1
      | exact RecoveryFocus.pick_slot resultSlots result_injective 2
      | decide
  simp only [install,hpick]
  fin_cases j <;> simp [data,Fin.addCases,ZeroPadding.pad]

theorem query_pair_fits {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (i : Fin (2^p.clauseBits)) (C : ℕ) (hC : PCPPQueryClause.queryBudget r p i+1 ≤ C) :
    (natListWord [literalIndex (p.clauses i).left,literalIndex (p.clauses i).right]).length ≤ C := by
  obtain ⟨raw,hr,hs,hout,hsource,harity,hh13,hindex,hh14⟩ :=
    PCPPQueryClause.lookup_retained_run r p i
  have hz := PCPPQueryClauseReset.initial_work (pcppOutput r p) r.arity i.val 15 (Or.inr rfl)
  have h := PCPSerializerReuse.tape_support PCPPQueryClause.machine _ _ raw hr 15 0 0
    (by rw [hz.1]) (by rw [hz.2]; simp)
  rw [hout] at h
  simp only [Nat.zero_add,max_eq_right (Nat.zero_le _)] at h
  omega

end NearCubicWires.RepairOrdinary.PCPPQueryClauseReuse
