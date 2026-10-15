import Proof.CaseAnalysis.RecoveryClauseFoldRun

/-! The existing fold returns the same clause bank with a cleared live
operand and its actual final accumulator. All retained sources are exact. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseFold
open LocalBitMultitape RepairRepresentation RecoveryRootRound RepairSource.VerifierDecoding
open RecoveryBoundedNativeUnaryPhase (trueBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def finalState (base : ℕ) (out : List Bool) (refs : List ℕ):=
  RecoveryBoundedNativeFoldLoop.State.iterate true refs.reverse ⟨base,0,0,out⟩
theorem output_heads (base C total : ℕ) (out pre : List Bool) (refs : List ℕ) :
    (output base C total out pre refs).heads=fun j=>Fin.addCases
      (PCPPNativeClauseBank.heads (finalState base out refs).out)
      (![0,0,pre.length,0,0,1] : Fin 6→ℕ) j := by
  funext j
  fin_cases j
  all_goals simp only [output,ZeroPadding.config,RecoveryBoundedNativeFoldLoop.configuration,RepeatMachine.cfg,
    controlConfig,TapeEmbedding.config,RecoveryBoundedNativeFoldLoop.State.entry,RecoveryBoundedNativeFold.entry,
    RecoveryBoundedNativeFoldLoop.stack,RecoveryBoundedNativeUnaryLoop.stackWords,List.reverse_nil,List.flatMap_nil,List.append_nil]
  all_goals rfl
theorem output_data (base C total : ℕ) (out pre : List Bool) (refs : List ℕ) (hC : 1 ≤ C) :
    (output base C total out pre refs).tapes=fun j=>Fin.addCases
      (RecoveryBoundedNativeFold.oldData 0 (finalState base out refs).acc C (finalState base out refs).out)
      (![List.replicate C false,List.replicate C false,
        pre++List.replicate (finalState base out refs).erased false,List.replicate C false,List.replicate C false,
        CompareMachine.word total] : Fin 6→List Bool) j := by
  funext j
  fin_cases j
  all_goals simp only [output,ZeroPadding.config,RecoveryBoundedNativeFoldLoop.configuration,RepeatMachine.cfg,
    controlConfig,TapeEmbedding.config,RecoveryBoundedNativeFoldLoop.State.entry,RecoveryBoundedNativeFold.entry,
    RecoveryBoundedNativeFoldLoop.stack,RecoveryBoundedNativeUnaryLoop.stackWords,List.reverse_nil,List.flatMap_nil,List.append_nil]
  all_goals first | rfl | exact ZeroPadding.pad_zero _ | exact RecoveryBoundedSelectorLoop.pad_false C hC

theorem fold_state (H RH : Fin 73→ℕ) (A RA : Fin 73→List Bool) (base left right C L total : ℕ)
    (out pre source queryRefs stack : List Bool) (refs : List ℕ)
    (h : RecoveryBoundedClauseState.State (H∘old) (A∘old) base left right C L out pre source queryRefs)
    (hH : ∀ j,RH (slots j)=(output base C total (out++trueBits) stack refs).heads j)
    (hA : ∀ j,RA (slots j)=(output base C total (out++trueBits) stack refs).tapes j)
    (hKeep : ∀ i,(∀ j,slots j≠i) → RH i=heads H (out++trueBits) i ∧ RA i=written (cleared A C) (out++trueBits) i)
    (hC : 1 ≤ C) :
    let f:=finalState base (out++trueBits) refs
    RecoveryBoundedClauseState.State (RH∘old) (RA∘old) f.acc 0 right C L f.out pre source queryRefs := by
  rw [output_heads] at hH
  rw [output_data base C total (out++trueBits) stack refs hC] at hA
  let f:=finalState base (out++trueBits) refs
  have keepH (i : Fin 73) (hi : ∀ j,slots j≠i) : RH i=H i := by
    rw [(hKeep i hi).1]
    have he : i≠20:=fun he=>hi 20 he.symm
    exact Function.update_of_ne he _ _
  have keepA (i : Fin 71) (hi : ∀ j,slots j≠old i)
      (hw : ∀ j,RecoveryBoundedLiteralReset.workSlots false j≠i) : RA (old i)=A (old i) := by
    rw [(hKeep (old i) hi).2]
    have he : i≠20:=by intro he;subst i;exact hi 20 rfl
    exact written_unchanged A C (out++trueBits) i he hw
  have resetA (j : Fin 14) : RA (old (RecoveryBoundedLiteralReset.workSlots false j))=List.replicate C false := by
    fin_cases j
    all_goals first
      | exact hA 29 | exact hA 30 | exact hA 1
      | (rw [(hKeep _ (by decide)).2];exact written_work A C (out++trueBits) _)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    by_cases h25 : j=25
    · subst j
      change RH 47=0
      rw [keepH 47 (by decide)]
      exact h.gateH 25
    · have he : old (RecoveryBoundedClauseState.gate j)=slots (j.castAdd 6) := by
        fin_cases j <;> first | rfl | exact False.elim (h25 rfl)
      change RH (old (RecoveryBoundedClauseState.gate j))=_
      rw [he,hH (j.castAdd 6)]
      simp only [Fin.addCases_left]
  · intro j
    by_cases h25 : j=25
    · subst j
      change RA 47=ZeroPadding.pad C (List.replicate right true)
      rw [show RA 47=A 47 from keepA 47 (by decide) (by decide)]
      exact h.gateA 25
    · have he : old (RecoveryBoundedClauseState.gate j)=slots (j.castAdd 6) := by
        fin_cases j <;> first | rfl | exact False.elim (h25 rfl)
      change RA (old (RecoveryBoundedClauseState.gate j))=_
      rw [he,hA (j.castAdd 6)]
      simp only [Fin.addCases_left]
      fin_cases j <;> simp_all [RecoveryBoundedNativeFold.oldData,RecoveryBoundedNativeFold.values,
        RecoveryBoundedUniversalGates.data,RecoveryBoundedUniversalGates.caps,RecoveryBoundedUniversalGates.values,
        PCPPNativeClauseBank.data,ZeroPadding.pad_zero]
  · intro j
    fin_cases j <;> first | exact hH 25 | exact hH 1 | exact hH 32 | exact hH 22 | exact hH 23
  · intro j
    fin_cases j <;> first | exact hA 25 | exact hA 1 | exact hA 32 | exact hA 22 | exact hA 23
  · exact hH 33
  · exact hA 33
  · intro j
    fin_cases j
    all_goals first
      | exact hH 29 | exact hH 30
      | exact (keepH 63 (by decide)).trans (h.scratchH 2)
      | exact (keepH 64 (by decide)).trans (h.scratchH 3)
      | exact (keepH 65 (by decide)).trans (h.scratchH 4)
      | exact (keepH 66 (by decide)).trans (h.scratchH 5)
      | exact (keepH 48 (by decide)).trans (h.scratchH 6)
      | exact (keepH 67 (by decide)).trans (h.scratchH 7)
      | exact (keepH 68 (by decide)).trans (h.scratchH 8)
      | exact (keepH 49 (by decide)).trans (h.scratchH 9)
      | exact (keepH 69 (by decide)).trans (h.scratchH 10)
      | exact (keepH 37 (by decide)).trans (h.scratchH 11)
      | exact (keepH 30 (by decide)).trans (h.scratchH 12)
  · intro j
    have he : RA (old (RecoveryBoundedClauseState.scratch j))=List.replicate C false := by
      fin_cases j <;> first
        | exact resetA 0 | exact resetA 1 | exact resetA 2 | exact resetA 3 | exact resetA 4
        | exact resetA 5 | exact resetA 6 | exact resetA 7 | exact resetA 8 | exact resetA 9
        | exact resetA 10 | exact resetA 11 | exact resetA 12
    change (RA (old (RecoveryBoundedClauseState.scratch j))).length ≤ C
    rw [he,List.length_replicate]
  · change RH 59=0
    rw [keepH 59 (by decide)]
    exact h.refsH
  · change RA 59=queryRefs
    rw [show RA 59=A 59 from keepA 59 (by decide) (by decide)]
    exact h.refsA
  · change RH 43=0
    rw [keepH 43 (by decide)]
    exact h.logH
  · change RA 43=List.replicate L false
    rw [show RA 43=A 43 from keepA 43 (by decide) (by decide)]
    exact h.logA
  · change RH 70=pre.length
    rw [keepH 70 (by decide)]
    exact h.sourceH
  · change RA 70=source
    rw [show RA 70=A 70 from keepA 70 (by decide) (by decide)]
    exact h.sourceA

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseFold
