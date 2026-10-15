import Proof.CaseAnalysis.RecoveryClauseFoldPrepare

/-! Literal projections into the existing reverse AND fold. The same paid
clause sentinel is reused, and its unused flag tape is padded false scratch. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseFold
open LocalBitMultitape RepairRepresentation RecoveryRootRound RepairSource.VerifierDecoding
open RecoveryBoundedNativeUnaryPhase (trueBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 35) : Fin 73:=Fin.addCases
  (fun i : Fin 29=>if i=1 then 45 else i.castAdd 44) (![61,62,71,32,34,72] : Fin 6→Fin 73) j
theorem slots_injective : Function.Injective slots:=by decide
def caps (C : ℕ) (j : Fin 35):=if j=29 then C else 0
noncomputable def input (base C total : ℕ) (out pre : List Bool) (refs : List ℕ):=
  ZeroPadding.config (caps C) (RecoveryBoundedNativeFoldLoop.configuration 0 true C false pre refs.reverse
    ⟨base,0,0,out⟩ total 1)
noncomputable def output (base C total : ℕ) (out pre : List Bool) (refs : List ℕ):=
  ZeroPadding.config (caps C) (RecoveryBoundedNativeFoldLoop.configuration 3 true C false pre []
    (RecoveryBoundedNativeFoldLoop.State.iterate true refs.reverse ⟨base,0,0,out⟩) total 1)
noncomputable def reverseMachine:=RecoveryFocus.machine slots (RecoveryBoundedNativeFoldLoop.machine true)

theorem input_heads (base C total : ℕ) (out pre : List Bool) (refs : List ℕ) :
    (input base C total out pre refs).heads=fun j=>Fin.addCases (PCPPNativeClauseBank.heads out)
      (![0,0,(pre++RecoveryBoundedClauseList.stackWord refs).length,0,0,1] : Fin 6→ℕ) j := by
  funext j
  fin_cases j
  all_goals simp only [input,ZeroPadding.config,RecoveryBoundedNativeFoldLoop.configuration,RepeatMachine.cfg,
    controlConfig,TapeEmbedding.config,RecoveryBoundedNativeFoldLoop.State.entry,RecoveryBoundedNativeFold.entry,
    RecoveryBoundedNativeFoldLoop.stack,List.reverse_reverse]
  all_goals rfl
theorem input_data (base C total : ℕ) (out pre : List Bool) (refs : List ℕ) :
    (input base C total out pre refs).tapes=fun j=>ZeroPadding.pad (caps C j)
      (Fin.addCases (RecoveryBoundedNativeFold.oldData 0 base C out)
        (![[false],List.replicate C false,pre++RecoveryBoundedClauseList.stackWord refs,
          List.replicate C false,List.replicate C false,CompareMachine.word total] : Fin 6→List Bool) j) := by
  funext j
  fin_cases j
  all_goals simp only [input,ZeroPadding.config,RecoveryBoundedNativeFoldLoop.configuration,RepeatMachine.cfg,
    controlConfig,TapeEmbedding.config,RecoveryBoundedNativeFoldLoop.State.entry,RecoveryBoundedNativeFold.entry,
    RecoveryBoundedNativeFoldLoop.stack,List.reverse_reverse,List.replicate_zero,List.append_nil]
  all_goals rfl

theorem written_unchanged (A : Fin 73→List Bool) (C : ℕ) (out : List Bool) (i : Fin 71)
    (hi : i≠20) (hw : ∀ j,RecoveryBoundedLiteralReset.workSlots false j≠i) :
    written (cleared A C) out (old i)=A (old i) := by
  have he : old i≠20:=by intro h;exact hi (old_injective h)
  unfold written
  rw [Function.update_of_ne he,cleared_old]
  exact install_other _ _ _ _ hw
theorem written_work (A : Fin 73→List Bool) (C : ℕ) (out : List Bool) (j : Fin 14) :
    written (cleared A C) out (old (RecoveryBoundedLiteralReset.workSlots false j))=List.replicate C false := by
  have hj : old (RecoveryBoundedLiteralReset.workSlots false j)≠20:=by fin_cases j <;> decide
  unfold written
  rw [Function.update_of_ne hj,cleared_old]
  exact install_slot _ (RecoveryBoundedLiteralReset.work_injective false) _ _ j

theorem low_data (H : Fin 73→ℕ) (A : Fin 73→List Bool) (base left right C L : ℕ)
    (out pre source queryRefs result : List Bool)
    (h : RecoveryBoundedClauseState.State (H∘old) (A∘old) base left right C L out pre source queryRefs)
    (j : Fin 29) (h1 : j≠1) (h20 : j≠20) (h25 : j≠25) :
    written (cleared A C) result (j.castAdd 44)=RecoveryBoundedNativeFold.oldData 0 base C result j := by
  have hj : (j.castAdd 42 : Fin 71)≠20:=by intro he;exact h20 (Fin.ext (congrArg (fun k : Fin 71=>k.val) he))
  have hw : ∀ k,RecoveryBoundedLiteralReset.workSlots false k≠(j.castAdd 42 : Fin 71) := by
    intro k he
    have hv:=congrArg (fun i : Fin 71=>i.val) he
    fin_cases k <;> norm_num [RecoveryBoundedLiteralReset.workSlots,RecoveryBoundedLiteralReset.target] at hv <;> omega
  rw [show written (cleared A C) result (j.castAdd 44)=A (j.castAdd 44) from written_unchanged A C result (j.castAdd 42) hj hw]
  have hs : old (RecoveryBoundedClauseState.gate j)=j.castAdd 44 := by
    fin_cases j <;> first | rfl | exact False.elim (h1 rfl) | exact False.elim (h25 rfl)
  have hd : RecoveryBoundedUniversalGates.data left right C out j=RecoveryBoundedNativeFold.oldData 0 base C result j := by
    fin_cases j <;> simp_all [RecoveryBoundedUniversalGates.data,RecoveryBoundedUniversalGates.caps,
      RecoveryBoundedUniversalGates.values,RecoveryBoundedNativeFold.oldData,RecoveryBoundedNativeFold.values,
      PCPPNativeClauseBank.data,ZeroPadding.pad_zero]
  have ha:=h.gateA j
  change A (old (RecoveryBoundedClauseState.gate j))=_ at ha
  rw [hs] at ha
  exact ha.trans hd

theorem prepared_heads (H : Fin 73→ℕ) (A : Fin 73→List Bool) (base left right C L total : ℕ)
    (out pre source queryRefs result stack : List Bool) (refs : List ℕ)
    (h : RecoveryBoundedClauseState.State (H∘old) (A∘old) base left right C L out pre source queryRefs)
    (hS : H 71=(stack++RecoveryBoundedClauseList.stackWord refs).length) (hD : H 72=1) (j : Fin 35) :
    heads H result (slots j)=(input base C total result stack refs).heads j := by
  rw [input_heads]
  fin_cases j
  all_goals first
    | rfl | exact hS | exact hD | exact h.restoreH 0 | exact h.restoreH 1 | exact h.restoreH 2 | exact h.zeroH
    | exact h.scratchH 0 | exact h.scratchH 1
    | exact h.gateH 0 | exact h.gateH 2 | exact h.gateH 3 | exact h.gateH 4 | exact h.gateH 5
    | exact h.gateH 6 | exact h.gateH 7 | exact h.gateH 8 | exact h.gateH 9 | exact h.gateH 10
    | exact h.gateH 11 | exact h.gateH 12 | exact h.gateH 13 | exact h.gateH 14 | exact h.gateH 15
    | exact h.gateH 16 | exact h.gateH 17 | exact h.gateH 18 | exact h.gateH 19 | exact h.gateH 21
    | exact h.gateH 22 | exact h.gateH 23 | exact h.gateH 24 | exact h.gateH 26 | exact h.gateH 27 | exact h.gateH 28

theorem prepared_tapes (H : Fin 73→ℕ) (A : Fin 73→List Bool) (base left right C L total : ℕ)
    (out pre source queryRefs result stack : List Bool) (refs : List ℕ)
    (h : RecoveryBoundedClauseState.State (H∘old) (A∘old) base left right C L out pre source queryRefs)
    (hS : A 71=stack++RecoveryBoundedClauseList.stackWord refs) (hD : A 72=CompareMachine.word total)
    (hC : 1 ≤ C) (j : Fin 35) :
    written (cleared A C) result (slots j)=(input base C total result stack refs).tapes j := by
  rw [input_data]
  refine Fin.addCases (m:=29) (n:=6) ?_ ?_ j
  · intro k
    have hc : caps C (k.castAdd 6)=0 := by
      unfold caps
      have hk : (k.castAdd 6 : Fin 35)≠29 := by intro he;have hv:=congrArg (fun i : Fin 35=>i.val) he;change k.val=29 at hv;omega
      exact if_neg hk
    simp only [slots,Fin.addCases_left,hc,ZeroPadding.pad_zero]
    by_cases h1 : k=1
    · subst k
      exact written_work A C result 13
    · rw [if_neg h1]
      by_cases h20 : k=20
      · subst k;rfl
      · by_cases h25 : k=25
        · subst k
          change written (cleared A C) result 25=RecoveryBoundedNativeFold.oldData 0 base C result 25
          rw [show written (cleared A C) result 25=A 25 from written_unchanged A C result 25 (by decide) (by decide)]
          exact h.restoreA 0
        · exact low_data H A base left right C L out pre source queryRefs result h k h1 h20 h25
  · intro k
    fin_cases k
    · change written (cleared A C) result 61=ZeroPadding.pad C [false]
      rw [RecoveryBoundedSelectorLoop.pad_false C hC]
      exact written_work A C result 0
    · change written (cleared A C) result 62=ZeroPadding.pad 0 (List.replicate C false)
      rw [ZeroPadding.pad_zero]
      exact written_work A C result 1
    · change written (cleared A C) result 71=ZeroPadding.pad 0 (stack++RecoveryBoundedClauseList.stackWord refs)
      rw [ZeroPadding.pad_zero,show written (cleared A C) result 71=cleared A C 71 from Function.update_of_ne (by decide) _ _]
      rw [cleared_other A C 71 (by intro k he;have hv:=congrArg (fun i : Fin 73=>i.val) he;change k.val=71 at hv;omega)]
      exact hS
    · change written (cleared A C) result 32=ZeroPadding.pad 0 (List.replicate C false)
      rw [ZeroPadding.pad_zero,show written (cleared A C) result 32=A 32 from written_unchanged A C result 32 (by decide) (by decide)]
      exact h.restoreA 2
    · change written (cleared A C) result 34=ZeroPadding.pad 0 (List.replicate C false)
      rw [ZeroPadding.pad_zero,show written (cleared A C) result 34=A 34 from written_unchanged A C result 34 (by decide) (by decide)]
      exact h.zeroA
    · change written (cleared A C) result 72=ZeroPadding.pad 0 (CompareMachine.word total)
      rw [ZeroPadding.pad_zero,show written (cleared A C) result 72=cleared A C 72 from Function.update_of_ne (by decide) _ _]
      rw [cleared_other A C 72 (by intro k he;have hv:=congrArg (fun i : Fin 73=>i.val) he;change k.val=72 at hv;omega)]
      exact hD

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseFold
