import Proof.CaseAnalysis.RecoveryProjectionCounters

/-! Four real input words produce the original 37-tape row bank and every
retained raw/sentinel dimension consumed by its enclosing recovery loop. -/
namespace NearCubicWires.RepairOrdinary.RecoveryProjectionCold
open LocalBitMultitape RepairSource RecoveryRootRound SourceInterfaces
open VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def allocated := Composition.machine scalarMachine bankMachine
noncomputable def counted := Composition.machine allocated countMachine
noncomputable def withR := Composition.machine counted rawRMachine
noncomputable def machine := Composition.machine withR rawQMachine
def budget (R Q B : ℕ) := scalarBudget R Q+1+bankBudget R B+1+Counter.budget (2^R)+1+(2*R+6)+1+(2*Q+6)

private theorem bank_ne_high (i : Fin 37) (j : Fin 113) (hj : (37 : ℕ)≤(j : Fin 113).val) :
    bankSlots i≠j := by
  intro h;have hv:=congrArg (fun i : Fin 113=>i.val) h
  change i.val=j.val at hv
  have hi:=i.isLt;omega

theorem ready (R Q B : ℕ) (queries : List Bool) : ∃ O,
    ClockJoin.ReadyRun machine (budget R Q B) (input R Q B queries) O ∧
      (∀ i,O (bankSlots i)=readyBank R Q B queries i) ∧
      O 103=List.replicate (2^R) true ∧ O 106=CompareMachine.word (2^R) ∧
      O 109=List.replicate R true ∧ O 111=List.replicate Q true ∧ O 104=List.replicate B true := by
  obtain ⟨A,ha,habank,ha103,hahigh⟩ := scalar_ready R Q B queries
  obtain ⟨M,hm,hmbank,hm104,hmkeep⟩ := bank_ready R Q B queries A habank
    (by simpa using hahigh 104 (by decide)) (by simpa using hahigh 105 (by decide))
  have mfresh (i : Fin 113) (hi : (106 : ℕ)≤(i : Fin 113).val) : M i=[] := by
    have h104 : i≠104 := by intro h;subst i;norm_num at hi
    have h105 : i≠105 := by intro h;subst i;norm_num at hi
    rw [hmkeep i (by omega) h104 h105,hahigh i (by omega)]
    simp only [h104,ite_false]
  obtain ⟨N,hn,hn106,hnkeep⟩ := count_ready (2^R) M
    ((hmkeep 103 (by decide) (by decide) (by decide)).trans ha103)
    (mfresh 106 (by decide)) (mfresh 107 (by decide)) (mfresh 108 (by decide))
  have nbank (i : Fin 37) : N (bankSlots i)=readyBank R Q B queries i :=
    (hnkeep _ (bank_ne_high i 106 (by decide)) (bank_ne_high i 107 (by decide))
      (bank_ne_high i 108 (by decide))).trans (hmbank i)
  have nfresh (i : Fin 113) (hi : (109 : ℕ)≤(i : Fin 113).val) : N i=[] := by
    have h106 : i≠106 := by intro h;subst i;norm_num at hi
    have h107 : i≠107 := by intro h;subst i;norm_num at hi
    have h108 : i≠108 := by intro h;subst i;norm_num at hi
    exact (hnkeep i h106 h107 h108).trans (mfresh i (by omega))
  have hr:=rawR_ready R N (nbank 34) (nfresh 109 (by decide)) (nfresh 110 (by decide))
  have n35 : N 35=CompareMachine.word Q := nbank 35
  have hq:=rawQ_ready Q (outputR N R)
    (by simpa [outputR] using n35)
    (by simpa [outputR] using nfresh 111 (by decide))
    (by simpa [outputR] using nfresh 112 (by decide))
  have halloc:=ClockJoin.join scalarMachine bankMachine _ _ _ _ _ ha hm
  have hcount:=ClockJoin.join allocated countMachine _ _ _ _ _ halloc hn
  have hrawR:=ClockJoin.join counted rawRMachine _ _ _ _ _ hcount hr
  have whole:=ClockJoin.join withR rawQMachine _ _ _ _ _ hrawR hq
  refine ⟨outputQ (outputR N R) Q,whole,?_,?_,?_,?_,?_,?_⟩
  · intro i
    simp only [outputQ,outputR,Function.update_of_ne (bank_ne_high i 109 (by decide)),
      Function.update_of_ne (bank_ne_high i 110 (by decide)),
      Function.update_of_ne (bank_ne_high i 111 (by decide)),
      Function.update_of_ne (bank_ne_high i 112 (by decide))]
    exact nbank i
  · simpa [outputQ,outputR] using (hnkeep 103 (by decide) (by decide) (by decide)).trans
      ((hmkeep 103 (by decide) (by decide) (by decide)).trans ha103)
  · simpa [outputQ,outputR] using hn106
  · simp [outputQ,outputR]
  · simp [outputQ]
  · simpa [outputQ,outputR] using (hnkeep 104 (by decide) (by decide) (by decide)).trans hm104

theorem original_ready (p : RawProjectionPCP) (R Q B : ℕ) : ∃ O,
    ClockJoin.ReadyRun machine (budget R Q B)
      (input R Q B (QueryBytes.framedCodes (normalizedRows p R Q).flatten)) O ∧
      (∀ i,O (bankSlots i)=RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) B i) ∧
      O 103=List.replicate (2^R) true ∧ O 106=CompareMachine.word (2^R) ∧
      O 109=List.replicate R true ∧ O 111=List.replicate Q true ∧ O 104=List.replicate B true := by
  obtain ⟨O,hr,hbank,hrest⟩ := ready R Q B (QueryBytes.framedCodes (normalizedRows p R Q).flatten)
  exact ⟨O,hr,by simpa only [readyBank_original] using hbank,hrest⟩

end NearCubicWires.RepairOrdinary.RecoveryProjectionCold
