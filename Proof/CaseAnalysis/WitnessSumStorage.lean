import Proof.CaseAnalysis.WitnessSumCleanup

/-! The successful sum reset has the exact next-sum layout. The three
unused alias holes are retained cells throughout; all live parser
scratch is cleared once, while the paid policy and output ports survive. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumStorage
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
open private normal_slot hole_outside core_data_other from Proof.CaseAnalysis.WitnessSumReader
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (H T : ℕ) (arity counts : List Bool) (i : Fin 528) : List Bool :=
  if i=501 then frame arity else if i=502 then List.replicate T true
  else if i=526 then counts else List.replicate H false
def data (P H b core W L T : ℕ) (arity out native counts : List Bool)
    (ambient : Fin 94 → List Bool) : Fin 3061 → List Bool :=
  Fin.addCases (m:=2533) (n:=528) (motive:=fun _=>List Bool)
    (SumDock.coreData P H b core W L (List.replicate H false) out native (List.replicate H false) true ambient)
    (extra H T arity counts)

theorem retained_outside (i : Fin 528) (hi : SumReset.retained i) :
    ∀ j,SumReset.slots j≠SumDock.slots i := by
  intro j
  refine Fin.addCases (m:=524) (n:=2) ?_ ?_ j
  · intro j h
    simp only [SumReset.slots,Fin.addCases_left,SumReset.scratch] at h
    change SumDock.slots (SumReset.privateSlot j)=SumDock.slots i at h
    have he:=SumDock.slots_injective h
    exact SumReset.private_not_retained j (he.symm ▸ hi)
  · intro j
    fin_cases j
    · exact Ne.symm (SumReset.sum_outside i).1
    · exact Ne.symm (SumReset.sum_outside i).2

private theorem core_outside (i : Fin 2533) (h722 : i≠722) (h724 : i≠724) (h2532 : i≠2532)
    (h2530 : i≠2530) (h2531 : i≠2531) : ∀ j,SumReset.slots j≠i.castAdd 528 := by
  intro j
  refine Fin.addCases (m:=524) (n:=2) ?_ ?_ j
  · intro j
    simpa only [SumReset.slots,Fin.addCases_left,SumReset.scratch] using
      SumDock.core_outside i h722 h724 h2532 (SumReset.privateSlot j)
  · intro j h
    fin_cases j
    · exact h2530 (Fin.ext (congrArg Fin.val h).symm)
    · exact h2531 (Fin.ext (congrArg Fin.val h).symm)

private theorem hole_outside_reset (i : Fin 528) (hi : i.val=357 ∨ i.val=368 ∨ i.val=499) :
    ∀ j,SumReset.slots j≠i.natAdd 2533 := by
  intro j
  refine Fin.addCases (m:=524) (n:=2) ?_ ?_ j
  · intro j
    simpa only [SumReset.slots,Fin.addCases_left,SumReset.scratch] using
      hole_outside i hi (SumReset.privateSlot j)
  · intro j h
    have hv:=congrArg Fin.val h
    fin_cases j
    · change 2530=2533+i.val at hv;omega
    · change 2531=2533+i.val at hv;omega

theorem scratch_bounds (P H b core W L K : ℕ) (source out native : List Bool)
    (ambient : Fin 94 → List Bool) (bank : Fin 528 → List Bool)
    (hsource : source.length ≤ H) (hcount : (ZeroPadding.pad H (CompareMachine.word K)).length ≤ H)
    (hbank : ∀ i : Fin 528,i≠501 → i≠502 → i≠526 → (bank i).length ≤ H) :
    ∀ j,(SumWork.data P H b core W L K source out native ambient bank (SumReset.scratch j)).length ≤ H := by
  intro j
  let i:=SumReset.privateSlot j
  have hi:¬SumReset.retained i:=SumReset.private_not_retained j
  by_cases h357:i=357
  · change (SumWork.data P H b core W L K source out native ambient bank (SumDock.slots i)).length ≤ H
    rw [h357]
    exact hsource
  by_cases h368:i=368
  · change (SumWork.data P H b core W L K source out native ambient bank (SumDock.slots i)).length ≤ H
    rw [h368]
    exact hcount
  have h499:i≠499:=by intro h;apply hi;rw [h];exact Or.inl rfl
  change (SumWork.data P H b core W L K source out native ambient bank (SumDock.slots i)).length ≤ H
  rw [normal_slot i h357 h368 h499,SumWork.data,Fin.addCases_right]
  exact hbank i (by intro h;apply hi;rw [h];exact Or.inr (Or.inl rfl))
    (by intro h;apply hi;rw [h];exact Or.inr (Or.inr (Or.inl rfl)))
    (by intro h;apply hi;rw [h];exact Or.inr (Or.inr (Or.inr rfl)))

theorem restored (P H b core W L K T : ℕ) (source arity out native counts : List Bool)
    (ambient : Fin 94 → List Bool) (bank : Fin 528 → List Bool) (final : Fin 3061 → List Bool)
    (h501 : bank 501=frame arity) (h502 : bank 502=List.replicate T true) (h526 : bank 526=counts)
    (holes : ∀ i : Fin 528,(i.val=357 ∨ i.val=368 ∨ i.val=499) → bank i=List.replicate H false)
    (cleared : ∀ j,final (SumReset.scratch j)=List.replicate H false)
    (driver : final 2530=List.replicate H true) (log : final 2531=List.replicate (H+1) false)
    (keep : ∀ i,(∀ j,SumReset.slots j≠i) →
      final i=SumWork.data P H b core W L K source out native ambient bank i) :
    final=data P H b core W L T arity out native counts ambient := by
  funext i
  refine Fin.addCases (m:=2533) (n:=528) ?_ ?_ i
  · intro j
    simp only [data,Fin.addCases_left]
    by_cases h722:j=722
    · subst j;exact cleared 357
    by_cases h2532:j=2532
    · subst j;exact cleared 368
    by_cases h724:j=724
    · subst j;exact keep (SumDock.slots 499) (retained_outside 499 (Or.inl rfl))
    by_cases h2530:j=2530
    · subst j;exact driver
    by_cases h2531:j=2531
    · subst j;exact log
    rw [keep _ (core_outside j h722 h724 h2532 h2530 h2531),SumWork.data,Fin.addCases_left]
    exact core_data_other P H b core W L source (List.replicate H false) out native
      (ZeroPadding.pad H (CompareMachine.word K)) (List.replicate H false) true true ambient j h722 h724 h2532
  · intro j
    simp only [data,Fin.addCases_right]
    by_cases h501j:j=501
    · subst j
      change final (SumDock.slots 501)=_
      rw [keep _ (retained_outside 501 (Or.inr (Or.inl rfl)))]
      exact h501
    by_cases h502j:j=502
    · subst j
      change final (SumDock.slots 502)=_
      rw [keep _ (retained_outside 502 (Or.inr (Or.inr (Or.inl rfl))))]
      exact h502
    by_cases h526j:j=526
    · subst j
      change final (SumDock.slots 526)=_
      rw [keep _ (retained_outside 526 (Or.inr (Or.inr (Or.inr rfl))))]
      exact h526
    simp only [extra,if_neg h501j,if_neg h502j,if_neg h526j]
    by_cases hh:j.val=357 ∨ j.val=368 ∨ j.val=499
    · rw [keep _ (hole_outside_reset j hh),SumWork.data,Fin.addCases_right]
      exact holes j hh
    have h357:j≠357:=by intro h;subst j;exact hh (Or.inl rfl)
    have h368:j≠368:=by intro h;subst j;exact hh (Or.inr (Or.inl rfl))
    have h499:j≠499:=by intro h;subst j;exact hh (Or.inr (Or.inr rfl))
    have hret:¬SumReset.retained j:=by
      rintro (h|h|h|h)
      · exact h499 (Fin.ext h)
      · exact h501j (Fin.ext h)
      · exact h502j (Fin.ext h)
      · exact h526j (Fin.ext h)
    obtain ⟨k,hk⟩:=SumReset.private_covers j hret
    rw [←normal_slot j h357 h368 h499,←hk]
    exact cleared k

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumStorage
