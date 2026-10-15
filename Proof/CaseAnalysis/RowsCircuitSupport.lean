import Proof.CaseAnalysis.RowsCircuitBodySupport

/-! Bound the original cold allocation and prefix by their own executed
banks. The C-sized sweeps never require their runtime to be at most C. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem install_support {t u : ℕ} (slots : Fin t → Fin u) (inj : Function.Injective slots)
    (P : Fin u → Prop) (C : ℕ) (A : Fin u → List Bool) (B : Fin t → List Bool)
    (ha : ∀ i,P i → (A i).length ≤ C) (hb : ∀ j,(B j).length ≤ C) :
    ∀ i,P i → (install slots A B i).length ≤ C:=by
  intro i hi
  by_cases hit:∃ j,slots j=i
  · obtain ⟨j,rfl⟩:=hit
    rw [install_slot slots inj];exact hb j
  · rw [install_other _ _ _ _ (by simpa only [not_exists] using hit)]
    exact ha i hi

theorem cleared_support (t C : ℕ) (i : Fin (t+1+1)) :
    (PCPTraversal.clearedLocal t C 0 i).length ≤ C+1:=by
  refine Fin.addCases (m:=t+1) (n:=1) ?_ ?_ i
  · intro j
    simp only [PCPTraversal.clearedLocal,Fin.addCases_left]
    refine Fin.addCases (m:=t) (n:=1) ?_ ?_ j
    · intro k;simp
    · intro k;simp
  · intro j
    simp [PCPTraversal.clearedLocal]

theorem cold_support (C core W L : ℕ) (bits out : List Bool) (bank : Fin 639 → List Bool)
    (hin : 2*bits.length+1 ≤ C) (hb : ∀ i,(bank i).length ≤ C) :
    ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 →
      (output C core W L bits out bank i).length ≤ C+1:=by
  let P:=fun i : Fin 1703=>i≠1 ∧ i≠1674 ∧ i≠1694 ∧ i≠1698 ∧ i≠1699 ∧ i≠1688
  have initial:∀ i,P i → (input C core W L bits out i).length ≤ C+1:=by
    intro i ⟨hr,hc,hd,hw,hl,ho⟩
    simp only [input,if_neg ho,CloseoutRowsCircuit.input,
      if_neg (show i.val≠1 from fun h=>hr (Fin.ext h)),
      if_neg (show i.val≠1674 from fun h=>hc (Fin.ext h)),
      if_neg (show i.val≠1694 from fun h=>hd (Fin.ext h)),
      if_neg (show i.val≠1698 from fun h=>hw (Fin.ext h)),
      if_neg (show i.val≠1699 from fun h=>hl (Fin.ext h)),List.length_nil]
    exact Nat.zero_le _
  have al:∀ i,P i → (allocated C core W L bits out i).length ≤ C+1:=
    install_support CloseoutRowsCircuitAllocate.slots CloseoutRowsCircuitAllocate.slots_injective P (C+1)
      _ _ initial (cleared_support 1054 C)
  have se:∀ i,P i → (seeded C core W L bits out i).length ≤ C+1:=by
    apply install_support seedSlots (by decide) P (C+1) _ _ al
    intro i;fin_cases i <;> simp [seedOutput,ZeroPadding.pad_length]
  have fr:∀ i,P i → (framed C core W L bits out bank i).length ≤ C+1:=
    install_support prefixSlots prefix_injective P (C+1) _ _ se (fun i=>(hb i).trans (Nat.le_succ C))
  intro i hr hc hd hw hl ho
  by_cases ht:i=640
  · subst i
    rw [output,Function.update_self,ZeroPadding.pad_length,frame_length]
    have width:(CloseoutRowsCircuitHeader.codeWord bits 3).length=bits.length:=
      (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits _)
    rw [width];omega
  · rw [output,Function.update_of_ne ht]
    exact fr i ⟨hr,hc,hd,hw,hl,ho⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
