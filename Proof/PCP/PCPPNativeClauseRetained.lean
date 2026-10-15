import Proof.PCP.PCPPNativeClauseReuseLayout

/-! Copy the actual decoded reference out of the padded field workspace.
Its original source and all capacity drivers are preserved for the sweep. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseReusable
open LocalBitMultitape RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev retained (i : Fin 23) : Prop :=
  i=4 ∨ i=5 ∨ i=6 ∨ i=13 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22
def reference (index stride : ℕ) (sign : Bool) (p n : ℕ) :=
  index*stride+PCPPNativeClauseReference.offset sign p n
def prefixBudget (bits : List Bool) (index stride : ℕ) (sign : Bool) (p n : ℕ) :=
  PCPPNativeClauseField.budget bits index sign stride p n+1+2*reference index stride sign p n+4

theorem outside_field (i : Fin 23) (hi : 19 ≤ i.val) : ∀ j,fieldSlots j≠i := by
  intro j h
  have hval := congrArg (fun k : Fin 23=>k.val) h
  change j.val=i.val at hval
  omega

theorem prefix_run (pre bits tail : List Bool) (index : ℕ) (sign : Bool)
    (stride p n C : ℕ) (hv : value bits=2*index+sign.toNat)
    (hC : PCPPNativeClauseField.budget bits index sign stride p n+1 ≤ C) : ∃ r,
    runFrom (Composition.machine first copyMachine) (prefixBudget bits index stride sign p n)
      (entry (Composition.machine first copyMachine) pre.length
        (data (pre++frame bits++tail) stride p n C []))=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) ∧
      (∀ i,retained i → r.final.tapes i=
        data (pre++frame bits++tail) stride p n C
          (List.replicate (reference index stride sign p n) true) i) ∧
      (∀ j : Fin 15,(r.final.tapes (fieldSlots (workSlots j))).length ≤ C) ∧
      r.steps ≤ prefixBudget bits index stride sign p n := by
  obtain ⟨base,hbase,bheads,b11,b13,b4,b5,b6,bwork,bstep⟩ :=
    PCPPNativeClauseField.padded_run pre bits tail index sign stride p n C hv hC
  obtain ⟨a,ha,_,astep,ah,atapes,akeep⟩ := RecoveryFocus.dock fieldSlots field_injective
    PCPPNativeClauseField.machine _ (heads pre.length)
    (data (pre++frame bits++tail) stride p n C []) _
    (fun j=>(field_input (pre++frame bits++tail) stride p n C pre.length j).1)
    (fun j=>(field_input (pre++frame bits++tail) stride p n C pre.length j).2) base hbase
  have aheads : a.final.heads=heads (pre.length+2*bits.length+1) := by
    funext i
    by_cases hi : i.val<19
    · let j : Fin 19 := ⟨i.val,hi⟩
      have he : fieldSlots j=i := Fin.ext rfl
      rw [←he,ah,bheads]
      exact (field_input (pre++frame bits++tail) stride p n C _ j).1.symm
    · rw [(akeep i (outside_field i (by omega))).1]
      have h13 : i≠13 := by intro h; subst i; simp at hi
      simp only [heads,h13,ite_false]
  have aref : a.final.tapes 11=ZeroPadding.pad C
      (List.replicate (reference index stride sign p n) true) := (atapes 11).trans b11
  have href : reference index stride sign p n ≤ C := by
    have h := bwork 11 (by decide)
    rw [b11,ZeroPadding.pad_length,List.length_replicate] at h
    exact (le_max_right _ _).trans h
  have ready := PCPUnaryCopy.copy_ready (reference index stride sign p n) C 0 (C+1)
  obtain ⟨b,hb,bh,bt,bs⟩ := ready.focus_at copySlots copy_injective a.final.heads a.final.tapes
    (by intro j; fin_cases j
        · exact aref
        · exact (akeep 19 (outside_field 19 (by decide))).2
        · exact (akeep 20 (outside_field 20 (by decide))).2)
    (by intro j; rw [aheads]; fin_cases j <;> rfl)
  have bout : b.final.tapes 19=List.replicate (reference index stride sign p n) true := by
    rw [bt]
    change install copySlots _ _ (copySlots 1)=_
    rw [install_slot _ copy_injective]
    exact ZeroPadding.pad_zero _
  have blog : b.final.tapes 20=List.replicate (C+1) false := by
    rw [bt]
    change install copySlots _ _ (copySlots 2)=_
    rw [install_slot _ copy_injective]
    exact congrArg (fun k=>List.replicate k false) (max_eq_left (by omega))
  have untouched (i : Fin 23) (hi : i≠11 ∧ i≠19 ∧ i≠20) :
      b.final.tapes i=a.final.tapes i := by
    rw [bt,install_other copySlots _ _ _ (by
      intro j; fin_cases j; exact Ne.symm hi.1; exact Ne.symm hi.2.1; exact Ne.symm hi.2.2)]
  have all := Composition.run_join first copyMachine _ _ _ a b ha hb
  have htime : PCPPNativeClauseField.budget bits index sign stride p n+1+
      (2*reference index stride sign p n+4)=prefixBudget bits index stride sign p n := by
    unfold prefixBudget
    omega
  rw [htime] at all
  refine ⟨Composition.joinedReceipt a b,all,bh.trans aheads,?_,?_,?_⟩
  · intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (untouched 4 (by decide)).trans ((atapes 4).trans b4)
    · exact (untouched 5 (by decide)).trans ((atapes 5).trans b5)
    · exact (untouched 6 (by decide)).trans ((atapes 6).trans b6)
    · exact (untouched 13 (by decide)).trans ((atapes 13).trans b13)
    · exact bout
    · exact blog
    · exact (untouched 21 (by decide)).trans (akeep 21 (outside_field 21 (by decide))).2
    · exact (untouched 22 (by decide)).trans (akeep 22 (outside_field 22 (by decide))).2
  · intro j
    change (b.final.tapes (fieldSlots (workSlots j))).length ≤ C
    by_cases hj : fieldSlots (workSlots j)=11
    · rw [hj,bt]
      change (install copySlots _ _ (copySlots 0)).length ≤ C
      rw [install_slot _ copy_injective]
      exact (congrArg List.length b11).symm ▸ bwork 11 (by decide)
    · rw [untouched _ ⟨hj,by
        constructor <;> intro h
        all_goals have hv' := congrArg (fun k : Fin 23=>k.val) h
        all_goals change (workSlots j).val=_ at hv'; have hh := (workSlots j).isLt; omega⟩,atapes]
      exact bwork _ (work_classify j)
  · change a.steps+1+b.steps ≤ _
    unfold prefixBudget
    omega

end NearCubicWires.RepairOrdinary.PCPPNativeClauseReusable
