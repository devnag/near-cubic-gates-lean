import Proof.PCP.PCPPNativeClauseFullReuseLayout

/-! Execute the original clause on retained padded references, then advance
the actual counters and erase precisely the four transient unary tapes. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseReuse
open LocalBitMultitape RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem padded_run (pre tail : List Bool) (bits : Fin 3→List Bool)
    (indices : Fin 3→ℕ) (signs : Fin 3→Bool) (stride p n C base accumulator : ℕ) (out : List Bool)
    (hv : ∀ i,value (bits i)=2*indices i+(signs i).toNat)
    (hC : ∀ i,PCPPNativeClauseField.budget (bits i) (indices i) (signs i) stride p n+1≤C)
    (hB : PCPPNativeClauseBank.Capacity
      (PCPPNativeClauseBank.values base accumulator (PCPPNativeClauseBody.references indices signs stride p n)) C) :
    ∃ r,runFrom PCPPNativeClauseBody.machine (PCPPNativeClauseBody.budget bits indices signs stride p n C base accumulator)
      (entry PCPPNativeClauseBody.machine (pre++PCPPNativeClauseTriple.fields bits++tail) pre.length
        stride p n C base accumulator 0 (fun _=>0) out)=some r ∧
      r.final.heads=PCPPNativeClauseBody.heads (pre++PCPPNativeClauseTriple.fields bits).length
        (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator (PCPPNativeClauseBody.references indices signs stride p n))) ∧
      r.final.tapes=data (pre++PCPPNativeClauseTriple.fields bits++tail) stride p n C base accumulator 0
        (PCPPNativeClauseBody.references indices signs stride p n)
        (out++PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator (PCPPNativeClauseBody.references indices signs stride p n))) ∧
      r.steps≤PCPPNativeClauseBody.budget bits indices signs stride p n C base accumulator := by
  obtain ⟨a,ha,ah,atapes,as⟩:=PCPPNativeClauseBody.body_run pre tail bits indices signs stride p n C base accumulator out hv hC hB
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config PCPPNativeClauseBody.machine (padding C) _ _ a ha
  have hi : ZeroPadding.config (padding C) (PCPPNativeClauseBody.entry PCPPNativeClauseBody.machine
      (pre++PCPPNativeClauseTriple.fields bits++tail) pre.length stride p n C base accumulator (fun _=>0) out)=
      entry PCPPNativeClauseBody.machine (pre++PCPPNativeClauseTriple.fields bits++tail) pre.length
        stride p n C base accumulator 0 (fun _=>0) out :=
    configuration_ext rfl rfl (zero_data _ _ _ _ _ _ _ _ _).symm
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.le.trans as⟩
  · rw [rf]; exact ah
  · rw [rf]
    change (fun i=>ZeroPadding.pad (padding C i) (a.final.tapes i))=_
    rw [atapes]
    exact (zero_data _ _ _ _ _ _ _ _ _).symm

theorem counter_run (source : List Bool) (pos stride p n C base accumulator : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool) (ha : accumulator≤base) (hC : base+3≤C) :
    ∃ r,runFrom counter (6*base+20) (entry counter source pos stride p n C base accumulator 0 refs out)=some r ∧
      r.final.heads=PCPPNativeClauseBody.heads pos out ∧
      r.final.tapes=data source stride p n C (base+3) (base+2) (base+3) refs out ∧ r.steps≤6*base+20 := by
  obtain ⟨a,ar,atapes,ah,as⟩:=PCPPNativeClauseCounter.counter_run base accumulator (C+1) ha (by omega)
  obtain ⟨b,br,bf,bs,_⟩:=ZeroPadding.run_config PCPPNativeClauseCounter.machine (counterPadding C) _ _ a ar
  have bh : b.final.heads=fun _=>0 := by rw [bf]; exact funext ah
  have bt : b.final.tapes=fun j=>ZeroPadding.pad (counterPadding C j)
      (PCPPNativeClauseCounter.data (base+3) (base+2) (base+3) (C+1) j) := by
    rw [bf]
    change (fun j=>ZeroPadding.pad (counterPadding C j) (a.final.tapes j))=_
    rw [atapes]
  obtain ⟨r,hr,_,rs,rh,rt,keep⟩:=RecoveryFocus.dock counterSlots counter_injective
    PCPPNativeClauseCounter.machine _ (PCPPNativeClauseBody.heads pos out)
    (data source stride p n C base accumulator 0 refs out) _
    (fun j=>(counter_input source pos stride p n C base accumulator 0 refs out j).1)
    (fun j=>(counter_input source pos stride p n C base accumulator 0 refs out j).2) b br
  refine ⟨r,hr,?_,?_,rs.le.trans (bs.le.trans as)⟩
  · funext i
    by_cases hi : ∃ j,counterSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh,bh]
      exact (counter_input source pos stride p n C (base+3) (base+2) (base+3) refs out j).1.symm
    · exact (keep i (by intro j h; exact hi ⟨j,h⟩)).1
  · funext i
    by_cases hi : ∃ j,counterSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt,bt]
      exact (counter_input source pos stride p n C (base+3) (base+2) (base+3) refs out j).2.symm
    · have hn : ∀ j,counterSlots j≠i:=by intro j h; exact hi ⟨j,h⟩
      rw [(keep i hn).2]
      exact counter_outside source stride p n C base accumulator 0 (base+3) (base+2) (base+3) refs out i hn

theorem erase_run (source : List Bool) (pos stride p n C base accumulator temporary : ℕ)
    (refs : Fin 3→ℕ) (out : List Bool) (ht : temporary≤C) (hC : ∀j,refs j≤C) :
    ∃ r,runFrom erase (2*C+4) (entry erase source pos stride p n C base accumulator temporary refs out)=some r ∧
      r.final.heads=PCPPNativeClauseBody.heads pos out ∧
      r.final.tapes=data source stride p n C base accumulator 0 (fun _=>0) out ∧ r.steps≤2*C+4 := by
  let backing : Fin 4→List Bool :=
    ![ZeroPadding.pad C (List.replicate (refs 0) true),ZeroPadding.pad C (List.replicate (refs 1) true),
      ZeroPadding.pad C (List.replicate (refs 2) true),ZeroPadding.pad C (List.replicate temporary true)]
  have hb : ∀ j,(backing j).length≤C := by
    have bound (k : ℕ) (hk : k≤C) : (ZeroPadding.pad C (List.replicate k true)).length≤C := by
      rw [ZeroPadding.pad_length,List.length_replicate]
      exact max_le (le_refl _) hk
    intro j
    fin_cases j
    · exact bound _ (hC 0)
    · exact bound _ (hC 1)
    · exact bound _ (hC 2)
    · exact bound _ ht
  have ready:=RecoveryScratchErase.erase_ready C (C+1) backing hb
  obtain ⟨r,hr,rh,rt,rs⟩:=ready.focus_at eraseSlots erase_injective (PCPPNativeClauseBody.heads pos out)
    (data source stride p n C base accumulator temporary refs out)
    (by intro j; fin_cases j <;> first | rfl | exact ZeroPadding.pad_zero _)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,rh,?_,rs.le⟩
  rw [rt]
  apply HierarchyWidth.install_eq eraseSlots erase_injective
  · intro j
    fin_cases j
    all_goals first | rfl | exact ZeroPadding.pad_zero _ | skip
    change ZeroPadding.pad 0 (List.replicate (C+1) false)=List.replicate (max (C+1) (C+1)) false
    rw [max_self]
    exact ZeroPadding.pad_zero _
  · intro i hi
    exact (erase_outside source stride p n C base accumulator temporary refs out i hi).symm

end NearCubicWires.RepairOrdinary.PCPPNativeClauseReuse
