import Proof.PCP.PCPClauseListLayout
import Proof.PCP.PCPTripleNative

/-! The complete native clause-list program at its actual ambient caller.
No prepared capacity, triple code, or clause-list code is an input. -/
namespace NearCubicWires.RepairOrdinary.PCPClauseList
open LocalBitMultitape PCPSerializerMass CanonicalBinary
open RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_fields (p : RawProjectionPCP) :
    fields (PCPTripleNative.groups p)=((Codec.clauses p).map encodeBalancedList).map Nat.bits := by
  simp only [fields,PCPTripleNative.groups,List.map_map,Function.comp_def,PCPTripleNative.code_values]

theorem native_code (p : RawProjectionPCP) :
    PCPTraversal.code (fields (PCPTripleNative.groups p))=
      encodeBalancedList ((Codec.clauses p).map encodeBalancedList) := by
  rw [native_fields]
  exact PCPTripleNative.clause_list_code p

theorem focused_run {u : ℕ} (slot : Fin 309 → Fin u) (hinj : Function.Injective slot)
    (groups : List (List (List Bool))) (hthree : ∀ fs∈groups,fs.length=3)
    (h : Fin u → ℕ) (t : Fin u → List Bool)
    (hh : ∀ j,h (slot j)=inputHeads j)
    (ht : ∀ j,t (slot j)=inputTapes groups.length (PCPTripleLoop.stream groups) j) :
    ∃ r,runFrom (RecoveryFocus.machine slot machine) (budget groups)
      ⟨machine.start,h,t⟩=some r ∧
      r.final.tapes (slot 258)=ZeroPadding.pad (PCPPairReusable.capacity (mass (fields groups)))
        (frame (PCPTraversal.code (fields groups)).bits) ∧
      r.final.tapes (slot 259)=(PCPTraversal.code (fields groups)).bits ∧
      r.final.heads (slot 258)=0 ∧ r.final.heads (slot 259)=0 ∧
      (∀ i,(∀ j,slot j≠i) → r.final.tapes i=t i ∧ r.final.heads i=h i) ∧
      r.steps ≤ budget groups := by
  obtain ⟨base,hb,b258,b259,bh258,bh259,_b0,_bh0,bs⟩ := clause_list_run groups hthree
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slot hinj machine h t _ _ base hb
  have he : RecoveryFocus.config slot h t (entry groups.length (PCPTripleLoop.stream groups))=
      (⟨machine.start,h,t⟩ : Configuration u _) := by
    apply TransitionEvent.focused_eq slot hinj (⟨machine.start,h,t⟩ : Configuration u _)
    · rfl
    · intro j
      rw [entry_heads]
      exact (hh j).symm
    · intro j
      rw [entry_tapes]
      exact (ht j).symm
    · intro i _
      rfl
    · intro i _
      rfl
  rw [he] at hr
  have st (j : Fin 309) : r.final.tapes (slot j)=base.final.tapes j := by
    simp only [rf,RecoveryFocus.config,RecoveryFocus.pick_slot slot hinj]
  have sh (j : Fin 309) : r.final.heads (slot j)=base.final.heads j := by
    simp only [rf,RecoveryFocus.config,RecoveryFocus.pick_slot slot hinj]
  refine ⟨r,hr,(st 258).trans b258,(st 259).trans b259,(sh 258).trans bh258,
    (sh 259).trans bh259,?_,by omega⟩
  intro i hi
  have hp : RecoveryFocus.pick slot i=none := by
    classical
    simp [RecoveryFocus.pick,show ¬∃ j,slot j=i by simpa using hi]
  simp only [rf,RecoveryFocus.config,hp]
  exact ⟨True.intro,True.intro⟩

end NearCubicWires.RepairOrdinary.PCPClauseList
