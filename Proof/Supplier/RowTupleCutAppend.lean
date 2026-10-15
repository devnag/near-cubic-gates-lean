import Proof.Supplier.RowTupleEnumeratedEquations

/-! Append the cached binLift signed coefficient after the complete equation.
The common row log resets only the coefficient source; append cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCutAppend
open LocalBitMultitape RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 49 := ![48,31,34]
theorem injective : Function.Injective slots := by decide
noncomputable def machine := RecoveryFocus.machine slots PCPSerializerReuse.copyMachine

theorem pick (i : Fin 49) : RecoveryFocus.pick slots i=
    (if i=48 then some 0 else if i=31 then some 1 else if i=34 then some 2 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slots injective 0
    | exact RecoveryFocus.pick_slot slots injective 1
    | exact RecoveryFocus.pick_slot slots injective 2
    | decide

theorem append_run (bits out : List Bool) (cap : ℕ) (heads : Fin 49 → ℕ) (a : Fin 49 → List Bool)
    (hcap : 2*bits.length+1 ≤ cap) (hh48 : heads 48=0) (hh31 : heads 31=out.length) (hh34 : heads 34=0)
    (ht48 : a 48=frame bits) (ht31 : a 31=out) (ht34 : a 34=List.replicate cap false) :
    ∃ r,runFrom machine (4*bits.length+4) ⟨machine.start,heads,a⟩=some r ∧
      r.final.heads=Function.update heads 31 (out++frame bits).length ∧
      r.final.tapes=Function.update a 31 (out++frame bits) ∧ r.steps ≤ 4*bits.length+4 := by
  obtain ⟨base,hb,bh,bt,bs⟩ := PCPSerializerReuse.copy_run [] bits [] out cap hcap
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slots injective PCPSerializerReuse.copyMachine
    heads a _ _ base hb
  have hi : RecoveryFocus.config slots heads a (PCPSerializerReuse.copyEntry [] bits [] out cap)=
      (⟨machine.start,heads,a⟩ : Configuration 49 5) := by
    apply WilliamsSourceCrop.focus_same slots (⟨machine.start,heads,a⟩ : Configuration 49 5)
    · intro i; fin_cases i
      · exact hh48
      · exact hh31
      · exact hh34
    · intro i; fin_cases i
      · change a 48=[]++frame bits++[]
        simpa only [List.nil_append,List.append_nil] using ht48
      · exact ht31
      · exact ht34
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.le.trans bs⟩
  · rw [rf]
    simp only [RecoveryFocus.config,bh,List.length_nil]
    funext i
    by_cases h48 : i=48
    · subst i; simp [pick,hh48]
    by_cases h31 : i=31
    · subst i; simp [pick]
    by_cases h34 : i=34
    · subst i; simp [pick,hh34]
    simp [pick,h48,h31,h34]
  · rw [rf]
    change install slots a base.final.tapes=_
    rw [bt]
    funext i
    by_cases h48 : i=48
    · subst i; simp [install,pick,ht48]
    by_cases h31 : i=31
    · subst i; simp [install,pick]
    by_cases h34 : i=34
    · subst i; simp [install,pick,ht34]
    simp [install,pick,h48,h31,h34]

end NearCubicWires.RepairOrdinary.RowTupleCutAppend
