import Proof.Supplier.RowCoefficientWhole

/-! Append the produced coefficient frame with the existing physical cursor
restore copier. Its reset workspace is supplied by the emitter's retained
log, so this handoff needs no separately manufactured capacity tape. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientAppendCall
open LocalBitMultitape RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 29 := ![26,28,27]
theorem injective : Function.Injective slots := by decide
noncomputable def machine := RecoveryFocus.machine slots PCPSerializerReuse.copyMachine

theorem pick (i : Fin 29) : RecoveryFocus.pick slots i=
    (if i=26 then some 0 else if i=28 then some 1 else if i=27 then some 2 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slots injective 0
    | exact RecoveryFocus.pick_slot slots injective 1
    | exact RecoveryFocus.pick_slot slots injective 2
    | decide

theorem append_run (bits out : List Bool) (cap : ℕ) (heads : Fin 29 → ℕ) (a : Fin 29 → List Bool)
    (hcap : 2*bits.length+1 ≤ cap) (hh26 : heads 26=0) (hh28 : heads 28=out.length) (hh27 : heads 27=0)
    (ht26 : a 26=frame bits) (ht28 : a 28=out) (ht27 : a 27=List.replicate cap false) :
    ∃ r,runFrom machine (4*bits.length+4) ⟨machine.start,heads,a⟩=some r ∧
      r.final.heads=Function.update heads 28 (out++frame bits).length ∧
      r.final.tapes=Function.update a 28 (out++frame bits) ∧ r.steps ≤ 4*bits.length+4 := by
  obtain ⟨base,hb,bh,bt,bs⟩ := PCPSerializerReuse.copy_run [] bits [] out cap hcap
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slots injective PCPSerializerReuse.copyMachine
    heads a _ _ base hb
  have hi : RecoveryFocus.config slots heads a (PCPSerializerReuse.copyEntry [] bits [] out cap)=
      (⟨machine.start,heads,a⟩ : Configuration 29 5) := by
    apply WilliamsSourceCrop.focus_same slots (⟨machine.start,heads,a⟩ : Configuration 29 5)
    · intro i; fin_cases i
      · exact hh26
      · exact hh28
      · exact hh27
    · intro i; fin_cases i
      · change a 26=[]++frame bits++[]
        simpa only [List.nil_append,List.append_nil] using ht26
      · exact ht28
      · exact ht27
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.le.trans bs⟩
  · rw [rf]
    simp only [RecoveryFocus.config,bh,List.length_nil]
    funext i
    by_cases h26 : i=26
    · subst i; simp [pick,hh26]
    by_cases h28 : i=28
    · subst i; simp [pick]
    by_cases h27 : i=27
    · subst i; simp [pick,hh27]
    simp [pick,h26,h28,h27]
  · rw [rf]
    change install slots a base.final.tapes=_
    rw [bt]
    funext i
    by_cases h26 : i=26
    · subst i; simp [install,pick,ht26]
    by_cases h28 : i=28
    · subst i; simp [install,pick]
    by_cases h27 : i=27
    · subst i; simp [install,pick,ht27]
    simp [install,pick,h26,h28,h27]

theorem field_log (w p n cap : ℕ) :
    RowCoefficientField.output w p n cap 0 6=List.replicate (2*w+4) false := by
  have h := install_slot RowCoefficientField.emitSlots RowCoefficientField.emit_injective
    (RowCoefficientField.middle w p n cap 0)
    (RowCoefficientEmit.output (decide (n ≤ p))
      (SignedSortKey.binary w (RowCoefficientNormalize.magnitude p n)) 0) 3
  change RowCoefficientField.output w p n cap 0 6=List.replicate
    (max 0 (2*(SignedSortKey.binary w (RowCoefficientNormalize.magnitude p n)).length+4)) false at h
  simpa only [SignedSortKey.binary_length,Nat.zero_max] using h

end NearCubicWires.RepairOrdinary.RowCoefficientAppendCall
