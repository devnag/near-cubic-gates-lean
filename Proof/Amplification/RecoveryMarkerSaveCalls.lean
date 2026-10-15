import Proof.Amplification.RecoveryMarkerSaveState

/-! Actual framed copies retain marker fields in the fixed57-tape bank.
Both reset buffers and every destination backing word are paid resources. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerSave
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem install_save (which : Fin 3) (ambient : Fin 57→List Bool)
    (bits : List Bool) (capacity reset : Nat) (hf : ambient 24=frame bits) :
    install (slots which) ambient ![frame bits,frame bits,List.replicate capacity false,List.replicate reset false]=
      Function.update (Function.update (Function.update ambient 22 (List.replicate capacity false))
        51 (List.replicate reset false)) (target which) (frame bits) := by
  funext i
  by_cases hi : ∃ j,slots which j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [install_slot (slots which) (slots_injective which)]
    fin_cases j
    · fin_cases which <;> exact hf.symm
    · fin_cases which <;> rfl
    · fin_cases which <;> rfl
    · fin_cases which <;> rfl
  · rw [install_other (slots which) _ _ _ (by intro j hj; exact hi ⟨j,hj⟩)]
    have hd : i≠target which := by intro he; exact hi ⟨1,he.symm⟩
    have h22 : i≠(22 : Fin 57) := by intro he; exact hi ⟨2,he.symm⟩
    have h51 : i≠(51 : Fin 57) := by intro he; exact hi ⟨3,he.symm⟩
    rw [Function.update_of_ne hd,Function.update_of_ne h51,Function.update_of_ne h22]

theorem target_bound (x : State) (which : Fin 3) (hx : x.Valid) :
    (x.tapes (target which)).length ≤ 2*x.width+1 := by
  fin_cases which
  · change (x.outer.fields 1).length ≤ _
    rw [←hx.2.2]
    exact hx.2.1.2 1
  · change (x.outer.fields 2).length ≤ _
    rw [←hx.2.2]
    exact hx.2.1.2 2
  · exact hx.1.2 1

theorem save_ready (x : State) (which : Fin 3) (bits : List Bool)
    (hx : x.Valid) (hw : bits.length=x.width) (hf : x.inner.data.fields 0=frame bits) :
    ReadyRun (machine which) (8*x.width+8) x.tapes (saved x which).tapes := by
  have hb : (x.tapes (target which)).length ≤ 2*bits.length+1 := by
    rw [hw]
    exact target_bound x which hx
  have h := (RecoveryRootRound.copy_ready bits (x.tapes (target which))
    x.inner.data.capacity x.outer.capacity hb).focus (slots which) (slots_injective which) x.tapes (by
      intro j
      fin_cases j
      · exact hf
      · rfl
      · rfl
      · rfl)
  have hi := install_save which x.tapes bits (max x.inner.data.capacity (2*bits.length+1))
    (max x.outer.capacity (4*bits.length+3)) hf
  rw [hi,hw,←hf,←saved_tapes x which] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryMarkerSave
