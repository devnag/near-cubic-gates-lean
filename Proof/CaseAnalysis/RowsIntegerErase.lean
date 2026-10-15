import Proof.CaseAnalysis.RowsIntegerFlag

/-! One paid parallel sweep restores every local integer tape. The native
output, source cursor, and aggregate validity remain live. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem erase_upper (i : Fin 216) : (eraseSlots i).val ≤ 216:=by
  rw [erase_val]
  split_ifs <;> omega
theorem erase_not_output (i : Fin 216) : eraseSlots i≠213:=by
  intro h
  have hv:=congrArg Fin.val h
  rw [erase_val] at hv
  split_ifs at hv <;> omega
theorem erase_later (i : Fin 5) (hi : 2 ≤ i.val) : ∀ j : Fin 216,eraseSlots j≠i.natAdd 215:=by
  intro j h
  have hv:=congrArg Fin.val h
  have hb:=erase_upper j
  change (eraseSlots j).val=215+i.val at hv
  omega

noncomputable def eraser:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 214)
noncomputable def erased (cap : ℕ) (tapes : Fin 220→List Bool):=
  install eraseSlots tapes (PCPTraversal.clearedLocal 214 cap (cap+1))
theorem erased_scratch (cap : ℕ) (tapes : Fin 220→List Bool) (i : Fin 214) :
    erased cap tapes (scratchSlots i)=List.replicate cap false:=by
  have h:=install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 214 cap (cap+1))
    ((i.castAdd 1).castAdd 1)
  have he:(i.castAdd 1).castAdd 1=i.castAdd 2:=Fin.ext rfl
  have hout:PCPTraversal.clearedLocal 214 cap (cap+1) ((i.castAdd 1).castAdd 1)=List.replicate cap false:=by
    simp only [PCPTraversal.clearedLocal,Fin.addCases_left]
  rw [hout] at h
  simpa only [erased,scratchSlots,he] using h
theorem erased_driver (cap : ℕ) (tapes : Fin 220→List Bool) :
    erased cap tapes 215=List.replicate cap true:=by
  exact install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 214 cap (cap+1)) 214
theorem erased_log (cap : ℕ) (tapes : Fin 220→List Bool) :
    erased cap tapes 216=List.replicate (cap+1) false:=by
  have h:=install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 214 cap (cap+1))
    ((0 : Fin 1).natAdd 215)
  have he:eraseSlots ((0 : Fin 1).natAdd 215)=(216 : Fin 220):=by decide
  simpa only [erased,he,PCPTraversal.clearedLocal,Fin.addCases_right,Nat.max_self] using h
theorem erased_other (cap : ℕ) (tapes : Fin 220→List Bool) (i : Fin 220)
    (hi : ∀ j : Fin 216,eraseSlots j≠i) : erased cap tapes i=tapes i:=install_other _ _ _ _ hi

theorem erased_data (cap : ℕ) (out source : List Bool) (flag : Bool)
    (tapes : Fin 220→List Bool) (hcap : 1 ≤ cap) (hstore : Stored cap out source flag tapes) :
    erased cap tapes=data cap [] out source flag:=by
  classical
  funext i
  refine Fin.addCases (m:=215) (n:=5) ?_ ?_ i
  · intro j
    simp only [data,Fin.addCases_left]
    change erased _ tapes (coreSlots j)=coreTapes cap [] out j
    by_cases hj:j=213
    · subst j
      rw [core_output_slot,erased_other _ _ _ erase_not_output]
      exact hstore.output
    · have hb:coreTapes cap [] out j=List.replicate cap false:=by
        simp only [coreTapes,if_neg hj]
        split_ifs
        · exact CloseoutRowsIntegerReady.pad_empty_frame _ hcap
        · rfl
      rw [hb]
      obtain ⟨k,hk⟩:=scratch_covers j hj
      rw [←hk,erased_scratch]
  · intro j
    fin_cases j
    · exact erased_driver _ tapes
    · exact erased_log _ tapes
    · exact (erased_other _ _ _ (erase_later 2 (by decide))).trans (hstore.extra 2)
    · exact (erased_other _ _ _ (erase_later 3 (by decide))).trans (hstore.extra 3)
    · exact (erased_other _ _ _ (erase_later 4 (by decide))).trans (hstore.extra 4)

theorem erase_run (cap position : ℕ) (out source : List Bool) (flag : Bool)
    (tapes : Fin 220→List Bool) (hcap : 1 ≤ cap) (hstore : Stored cap out source flag tapes) : ∃ result,
    runFrom eraser (2*cap+4)
      ⟨eraser.start,heads out position,tapes⟩=some result ∧
      result.steps=2*cap+4 ∧ result.final.heads=heads out position ∧
      result.final.tapes=data cap [] out source flag:=by
  have h:=RecoveryScratchErase.erase_ready cap (cap+1) (fun i=>tapes (scratchSlots i)) hstore.scratch
  obtain ⟨r,hr,rh,rt,rs⟩:=h.focus_at eraseSlots erase_injective (heads out position) tapes
    (by
      intro i
      refine Fin.addCases (m:=215) (n:=1) ?_ ?_ i
      · intro j
        refine Fin.addCases (m:=214) (n:=1) ?_ ?_ j
        · intro k
          simp only [Fin.addCases_left]
          rfl
        · intro k
          have hk:k=0:=Fin.eq_zero k
          subst k
          exact hstore.extra 0
      · intro j
        have hj:j=0:=Fin.eq_zero j
        subst j
        exact hstore.extra 1)
    (by
      intro i
      have hn:eraseSlots i≠217:=by
        intro h
        have hv:=congrArg Fin.val h
        have hb:=erase_upper i
        change (eraseSlots i).val=217 at hv
        omega
      simp only [heads,if_neg (erase_not_output i),if_neg hn])
  refine ⟨r,hr,rs,rh,?_⟩
  exact rt.trans (erased_data cap out source flag tapes hcap hstore)

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
