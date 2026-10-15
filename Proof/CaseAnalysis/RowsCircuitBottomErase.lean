import Proof.CaseAnalysis.RowsCircuitBottomStore

/-! One paid parallel sweep resets all gate scratch after each actual
bottom. Native outputs, totals, source/bitmap cursors and the domain survive. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem erase_val (i : Fin 1050) : (eraseSlots i).val=
    if i.val<1048 then (if i.val<1035 then i.val else i.val+1)
    else if i.val=1048 then 1055 else 1056 := by
  refine Fin.addCases (m:=1048) (n:=2) ?_ ?_ i
  · intro j
    simp only [eraseSlots,Fin.addCases_left,scratch_val,Fin.val_castAdd,if_pos j.isLt]
  · intro j;fin_cases j <;> rfl
theorem erase_injective : Function.Injective eraseSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [erase_val,erase_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem erase_not_domain : ∀ j,eraseSlots j≠1035:=by
  intro j h;have hv:=congrArg Fin.val h
  rw [erase_val] at hv
  split_ifs at hv <;> omega
theorem erase_extra (i : Fin 10) (hi : i.val≠6 ∧ i.val≠7) : ∀ j,eraseSlots j≠i.natAdd 1049:=by
  intro j h;have hv:=congrArg Fin.val h
  rw [erase_val] at hv
  change (if j.val<1048 then (if j.val<1035 then j.val else j.val+1)
    else if j.val=1048 then 1055 else 1056)=1049+i.val at hv
  split_ifs at hv <;> omega
theorem scratch_covers (i : Fin 1049) (hi : i.val≠1035) : ∃ j,scratchSlots j=coreSlots i:=by
  by_cases h:i.val<1035
  · refine ⟨⟨i.val,by omega⟩,Fin.ext ?_⟩
    rw [scratch_val];change (if i.val<1035 then i.val else i.val+1)=i.val
    rw [if_pos h]
  · refine ⟨⟨i.val-1,by omega⟩,Fin.ext ?_⟩
    rw [scratch_val]
    change (if i.val-1<1035 then i.val-1 else i.val-1+1)=i.val
    rw [if_neg (by omega)];omega

noncomputable def eraser:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1048)
noncomputable def erased (cap : ℕ) (tapes : Fin 1059→List Bool):=
  install eraseSlots tapes (PCPTraversal.clearedLocal 1048 cap (cap+1))
theorem erased_scratch (cap : ℕ) (tapes : Fin 1059→List Bool) (i : Fin 1048) :
    erased cap tapes (scratchSlots i)=List.replicate cap false := by
  have h:=install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 1048 cap (cap+1))
    ((i.castAdd 1).castAdd 1)
  have he:(i.castAdd 1).castAdd 1=i.castAdd 2:=Fin.ext rfl
  simp only [PCPTraversal.clearedLocal,Fin.addCases_left] at h
  simpa only [erased,he,eraseSlots,Fin.addCases_left] using h
theorem erased_driver (cap : ℕ) (tapes : Fin 1059→List Bool) : erased cap tapes 1055=List.replicate cap true := by
  exact install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 1048 cap (cap+1)) 1048
theorem erased_log (cap : ℕ) (tapes : Fin 1059→List Bool) : erased cap tapes 1056=List.replicate (cap+1) false := by
  have h:=install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 1048 cap (cap+1)) 1049
  change erased cap tapes 1056=List.replicate (max (cap+1) (cap+1)) false at h
  simpa only [Nat.max_self] using h
theorem erased_other (cap : ℕ) (tapes : Fin 1059→List Bool) (i : Fin 1059)
    (hi : ∀ j,eraseSlots j≠i) : erased cap tapes i=tapes i:=install_other _ _ _ _ hi

theorem empty_core (cap core : ℕ) (hc : 1 ≤ cap) (i : Fin 1049) :
    CloseoutRowsGateBank.input cap core [] i=
      if i.val=1035 then UnaryTemplate.tape core else List.replicate cap false := by
  simp only [CloseoutRowsGateBank.input,CloseoutRowsGateBank.padded,CloseoutRowsGateBank.input_eq,
    CloseoutRowsGateBank.pads]
  by_cases hi:i.val=1035
  · simp only [if_pos hi,ZeroPadding.pad_zero]
  · rw [if_neg hi,if_neg hi]
    split_ifs
    · exact CloseoutRowsIntegerReady.pad_empty_frame cap hc
    · simp [ZeroPadding.pad]

theorem erased_data (cap core : ℕ) (out source membership : List Bool) (description wireCount : ℕ)
    (flag : Bool) (tapes : Fin 1059→List Bool) (hc : 1 ≤ cap)
    (hs : Stored cap core out source membership description wireCount flag tapes) :
    erased cap tapes=data cap core [] out source membership description wireCount flag := by
  funext i
  refine Fin.addCases (m:=1049) (n:=10) ?_ ?_ i
  · intro j
    change erased cap tapes (coreSlots j)=data cap core [] out source membership description wireCount flag (coreSlots j)
    rw [data_core,empty_core cap core hc]
    by_cases hj:j.val=1035
    · have he:j=1035:=Fin.ext hj;subst j
      change erased cap tapes 1035=UnaryTemplate.tape core
      rw [erased_other _ _ _ erase_not_domain]
      exact hs.domain
    · rw [if_neg hj]
      obtain ⟨k,hk⟩:=scratch_covers j hj
      rw [←hk,erased_scratch]
  · intro j
    rw [data_extra]
    fin_cases j
    · exact (erased_other _ _ _ (erase_extra 0 (by decide))).trans (hs.extra 0)
    · exact (erased_other _ _ _ (erase_extra 1 (by decide))).trans (hs.extra 1)
    · exact (erased_other _ _ _ (erase_extra 2 (by decide))).trans (hs.extra 2)
    · exact (erased_other _ _ _ (erase_extra 3 (by decide))).trans (hs.extra 3)
    · exact (erased_other _ _ _ (erase_extra 4 (by decide))).trans (hs.extra 4)
    · exact (erased_other _ _ _ (erase_extra 5 (by decide))).trans (hs.extra 5)
    · exact erased_driver cap tapes
    · exact erased_log cap tapes
    · exact (erased_other _ _ _ (erase_extra 8 (by decide))).trans (hs.extra 8)
    · exact (erased_other _ _ _ (erase_extra 9 (by decide))).trans (hs.extra 9)

theorem erase_heads (pos memberPos : ℕ) (out : List Bool) (description wireCount : ℕ) (i : Fin 1050) :
    heads pos memberPos out description wireCount (eraseSlots i)=0 := by
  simp only [heads,erase_val]
  split_ifs <;> omega

theorem erase_run (cap core pos memberPos : ℕ) (out source membership : List Bool)
    (description wireCount : ℕ) (flag : Bool) (tapes : Fin 1059→List Bool) (hc : 1 ≤ cap)
    (hs : Stored cap core out source membership description wireCount flag tapes) :
    PCPOuter.Exact eraser (2*cap+4) (heads pos memberPos out description wireCount) tapes
      (heads pos memberPos out description wireCount)
      (data cap core [] out source membership description wireCount flag) := by
  have localRun:=RecoveryScratchErase.erase_ready cap (cap+1) (fun i=>tapes (scratchSlots i)) hs.scratch
  obtain ⟨r,hr,rh,rt,rs⟩:=localRun.focus_at eraseSlots erase_injective
    (heads pos memberPos out description wireCount) tapes (by
      intro i
      refine Fin.addCases (m:=1049) (n:=1) ?_ ?_ i
      · intro j
        refine Fin.addCases (m:=1048) (n:=1) ?_ ?_ j
        · intro k
          simp only [Fin.addCases_left]
          rw [show (k.castAdd 1).castAdd 1=k.castAdd 2 from Fin.ext rfl]
          simp only [eraseSlots,Fin.addCases_left]
        · intro k;have hk:k=0:=Fin.eq_zero k;subst k;exact hs.extra 6
      · intro j;have hj:j=0:=Fin.eq_zero j;subst j;exact hs.extra 7)
    (erase_heads pos memberPos out description wireCount)
  refine ⟨r,hr,rh,?_,rs⟩
  exact rt.trans (erased_data cap core out source membership description wireCount flag tapes hc hs)

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
