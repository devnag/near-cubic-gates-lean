import Proof.CaseAnalysis.WitnessNodeFlag

/-! One existing parallel scratch sweep restores the complete node bank.
Its own unary driver and rewind log are retained for the next node. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem erase_upper (i : Fin 746) : (eraseSlots i).val ≤ 750:=by
  rw [erase_val]
  split_ifs <;> omega
theorem erase_not_output (i : Fin 746) : eraseSlots i≠747:=by
  intro h
  have hv:=congrArg Fin.val h
  rw [erase_val] at hv
  split_ifs at hv <;> omega
theorem erase_not_common (i : Fin 746) (j : Fin 4) :
    eraseSlots i≠(NodeGuard.common j).castAdd 9:=by
  intro h
  have hv:=congrArg Fin.val h
  simp only [erase_val,NodeGuard.common,Fin.val_castAdd] at hv
  split_ifs at hv <;> omega
theorem erase_later (i : Fin 6) (hi : 2 ≤ i.val) : ∀ j : Fin 746,eraseSlots j≠i.natAdd 749:=by
  intro j h
  have hv:=congrArg Fin.val h
  have hb:=erase_upper j
  change (eraseSlots j).val=749+i.val at hv
  omega

noncomputable def eraser:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 744)
noncomputable def erased (cap : ℕ) (tapes : Fin 755 → List Bool):=
  install eraseSlots tapes (PCPTraversal.clearedLocal 744 cap (cap+1))
theorem erased_scratch (cap : ℕ) (tapes : Fin 755 → List Bool) (i : Fin 744) :
    erased cap tapes (scratchSlots i)=List.replicate cap false:=by
  have h:=install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 744 cap (cap+1))
    ((i.castAdd 1).castAdd 1)
  have he:(i.castAdd 1).castAdd 1=i.castAdd 2:=Fin.ext rfl
  have hout:PCPTraversal.clearedLocal 744 cap (cap+1) ((i.castAdd 1).castAdd 1)=List.replicate cap false:=by
    simp only [PCPTraversal.clearedLocal,Fin.addCases_left]
  rw [hout] at h
  simpa only [erased,scratchSlots,he] using h
theorem erased_driver (cap : ℕ) (tapes : Fin 755 → List Bool) :
    erased cap tapes 749=List.replicate cap true:=by
  exact install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 744 cap (cap+1)) 744
theorem erased_log (cap : ℕ) (tapes : Fin 755 → List Bool) :
    erased cap tapes 750=List.replicate (cap+1) false:=by
  have h:=install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 744 cap (cap+1))
    ((0 : Fin 1).natAdd 745)
  have he:eraseSlots ((0 : Fin 1).natAdd 745)=(750 : Fin 755):=by decide
  simpa only [erased,he,PCPTraversal.clearedLocal,Fin.addCases_right,Nat.max_self] using h
theorem erased_other (cap : ℕ) (tapes : Fin 755 → List Bool) (i : Fin 755)
    (hi : ∀ j : Fin 746,eraseSlots j≠i) : erased cap tapes i=tapes i:=install_other _ _ _ _ hi

theorem erased_data (cap w : ℕ) (left right out source : List Bool) (flag : Bool)
    (tapes : Fin 755 → List Bool) (hcap : 1 ≤ cap) (hstore : Stored cap w left right out source flag tapes) :
    erased cap tapes=data cap w left right [] out source flag:=by
  classical
  funext i
  refine Fin.addCases (m:=749) (n:=6) ?_ ?_ i
  · intro j
    simp only [data,Fin.addCases_left]
    change erased cap tapes (nodeSlots j)=(NodeReady.entry cap w left right [] out).tapes j
    by_cases hj:j=747
    · subst j
      rw [node_output_slot,erased_other _ _ _ erase_not_output,NodeReady.entry_output]
      exact hstore.descriptor
    by_cases hc:∃ k : Fin 4,(NodeGuard.common k).castAdd 3=j
    · obtain ⟨k,rfl⟩:=hc
      rw [erased_other _ _ _ (by intro z;exact erase_not_common z k),NodeReady.entry_common]
      exact hstore.common k
    · have hn:∀ k : Fin 4,(NodeGuard.common k).castAdd 3≠j:=by
        intro k h;exact hc ⟨k,h⟩
      rw [NodeReady.entry_blank _ _ _ _ _ hcap j hj hn]
      obtain ⟨k,hk⟩:=scratch_covers j hj hn
      rw [←hk,erased_scratch]
  · intro j
    fin_cases j
    · exact erased_driver cap tapes
    · exact erased_log cap tapes
    · exact (erased_other _ _ _ (erase_later 2 (by decide))).trans (hstore.extra 2)
    · exact (erased_other _ _ _ (erase_later 3 (by decide))).trans (hstore.extra 3)
    · exact (erased_other _ _ _ (erase_later 4 (by decide))).trans (hstore.extra 4)
    · exact (erased_other _ _ _ (erase_later 5 (by decide))).trans (hstore.extra 5)

theorem erase_run (cap w position : ℕ) (left right out source : List Bool) (flag : Bool)
    (tapes : Fin 755 → List Bool) (hcap : 1 ≤ cap) (hstore : Stored cap w left right out source flag tapes) : ∃ result,
    runFrom eraser (2*cap+4) ⟨eraser.start,heads out position,tapes⟩=some result ∧
      result.steps=2*cap+4 ∧ result.final.heads=heads out position ∧
      result.final.tapes=data cap w left right [] out source flag:=by
  have h:=RecoveryScratchErase.erase_ready cap (cap+1) (fun i=>tapes (scratchSlots i)) hstore.scratch
  obtain ⟨r,hr,rh,rt,rs⟩:=h.focus_at eraseSlots erase_injective (heads out position) tapes
    (by
      intro i
      refine Fin.addCases (m:=745) (n:=1) ?_ ?_ i
      · intro j
        refine Fin.addCases (m:=744) (n:=1) ?_ ?_ j
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
      have hn:eraseSlots i≠751:=by
        intro h
        have hv:=congrArg Fin.val h
        have hb:=erase_upper i
        change (eraseSlots i).val=751 at hv
        omega
      simp only [heads,if_neg (erase_not_output i),if_neg hn])
  refine ⟨r,hr,rs,rh,?_⟩
  exact rt.trans (erased_data cap w left right out source flag tapes hcap hstore)

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
