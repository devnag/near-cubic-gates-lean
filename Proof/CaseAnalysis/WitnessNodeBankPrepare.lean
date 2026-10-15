import Proof.CaseAnalysis.WitnessNodeBankCopy

/-! A supplied literal capacity driver allocates the bank by an actual
parallel erase. The four retained physical metadata words are then loaded
by the existing bounded-copy worker, with every join charged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeBank
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_work (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (j : Fin 750) :
    input cap fields source flag (workSlot j)=[]:=by
  let i : Fin 755:=⟨(workSlot j).val,(work_small j).trans (by decide)⟩
  have he:workSlot j=i.castAdd 4:=Fin.ext rfl
  have h749:i≠749:=by
    intro h
    have hv:=congrArg (fun a : Fin 755=>a.val) h
    exact (work_avoids j).2.1 (Fin.ext hv)
  have h751:i≠751:=by
    intro h
    have hv:=congrArg (fun a : Fin 755=>a.val) h
    exact (work_avoids j).2.2.2 (Fin.ext hv)
  have h754:i≠754:=by
    intro h
    have hv:=congrArg Fin.val h
    have hb:=work_small j
    change (workSlot j).val=754 at hv
    omega
  rw [he]
  simp only [input,Fin.addCases_left,if_neg h749,if_neg h751,if_neg h754]

noncomputable def allocate:=RecoveryFocus.machine sweepSlot (RecoveryScratchErase.resetMachine 750)
theorem allocate_ready (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) :
    ReadyRun allocate (2*cap+4) (input cap fields source flag) (erased cap fields source flag):=by
  have h:=RecoveryScratchErase.erase_ready cap 0 (fun _ : Fin 750=>[]) (by intro i;simp)
  have hf:=h.focus sweepSlot sweep_injective (input cap fields source flag) (by
    intro i
    refine Fin.addCases (m:=751) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=750) (n:=1) ?_ ?_ j
      · intro k
        simp only [Fin.addCases_left]
        have he:(k.castAdd 1).castAdd 1=k.castAdd 2:=Fin.ext rfl
        rw [he]
        simp only [sweepSlot,Fin.addCases_left]
        exact input_work cap fields source flag k
      · intro k
        have hk:k=0:=Fin.eq_zero k
        subst k
        rfl
    · intro j
      have hj:j=0:=Fin.eq_zero j
      subst j
      rfl)
  change ReadyRun allocate (2*cap+4) (input cap fields source flag)
    (install sweepSlot (input cap fields source flag) (PCPTraversal.clearedLocal 750 cap (cap+1)))
  unfold PCPTraversal.clearedLocal
  simp only [Nat.max_self]
  simpa only [allocate,Nat.zero_max] using hf

noncomputable def machine:=Composition.machine allocate copies
theorem bank_ready (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool)
    (hc : ∀ j,(fields j).length≤cap) :
    ClockJoin.ReadyRun machine (10*cap+24) (input cap fields source flag)
      (bank cap fields source flag 4):=by
  obtain ⟨r,hr,ht,hh,hs⟩:=allocate_ready cap fields source flag
  have ha:ClockJoin.ReadyRun allocate (2*cap+4) (input cap fields source flag)
      (erased cap fields source flag):=⟨r,hr,ht,hh,hs.le⟩
  have h:=ClockJoin.join allocate copies _ _ _ _ _ ha (copies_ready cap fields source flag hc)
  have he:2*cap+4+1+(8*cap+19)=10*cap+24:=by omega
  rw [he] at h
  exact h

theorem erased_work (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (j : Fin 750) :
    erased cap fields source flag (workSlot j)=List.replicate cap false:=by
  have h:=install_slot sweepSlot sweep_injective (input cap fields source flag)
    (PCPTraversal.clearedLocal 750 cap (cap+1)) ((j.castAdd 1).castAdd 1)
  have hout:PCPTraversal.clearedLocal 750 cap (cap+1) ((j.castAdd 1).castAdd 1)=List.replicate cap false:=by
    simp only [PCPTraversal.clearedLocal,Fin.addCases_left]
  rw [hout] at h
  have he:(j.castAdd 1).castAdd 1=j.castAdd 2:=Fin.ext rfl
  simpa only [erased,he,sweepSlot,Fin.addCases_left] using h
theorem sweep_retained (i : Fin 759) (hi : i=747 ∨ i=751 ∨ i=754) : ∀ j,sweepSlot j≠i:=by
  intro j
  refine Fin.addCases (m:=750) (n:=2) ?_ ?_ j
  · intro k
    simp only [sweepSlot,Fin.addCases_left]
    rcases hi with rfl|rfl|rfl
    · exact (work_avoids k).1
    · exact (work_avoids k).2.2.2
    · intro h
      have hv:=congrArg Fin.val h
      have hb:=work_small k
      change (workSlot k).val=754 at hv
      omega
  · intro k
    simp only [sweepSlot,Fin.addCases_right]
    rcases hi with rfl|rfl|rfl <;> fin_cases k <;> decide
theorem bank_retained (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (k : ℕ)
    (i : Fin 759) (hi : i=747 ∨ i=751 ∨ i=754) :
    bank cap fields source flag k i=input cap fields source flag i:=by
  rw [bank_other _ _ _ _ _ _ (common_outside _ (by rcases hi with rfl|rfl|rfl <;> decide)),
    erased,install_other _ _ _ _ (sweep_retained i hi)]

theorem bank_data (cap w : ℕ) (left right source : List Bool) (flag : Bool) (hcap : 1≤cap) :
    ∀ i : Fin 755,bank cap (NodeGuard.shared w left right) source flag 4 (i.castAdd 4)=
      NodeRound.data cap w left right [] [] source flag i:=by
  intro i
  refine Fin.addCases (m:=749) (n:=6) ?_ ?_ i
  · intro j
    simp only [NodeRound.data,Fin.addCases_left]
    by_cases ho:j=747
    · subst j
      rw [NodeReady.entry_output]
      exact bank_retained cap _ source flag 4 747 (Or.inl rfl)
    by_cases hc:∃ k : Fin 4,(NodeGuard.common k).castAdd 3=j
    · obtain ⟨k,rfl⟩:=hc
      rw [NodeReady.entry_common]
      change bank cap _ source flag 4 (common k)=_
      rw [bank_common,if_pos k.isLt]
    · have hn:∀ k : Fin 4,(NodeGuard.common k).castAdd 3≠j:=by intro k h;exact hc ⟨k,h⟩
      rw [NodeReady.entry_blank _ _ _ _ _ hcap j ho hn]
      have hn':∀ k,common k≠(j.castAdd 6).castAdd 4:=by
        intro k h
        have hv:=congrArg (fun a : Fin 759=>a.val) h
        apply hn k
        exact Fin.ext hv
      rw [bank_other _ _ _ _ _ _ hn']
      by_cases hj:j.val<747
      · have he:((j.castAdd 6).castAdd 4)=workSlot ⟨j.val,by omega⟩:=by
          apply Fin.ext
          simp only [Fin.val_castAdd,work_val,hj,if_true]
        rw [he,erased_work]
      · have he:j.val=748:=by
          have hne:j.val≠747:=by intro h;exact ho (Fin.ext h)
          omega
        have he':((j.castAdd 6).castAdd 4)=workSlot 747:=Fin.ext (by change j.val=748;exact he)
        rw [he',erased_work]
  · intro j
    fin_cases j
    · exact bank_driver cap _ source flag 4
    · exact bank_log cap _ source flag 4
    · exact bank_retained cap _ source flag 4 751 (Or.inr (Or.inl rfl))
    · rw [bank_other _ _ _ _ _ _ (common_outside _ (by decide))]
      exact erased_work cap _ source flag 748
    · rw [bank_other _ _ _ _ _ _ (common_outside _ (by decide))]
      exact erased_work cap _ source flag 749
    · exact bank_retained cap _ source flag 4 754 (Or.inr (Or.inr rfl))

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeBank
