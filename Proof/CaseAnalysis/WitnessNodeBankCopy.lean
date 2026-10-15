import Proof.CaseAnalysis.WitnessNodeBankLayout

/-! Four existing bounded copies fill the common node metadata while
retaining the literal capacity driver and its rewind log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeBank
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem common_outside (i : Fin 759) (hi : 672 ≤ i.val) : ∀ j,common j≠i:=by
  intro j h
  have hv:=congrArg Fin.val h
  change 668+j.val=i.val at hv
  omega
theorem bank_field (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (k : ℕ) (j : Fin 4) :
    bank cap fields source flag k (field j)=fields j:=by
  rw [bank_other _ _ _ _ _ _ (common_outside _ (by simp only [field,Fin.val_natAdd];omega)),erased_field]
theorem bank_driver (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (k : ℕ) :
    bank cap fields source flag k 749=List.replicate cap true:=by
  rw [bank_other _ _ _ _ _ _ (common_outside _ (by decide)),erased_driver]
theorem bank_log (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (k : ℕ) :
    bank cap fields source flag k 750=List.replicate (cap+1) false:=by
  rw [bank_other _ _ _ _ _ _ (common_outside _ (by decide)),erased_log]
theorem bank_succ_other (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool)
    (j : Fin 4) (i : Fin 759) (hi : common j≠i) :
    bank cap fields source flag (j.val+1) i=bank cap fields source flag j.val i:=by
  classical
  by_cases hc:∃ k,common k=i
  · obtain ⟨k,rfl⟩:=hc
    rw [bank_common,bank_common]
    have hne:k.val≠j.val:=by
      intro h
      have he:k=j:=Fin.ext h
      subst k
      exact hi rfl
    have hp:k.val<j.val+1 ↔ k.val<j.val:=by omega
    simp only [hp]
  · have hn:∀ k,common k≠i:=by intro k h;exact hc ⟨k,h⟩
    rw [bank_other _ _ _ _ _ _ hn,bank_other _ _ _ _ _ _ hn]

noncomputable def copyProgram (j : Fin 4):=
  RecoveryFocus.machine (copySlots j) RecoveryBoundedTapeCopy.machine
theorem copy_input (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (j : Fin 4) :
    ∀ i,bank cap fields source flag j.val (copySlots j i)=CloseoutRowsMetadataCopy.input (fields j) cap i:=by
  intro i
  fin_cases i
  · exact bank_field cap fields source flag j.val j
  · change bank cap fields source flag j.val (common j)=_
    rw [bank_common,if_neg (Nat.lt_irrefl _)]
    rfl
  · exact bank_driver cap fields source flag j.val
  · exact bank_log cap fields source flag j.val
theorem copy_install (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool) (j : Fin 4) :
    install (copySlots j) (bank cap fields source flag j.val)
      (CloseoutRowsMetadataCopy.output (fields j) cap)=bank cap fields source flag (j.val+1):=by
  apply HierarchyAllocation.install_eq _ (copy_injective j)
  · intro i
    fin_cases i
    · exact bank_field cap fields source flag (j.val+1) j
    · change bank cap fields source flag (j.val+1) (common j)=_
      rw [bank_common,if_pos (by omega)]
      rfl
    · exact bank_driver cap fields source flag (j.val+1)
    · exact bank_log cap fields source flag (j.val+1)
  · intro i hi
    exact bank_succ_other cap fields source flag j i (hi 1)

theorem copy_ready (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool)
    (j : Fin 4) (hc : (fields j).length≤cap) :
    ReadyRun (copyProgram j) (2*cap+4) (bank cap fields source flag j.val)
      (bank cap fields source flag (j.val+1)):=by
  have h:=(CloseoutRowsMetadataCopy.copy_ready (fields j) cap hc).focus
    (copySlots j) (copy_injective j) (bank cap fields source flag j.val) (copy_input cap fields source flag j)
  rw [copy_install] at h
  exact h

noncomputable def firstTwo:=Composition.machine (copyProgram 0) (copyProgram 1)
noncomputable def firstThree:=Composition.machine firstTwo (copyProgram 2)
noncomputable def copies:=Composition.machine firstThree (copyProgram 3)

theorem copies_ready (cap : ℕ) (fields : Fin 4→List Bool) (source : List Bool) (flag : Bool)
    (hc : ∀ j,(fields j).length≤cap) :
    ClockJoin.ReadyRun copies (8*cap+19) (erased cap fields source flag)
      (bank cap fields source flag 4):=by
  have h (j : Fin 4):ClockJoin.ReadyRun (copyProgram j) (2*cap+4)
      (bank cap fields source flag j.val) (bank cap fields source flag (j.val+1)):=by
    obtain ⟨r,hr,ht,hh,hs⟩:=copy_ready cap fields source flag j (hc j)
    exact ⟨r,hr,ht,hh,hs.le⟩
  have h01:=ClockJoin.join (copyProgram 0) (copyProgram 1) _ _ _ _ _ (h 0) (h 1)
  have h012:=ClockJoin.join firstTwo (copyProgram 2) _ _ _ _ _ h01 (h 2)
  have h0123:=ClockJoin.join firstThree (copyProgram 3) _ _ _ _ _ h012 (h 3)
  have he:((2*cap+4+1+(2*cap+4))+1+(2*cap+4))+1+(2*cap+4)=8*cap+19:=by omega
  rw [he] at h0123
  change ClockJoin.ReadyRun copies (8*cap+19) (bank cap fields source flag 0)
    (bank cap fields source flag 4) at h0123
  rw [bank_zero] at h0123
  exact h0123

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeBank
