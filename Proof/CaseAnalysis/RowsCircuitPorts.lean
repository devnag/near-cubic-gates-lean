import Proof.CaseAnalysis.RowsCircuitPrepare

/-! The cold preparation's exact ports feed both existing top consumers.
Only the top field changes in the allocated gate bank; policy and native
append fields are retained outside that bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_prefix (cap core W L : ℕ) (bits out : List Bool) (bank : Fin 639→List Bool)
    (i : Fin 639) : output cap core W L bits out bank (prefixSlots i)=bank i:=by
  rw [output,Function.update_of_ne (by
    intro h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
    change i.val=640 at hv;omega)]
  exact install_slot prefixSlots prefix_injective _ _ i

theorem output_allocated_gate (cap core W L : ℕ) (bits out : List Bool)
    (bank : Fin 639→List Bool) (i : Fin 1048)
    (hi : CloseoutRowsCircuitAllocate.gate i≠640) :
    output cap core W L bits out bank (CloseoutRowsCircuitAllocate.gate i)=List.replicate cap false:=by
  have hr:=CloseoutRowsCircuitAllocate.gate_range i
  rw [output,Function.update_of_ne hi,framed_other _ _ _ _ _ _ _ _ hr.1,
    seeded_other _ _ _ _ _ _ _ (by
      intro j h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
      fin_cases j
      · change 0=(CloseoutRowsCircuitAllocate.gate i).val at hv;omega
      · change 1693=(CloseoutRowsCircuitAllocate.gate i).val at hv;omega
      · change 1697=(CloseoutRowsCircuitAllocate.gate i).val at hv;omega)]
  have h:=allocated_scratch cap core W L bits out (i.castAdd 6)
  rw [CloseoutRowsCircuitAllocate.scratch_old] at h
  exact h

theorem output_blank (cap core W L : ℕ) (bits out : List Bool) (bank : Fin 639→List Bool)
    (i : Fin 1703) (hi : 639 ≤ i.val ∧ i.val ≤ 1687 ∧ i.val≠1674 ∧ i≠640) :
    output cap core W L bits out bank i=List.replicate cap false:=by
  let j : Fin 1049:=⟨i.val-639,by omega⟩
  obtain ⟨k,hk⟩:=CloseoutRowsCircuitBottom.scratch_covers j (by dsimp [j];omega)
  have he:CloseoutRowsCircuitAllocate.gate k=i:=by
    apply Fin.ext
    have h:=congrArg (fun a : Fin 1059=>a.val) hk
    change (CloseoutRowsCircuitBottom.scratchSlots k).val=i.val-639 at h
    change 639+(CloseoutRowsCircuitBottom.scratchSlots k).val=i.val
    omega
  rw [←he]
  exact output_allocated_gate cap core W L bits out bank k (he ▸ hi.2.2.2)

theorem output_top (cap core W L : ℕ) (bits out : List Bool) (bank : Fin 639→List Bool) :
    output cap core W L bits out bank 640=
      ZeroPadding.pad cap (frame (CloseoutRowsCircuitHeader.codeWord bits 3)):=by
  exact Function.update_self _ _ _

theorem output_gate (cap core W L : ℕ) (bits out : List Bool) (bank : Fin 639→List Bool)
    (count : ℕ) (hcount : bank 624=UnaryTemplate.tape count) (i : Fin 1049) :
    output cap core W L bits out bank (gateSlots i)=
      CloseoutRowsGateBank.input cap count (CloseoutRowsCircuitHeader.codeWord bits 3) i:=by
  simp only [CloseoutRowsGateBank.input,CloseoutRowsGateBank.padded,CloseoutRowsGateBank.input_eq,
    CloseoutRowsGateBank.pads]
  by_cases hd:i.val=1035
  · simp only [if_pos hd,ZeroPadding.pad_zero]
    have he:gateSlots i=prefixSlots 624:=by apply Fin.ext;rw [gate_val,if_pos hd];rfl
    rw [he,output_prefix];exact hcount
  · rw [if_neg hd,if_neg hd]
    by_cases hi:i.val=1
    · rw [if_pos hi]
      have he:gateSlots i=640:=by apply Fin.ext;rw [gate_val,if_neg hd,hi];rfl
      rw [he];exact output_top cap core W L bits out bank
    · rw [if_neg hi]
      rw [output_blank _ _ _ _ _ _ _ _ (by
        rw [gate_val,if_neg hd]
        refine ⟨by omega,by omega,by omega,?_⟩
        intro he;have hv:=congrArg (fun k : Fin 1703=>k.val) he
        rw [gate_val,if_neg hd] at hv
        change 639+i.val=640 at hv;omega)]
      simp [ZeroPadding.pad]

theorem output_external (cap core W L : ℕ) (bits out : List Bool) (bank : Fin 639→List Bool) :
    ∀ i,output cap core W L bits out bank (CloseoutRowsCircuitThresholdTop.external i)=
      CloseoutRowsCircuitThresholdTop.externalData cap i:=by
  intro i;fin_cases i
  all_goals rw [output,Function.update_of_ne (by decide),framed_other _ _ _ _ _ _ _ _ (by decide),
    seeded_other _ _ _ _ _ _ _ (by decide)]
  · exact install_slot CloseoutRowsCircuitAllocate.slots CloseoutRowsCircuitAllocate.slots_injective _ _ 1054
  · have h:=install_slot CloseoutRowsCircuitAllocate.slots CloseoutRowsCircuitAllocate.slots_injective
      (input cap core W L bits out) (PCPTraversal.clearedLocal 1054 cap 0) 1055
    change allocated cap core W L bits out 1695=
      PCPTraversal.clearedLocal 1054 cap 0 ((0 : Fin 1).natAdd 1055) at h
    change allocated cap core W L bits out 1695=List.replicate (cap+1) false
    simpa only [PCPTraversal.clearedLocal,Fin.addCases_right,Nat.max_eq_right (Nat.zero_le _)] using h
  · have h:=allocated_scratch cap core W L bits out ((4 : Fin 6).natAdd 1048)
    rw [CloseoutRowsCircuitAllocate.scratch_new] at h;exact h
  · have h:=allocated_scratch cap core W L bits out ((1 : Fin 6).natAdd 1048)
    rw [CloseoutRowsCircuitAllocate.scratch_new] at h;exact h
  · have h:=allocated_scratch cap core W L bits out ((5 : Fin 6).natAdd 1048)
    rw [CloseoutRowsCircuitAllocate.scratch_new] at h;exact h
  · exact (allocated_other _ _ _ _ _ _ _ (untouched 1689 (by decide))).trans rfl
  · have h:=allocated_scratch cap core W L bits out ((2 : Fin 6).natAdd 1048)
    rw [CloseoutRowsCircuitAllocate.scratch_new] at h;exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
