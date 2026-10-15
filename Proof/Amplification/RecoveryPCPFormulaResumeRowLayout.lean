import Proof.Amplification.RecoverySourceClauseRow

/-! Shared physical tape for the projected-address batch and source-clause
reader. The formula cursor and clause source belong to the enclosing row. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRow
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clauseSlots (i : Fin 281) : Fin 317 := i.castAdd 36
def addressSlots (i : Fin 37) : Fin 317 :=
  ⟨if i.val=31 then 159 else if i.val<31 then 281+i.val else 280+i.val,by
    have hi:=i.isLt; split_ifs <;> omega⟩
theorem clause_injective : Function.Injective clauseSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 317=>i.val) h)
theorem address_injective : Function.Injective addressSlots := by
  intro a b h
  have hv:=congrArg (fun i : Fin 317=>i.val) h
  have ha:=a.isLt; have hb:=b.isLt
  apply Fin.ext
  dsimp [addressSlots] at hv
  split_ifs at hv <;> omega

theorem outside_address (i : Fin 281) (hi : i≠159) : ∀ j,addressSlots j≠clauseSlots i := by
  intro j h
  have hv:=congrArg (fun k : Fin 317=>k.val) h
  have hi' : i.val≠159 := fun he=>hi (Fin.ext he)
  have hil:=i.isLt
  dsimp [addressSlots,clauseSlots] at hv
  split_ifs at hv <;> omega

noncomputable def before (cap : Nat) (source out : List Bool) (sourcePos count : Nat) :=
  RecoverySourceClauseList.cfg 0 cap source [] out sourcePos count 1
noncomputable def initialHeads (cap : Nat) (source out : List Bool) (sourcePos count : Nat) : Fin 317→Nat :=
  Fin.addCases (m:=281) (n:=36) (motive:=fun _=>Nat)
    (before cap source out sourcePos count).heads (fun _=>0)
noncomputable def batchInput (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R) (logCap : Nat) : Fin 37→List Bool :=
  Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryProjectionRowsRewind.batchInput p R Q randomness) (fun _=>List.replicate logCap false)
noncomputable def initialTapes (cap : Nat) (source out : List Bool) (sourcePos count : Nat)
    (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R) (logCap : Nat) : Fin 317→List Bool :=
  install addressSlots (Fin.addCases (m:=281) (n:=36) (motive:=fun _=>List Bool)
    (before cap source out sourcePos count).tapes (fun _=>[])) (batchInput p R Q randomness logCap)
noncomputable def first := RecoveryFocus.machine addressSlots RecoveryProjectionRowsRewind.machine
noncomputable def last := RecoveryFocus.machine clauseSlots RecoverySourceClauseList.machine
noncomputable def machine := Composition.machine first last

theorem address_heads (cap : Nat) (source out : List Bool) (sourcePos count : Nat) (i : Fin 37) :
    initialHeads cap source out sourcePos count (addressSlots i)=0 := by
  by_cases h31 : i.val=31
  · have he : i=31 := Fin.ext h31
    subst i; rfl
  · have hlarge : 281≤(addressSlots i).val := by
      dsimp [addressSlots]; split_ifs <;> omega
    have hsmall : (addressSlots i).val<317 := (addressSlots i).isLt
    let j : Fin 36 := ⟨(addressSlots i).val-281,by omega⟩
    have he : addressSlots i=j.natAdd 281 := by apply Fin.ext; dsimp [j]; omega
    rw [he]
    simp only [initialHeads,Fin.addCases_right]

theorem initial_other (cap : Nat) (source out : List Bool) (sourcePos count : Nat)
    (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R) (logCap : Nat)
    (i : Fin 281) (hi : i≠159) :
    initialTapes cap source out sourcePos count p R Q randomness logCap (clauseSlots i)=
      (before cap source out sourcePos count).tapes i := by
  rw [initialTapes,install_other _ _ _ _ (outside_address i hi)]
  simp only [clauseSlots,Fin.addCases_left]

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRow
