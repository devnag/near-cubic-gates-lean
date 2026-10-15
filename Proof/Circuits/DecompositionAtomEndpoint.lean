import Proof.Circuits.DecompositionAtomBody

/-! Literal stabilized input/output bank for the integer-field loop. -/
namespace NearCubicWires.RepairOrdinary.DecompositionAtomReuse
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bodyTapes (capacity : ℕ) (source out : List Bool) (i : Fin 179) : List Bool :=
  if i=0 then source else if i=176 then out
  else if i=177 then List.replicate capacity true
  else if i=178 then List.replicate (capacity+1) false else List.replicate capacity false

theorem reset_entry_heads (capacity : ℕ) (source : List Bool) (pos : ℕ) (i : Fin 176) :
    (DecompositionAtomReset.entry capacity source pos).heads i=if i=0 then pos else 0 := by
  simp only [DecompositionAtomReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config]
  refine Fin.addCases (m:=175) (n:=1) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    by_cases hj : j=0
    · subst j; rfl
    have hj0 : j.castAdd 1≠(0 : Fin 176) :=
      fun h => hj (Fin.ext (congrArg (fun k : Fin 176 => k.val) h))
    rw [if_neg hj0]
    exact DecompositionAtomReset.entry_heads source pos j hj
  · fin_cases j; rfl

theorem reset_entry_tapes (capacity : ℕ) (source : List Bool) (pos : ℕ) (i : Fin 176) :
    (DecompositionAtomReset.entry capacity source pos).tapes i=
      if i=0 then source else List.replicate capacity false := by
  simp only [DecompositionAtomReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config]
  refine Fin.addCases (m:=175) (n:=1) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    by_cases hj : j=0
    · subst j
      change ZeroPadding.pad 0 source=source
      exact ZeroPadding.pad_zero source
    have hj0 : j.castAdd 1≠(0 : Fin 176) :=
      fun h => hj (Fin.ext (congrArg (fun k : Fin 176 => k.val) h))
    rw [if_neg hj0,DecompositionAtomReset.entry_tapes source pos j hj,
      DecompositionAtomReset.caps_old]
    simp [DecompositionAtomReset.selected,hj,ZeroPadding.pad]
  · fin_cases j
    change ZeroPadding.pad capacity []=List.replicate capacity false
    simp [ZeroPadding.pad]

theorem bodyEntry_heads (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :
    (bodyEntry capacity source pos out).heads=bodyHeads pos out.length := by
  simp only [bodyEntry,Composition.leftConfig,TapeEmbedding.config]
  funext i
  refine Fin.addCases (m:=176) (n:=3) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    rw [reset_entry_heads]
    have hn : j.val≠176 := by omega
    simp only [bodyHeads,Fin.ext_iff,Fin.val_castAdd,Fin.val_zero,
      show (176 : Fin 179).val=176 from rfl,hn,ite_false]
  · fin_cases j <;> rfl

theorem bodyEntry_tapes (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :
    (bodyEntry capacity source pos out).tapes=bodyTapes capacity source out := by
  simp only [bodyEntry,Composition.leftConfig,TapeEmbedding.config]
  funext i
  refine Fin.addCases (m:=176) (n:=3) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    rw [reset_entry_tapes]
    have h176 : j.val≠176 := by omega
    have h177 : j.val≠177 := by omega
    have h178 : j.val≠178 := by omega
    simp only [bodyTapes,Fin.ext_iff,Fin.val_castAdd,Fin.val_zero,
      show (176 : Fin 179).val=176 from rfl,show (177 : Fin 179).val=177 from rfl,
      show (178 : Fin 179).val=178 from rfl,h176,h177,h178,ite_false]
  · fin_cases j <;> rfl

theorem scratch_covers (i : Fin 179) (h0 : i≠0) (h176 : i≠176)
    (h177 : i≠177) (h178 : i≠178) : ∃ j,scratchSlots j=i := by
  have hi := i.isLt
  have hv0 : i.val≠0 := fun h => h0 (Fin.ext h)
  have hv176 : i.val≠176 := fun h => h176 (Fin.ext h)
  have hv177 : i.val≠177 := fun h => h177 (Fin.ext h)
  have hv178 : i.val≠178 := fun h => h178 (Fin.ext h)
  refine ⟨⟨i.val-1,by omega⟩,?_⟩
  apply Fin.ext
  change i.val-1+1=i.val
  omega

theorem body_repeated_run (pre tail out : List Bool) (z : ℤ) (capacity : ℕ)
    (hcap : DecompositionAtom.budget z+1 ≤ capacity) :
    ∃ r,runFrom bodyMachine (6*capacity+12)
      (bodyEntry capacity (pre++intWord z++tail) pre.length out)=some r ∧
      r.final.heads=(bodyEntry capacity (pre++intWord z++tail)
        (pre.length+(intWord z).length) (out++frame (CanonicalBinary.encodeInt z).bits)).heads ∧
      r.final.tapes=(bodyEntry capacity (pre++intWord z++tail)
        (pre.length+(intWord z).length) (out++frame (CanonicalBinary.encodeInt z).bits)).tapes ∧
      r.steps ≤ 6*capacity+12 := by
  obtain ⟨r,hr,rh,r0,ro,rd,rl,rs,rt⟩ := body_run pre tail out z capacity hcap
  refine ⟨r,hr,?_,?_,rt⟩
  · rw [bodyEntry_heads]
    exact rh
  · rw [bodyEntry_tapes]
    funext i
    by_cases hi0 : i=0
    · subst i; exact r0
    by_cases hi176 : i=176
    · subst i; exact ro
    by_cases hi177 : i=177
    · subst i; exact rd
    by_cases hi178 : i=178
    · subst i; exact rl
    obtain ⟨j,hj⟩ := scratch_covers i hi0 hi176 hi177 hi178
    simpa only [bodyTapes,hi0,hi176,hi177,hi178,ite_false,hj] using rs j

end NearCubicWires.RepairOrdinary.DecompositionAtomReuse
