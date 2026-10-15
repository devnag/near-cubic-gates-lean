import Proof.PCP.PCPPRequestNodeBody

/-! Literal stabilized input/output bank for the Boolean-node loop. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeReuse
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bodyTapes (capacity : ℕ) (source out : List Bool) (i : Fin 646) : List Bool :=
  if i=0 then source else if i=643 then out
  else if i=644 then List.replicate capacity true
  else if i=645 then List.replicate (capacity+1) false else List.replicate capacity false

theorem reset_entry_heads (capacity : ℕ) (source : List Bool) (pos : ℕ) (i : Fin 643) :
    (PCPPRequestNodeReset.entry capacity source pos).heads i=if i=0 then pos else 0 := by
  simp only [PCPPRequestNodeReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config]
  refine Fin.addCases (m:=642) (n:=1) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    by_cases hj : j=0
    · subst j; rfl
    have hj0 : j.castAdd 1≠(0 : Fin 643) :=
      fun h => hj (Fin.ext (congrArg (fun k : Fin 643 => k.val) h))
    rw [if_neg hj0]
    exact PCPPRequestNodeReset.initial_head source pos j hj
  · fin_cases j; rfl

theorem reset_entry_tapes (capacity : ℕ) (source : List Bool) (pos : ℕ) (i : Fin 643) :
    (PCPPRequestNodeReset.entry capacity source pos).tapes i=
      if i=0 then source else List.replicate capacity false := by
  simp only [PCPPRequestNodeReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config]
  refine Fin.addCases (m:=642) (n:=1) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    by_cases hj : j=0
    · subst j
      change ZeroPadding.pad 0 source=source
      exact ZeroPadding.pad_zero source
    have hj0 : j.castAdd 1≠(0 : Fin 643) :=
      fun h => hj (Fin.ext (congrArg (fun k : Fin 643 => k.val) h))
    rw [if_neg hj0,PCPPRequestNodeReset.initial_tape source pos j hj,
      PCPPRequestNodeReset.caps_old]
    simp [PCPPRequestNodeReset.selected,hj,ZeroPadding.pad]
  · fin_cases j
    change ZeroPadding.pad capacity []=List.replicate capacity false
    simp [ZeroPadding.pad]

theorem bodyEntry_heads (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :
    (bodyEntry capacity source pos out).heads=bodyHeads pos out.length := by
  simp only [bodyEntry,Composition.leftConfig,TapeEmbedding.config]
  funext i
  refine Fin.addCases (m:=643) (n:=3) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    rw [reset_entry_heads]
    have hn : j.val≠643 := by omega
    simp only [bodyHeads,Fin.ext_iff,Fin.val_castAdd,Fin.val_zero,
      show (643 : Fin 646).val=643 from rfl,hn,ite_false]
  · fin_cases j <;> rfl

theorem bodyEntry_tapes (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :
    (bodyEntry capacity source pos out).tapes=bodyTapes capacity source out := by
  simp only [bodyEntry,Composition.leftConfig,TapeEmbedding.config]
  funext i
  refine Fin.addCases (m:=643) (n:=3) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    rw [reset_entry_tapes]
    have h643 : j.val≠643 := by omega
    have h644 : j.val≠644 := by omega
    have h645 : j.val≠645 := by omega
    simp only [bodyTapes,Fin.ext_iff,Fin.val_castAdd,Fin.val_zero,
      show (643 : Fin 646).val=643 from rfl,show (644 : Fin 646).val=644 from rfl,
      show (645 : Fin 646).val=645 from rfl,h643,h644,h645,ite_false]
  · fin_cases j <;> rfl

theorem scratch_covers (i : Fin 646) (h0 : i≠0) (h643 : i≠643)
    (h644 : i≠644) (h645 : i≠645) : ∃ j,scratchSlots j=i := by
  have hi := i.isLt
  have hv0 : i.val≠0 := fun h => h0 (Fin.ext h)
  have hv643 : i.val≠643 := fun h => h643 (Fin.ext h)
  have hv644 : i.val≠644 := fun h => h644 (Fin.ext h)
  have hv645 : i.val≠645 := fun h => h645 (Fin.ext h)
  refine ⟨⟨i.val-1,by omega⟩,?_⟩
  apply Fin.ext
  change i.val-1+1=i.val
  omega

theorem body_repeated_run {n : ℕ} (pre tail out : List Bool) (node : BooleanNode n) (capacity : ℕ)
    (hcap : PCPPRequestNodeCold.budget node+1 ≤ capacity) :
    ∃ r,runFrom bodyMachine (6*capacity+12)
      (bodyEntry capacity (pre++PCPPRequestNodeSchema.native node++tail) pre.length out)=some r ∧
      r.final.heads=(bodyEntry capacity (pre++PCPPRequestNodeSchema.native node++tail)
        (pre.length+(PCPPRequestNodeSchema.native node).length) (out++frame (ExecutableInterfaces.encodeBooleanNode node).bits)).heads ∧
      r.final.tapes=(bodyEntry capacity (pre++PCPPRequestNodeSchema.native node++tail)
        (pre.length+(PCPPRequestNodeSchema.native node).length) (out++frame (ExecutableInterfaces.encodeBooleanNode node).bits)).tapes ∧
      r.steps ≤ 6*capacity+12 := by
  obtain ⟨r,hr,rh,r0,ro,rd,rl,rs,rt⟩ := body_run pre tail out node capacity hcap
  refine ⟨r,hr,?_,?_,rt⟩
  · rw [bodyEntry_heads]
    exact rh
  · rw [bodyEntry_tapes]
    funext i
    by_cases hi0 : i=0
    · subst i; exact r0
    by_cases hi643 : i=643
    · subst i; exact ro
    by_cases hi644 : i=644
    · subst i; exact rd
    by_cases hi645 : i=645
    · subst i; exact rl
    obtain ⟨j,hj⟩ := scratch_covers i hi0 hi643 hi644 hi645
    simpa only [bodyTapes,hi0,hi643,hi644,hi645,ite_false,hj] using rs j

end NearCubicWires.RepairOrdinary.PCPPRequestNodeReuse
