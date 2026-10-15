import Proof.Circuits.DecompositionSourceCall

/-! The child count is physically read from the very same source output.
All source/arity/destination storage remains in its executed configuration. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSource.Counted
open LocalBitMultitape RepairRepresentation ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)
abbrev tapes := Call.tapes a+11
def old (i : Fin (Call.tapes a)) : Fin (tapes a) := i.castAdd 11
def sourceTape := old a (Call.outputTape a)
def localTape (i : Fin 16) := old a (Call.old a i)
def fresh (i : Fin 11) : Fin (tapes a) := i.natAdd (Call.tapes a)
def countSlots : Fin 12→Fin (tapes a) := Fin.cases (sourceTape a) (fresh a)
theorem old_injective : Function.Injective (old a) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (tapes a) => x.val) h)
theorem countSlots_injective : Function.Injective (countSlots a) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro h
      have hv := congrArg Fin.val h
      simp only [countSlots,Fin.cases_zero,Fin.cases_succ,sourceTape,old,fresh,
        Fin.val_castAdd,Fin.val_natAdd] at hv
      have := (Call.outputTape a).isLt
      omega
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      have hv := congrArg Fin.val h
      simp only [countSlots,Fin.cases_zero,Fin.cases_succ,sourceTape,old,fresh,
        Fin.val_castAdd,Fin.val_natAdd] at hv
      have := (Call.outputTape a).isLt
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [countSlots,Fin.cases_succ,fresh,Fin.val_natAdd] at hv
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
theorem old_none (i : Fin (Call.tapes a)) (hi : i≠Call.outputTape a) :
    RecoveryFocus.pick (countSlots a) (old a i)=none := by
  have hn : ¬∃ j,countSlots a j=old a i := by
    rintro ⟨j,hj⟩
    revert hj
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      apply hi
      exact ((old_injective a) h).symm
    · intro h
      have hv := congrArg Fin.val h
      simp only [countSlots,Fin.cases_succ,fresh,old,Fin.val_natAdd,Fin.val_castAdd] at hv
      have := i.isLt
      omega
  simp [RecoveryFocus.pick,hn]

noncomputable def source := TapeEmbedding.machine 11 (Call.machine a)
noncomputable def count := RecoveryFocus.machine (countSlots a) Count.machine
noncomputable def machine := Composition.machine (source a) (count a)
def input (r : ExactDecompositionRequest) : Fin (tapes a)→List Bool :=
  Fin.addCases (Call.input a r) (fun _ => [])
def budget (r : ExactDecompositionRequest) := Call.budget a r+Count.budget (a.output r).children.length+1

theorem counted_run (r : ExactDecompositionRequest) :
    ∃ receipt,run (machine a) (budget a r) (input a r)=some receipt ∧ receipt.steps ≤ budget a r ∧
      receipt.final.tapes (sourceTape a)=exactListWord (a.output r).children ∧
      receipt.final.heads (sourceTape a)=0 ∧
      receipt.final.tapes (fresh a 9)=UnaryTemplate.tape (a.output r).children.length ∧
      receipt.final.heads (fresh a 9)=1 ∧
      receipt.final.tapes (localTape a 12)=UnaryTemplate.tape r.arity ∧ receipt.final.heads (localTape a 12)=1 ∧
      receipt.final.tapes (localTape a 14)=PCPPQueryField.saved r.arity [] ∧ receipt.final.heads (localTape a 14)=0 ∧
      receipt.final.tapes (localTape a 15)=natWord r.arity ∧ receipt.final.heads (localTape a 15)=(natWord r.arity).length := by
  obtain ⟨base,hb,hbs,hout,houtHead,hn,hnh,hback,hbackHead,hprefix,hprefixHead⟩ := Call.call_run a r
  have he := TapeEmbedding.run_embed (Call.machine a) (fun _ : Fin 11 => 0) (fun _ : Fin 11 => []) _ _ base hb
  rw [RepairSource.ProjectionNormalization.StreamPrepare.embed_initial] at he
  let ambient := TapeEmbedding.config (fun _ : Fin 11 => 0) (fun _ : Fin 11 => []) base.final
  have ht : ∀ j,ambient.tapes (countSlots a j)=if j=0 then
      natWord (a.output r).children.length++(a.output r).children.flatMap exactWord else [] := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [ambient,countSlots,sourceTape,old,TapeEmbedding.config,exactListWord] using hout
    · simp [ambient,countSlots,fresh,TapeEmbedding.config]
  have hh : ∀ j,ambient.heads (countSlots a j)=0 := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [ambient,countSlots,sourceTape,old,TapeEmbedding.config] using houtHead
    · simp [ambient,countSlots,fresh,TapeEmbedding.config]
  obtain ⟨last,hl,hls,hsource,hsourceHead,hm,hmh,hother⟩ := Count.focus_run (countSlots a)
    (countSlots_injective a) ambient (a.output r).children.length ((a.output r).children.flatMap exactWord) ht hh
  have hj := Composition.run_join (source a) (count a) _ _ _
    (TapeEmbedding.receipt (fun _ : Fin 11 => 0) (fun _ : Fin 11 => []) base) last he hl
  have htime : Call.budget a r+1+Count.budget (a.output r).children.length=budget a r := by unfold budget; omega
  rw [htime] at hj
  change run (machine a) (budget a r) (input a r)=_ at hj
  have other (i : Fin 16) : last.final.tapes (localTape a i)=base.final.tapes (Call.old a i) ∧
      last.final.heads (localTape a i)=base.final.heads (Call.old a i) := by
    have h := hother (localTape a i) (old_none a (Call.old a i) (Ne.symm (Call.output_ne_old a i)))
    simpa [ambient,localTape,old,TapeEmbedding.config] using h
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 11 => 0) (fun _ : Fin 11 => []) base) last,hj,?_,
    hsource,hsourceHead,hm,hmh,
    (other 12).1.trans hn,(other 12).2.trans hnh,
    (other 14).1.trans hback,(other 14).2.trans hbackHead,
    (other 15).1.trans hprefix,(other 15).2.trans hprefixHead⟩
  change base.steps+1+last.steps ≤ _
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.DecompositionSource.Counted
