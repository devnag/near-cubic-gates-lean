import Proof.PCP.PCPPRequestNodeTail
import Proof.PCP.PCPPRequestNodeReset

/-! A whole reusable native Boolean-node call: parse once, serialize through
the shared machine, append its exact atom, and physically erase local work. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeReuse
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bodyFirst := TapeEmbedding.machine 3 PCPPRequestNodeReset.machine
noncomputable def bodyMachine := Composition.machine bodyFirst tailMachine
noncomputable def bodyEntry (capacity : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :=
  Composition.leftConfig 9 (TapeEmbedding.config (![out.length,0,0] : Fin 3 → ℕ)
    (![out,List.replicate capacity true,List.replicate (capacity+1) false] : Fin 3 → List Bool)
    (PCPPRequestNodeReset.entry capacity source pos))
def bodyHeads (pos appendPos : ℕ) (i : Fin 646) : ℕ :=
  if i=0 then pos else if i=643 then appendPos else 0

theorem body_run {n : ℕ} (pre tail out : List Bool) (node : BooleanNode n) (capacity : ℕ)
    (hcap : PCPPRequestNodeCold.budget node+1 ≤ capacity) :
    ∃ r,runFrom bodyMachine (6*capacity+12)
      (bodyEntry capacity (pre++PCPPRequestNodeSchema.native node++tail) pre.length out)=some r ∧
      r.final.heads=bodyHeads (pre.length+(PCPPRequestNodeSchema.native node).length)
        (out++frame (ExecutableInterfaces.encodeBooleanNode node).bits).length ∧
      r.final.tapes 0=pre++PCPPRequestNodeSchema.native node++tail ∧
      r.final.tapes 643=out++frame (ExecutableInterfaces.encodeBooleanNode node).bits ∧
      r.final.tapes 644=List.replicate capacity true ∧
      r.final.tapes 645=List.replicate (capacity+1) false ∧
      (∀ j,r.final.tapes (scratchSlots j)=List.replicate capacity false) ∧
      r.steps ≤ 6*capacity+12 := by
  obtain ⟨fuel,hfuel,base,hbase,bh0,bh,b0,b630,b642,bsize,bs⟩ :=
    PCPPRequestNodeReset.reset_run pre tail node capacity hcap
  let eheads : Fin 3 → ℕ := ![out.length,0,0]
  let etapes : Fin 3 → List Bool :=
    ![out,List.replicate capacity true,List.replicate (capacity+1) false]
  let prepared := TapeEmbedding.receipt eheads etapes base
  have hp := TapeEmbedding.run_embed PCPPRequestNodeReset.machine eheads etapes _ _ base hbase
  have oldT (i : Fin 643) : prepared.final.tapes (i.castAdd 3)=base.final.tapes i := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have oldH (i : Fin 643) : prepared.final.heads (i.castAdd 3)=base.final.heads i := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have bhAll : prepared.final.heads=bodyHeads (pre.length+(PCPPRequestNodeSchema.native node).length) out.length := by
    funext i
    refine Fin.addCases (m:=643) (n:=3) (fun j => ?_) (fun j => ?_) i
    · rw [oldH]
      by_cases hj : j=0
      · subst j; exact bh0
      have hcast0 : j.castAdd 3≠(0 : Fin 646) :=
        fun h => hj (Fin.ext (congrArg (fun k : Fin 646 => k.val) h))
      have hcast643 : j.castAdd 3≠(643 : Fin 646) := by
        intro h; have hv := congrArg Fin.val h; have hjlt := j.isLt; dsimp at hv; omega
      simp only [bodyHeads,hcast0,hcast643,ite_false]
      exact bh j hj
    · fin_cases j <;> rfl
  let bits := (ExecutableInterfaces.encodeBooleanNode node).bits
  have b630' : prepared.final.tapes 630=ZeroPadding.pad capacity (frame bits) := (oldT 630).trans b630
  have framedSize : 2*bits.length+1 ≤ capacity := by
    have h := bsize 630 (by decide)
    rw [b630,ZeroPadding.pad_length,frame_length] at h
    change max capacity (2*bits.length+1)=capacity at h
    omega
  let index (j : Fin 642) : Fin 643 := ⟨(scratchSlots j).val,scratch_small j⟩
  have index_cast (j : Fin 642) : (index j).castAdd 3=scratchSlots j := rfl
  have index_ne (j : Fin 642) : index j≠0 := by
    intro h
    have hv := congrArg Fin.val h
    change j.val+1=0 at hv
    omega
  have localSize (j : Fin 642) : (prepared.final.tapes (scratchSlots j)).length ≤ capacity := by
    rw [←index_cast j,oldT]
    exact (bsize (index j) (index_ne j)).le
  have localHeads (j : Fin 642) : prepared.final.heads (scratchSlots j)=0 := by
    rw [←index_cast j,oldH]
    exact bh (index j) (index_ne j)
  obtain ⟨last,hl,lh,l0,lo,ld,ll,lscratch,ls⟩ := tail_run capacity (capacity+1)
    bits (List.replicate (capacity-(frame bits).length) false) out
    prepared.final.heads prepared.final.tapes framedSize localSize localHeads b630'
    (by rfl) (by rfl) ((oldT 642).trans b642) (by rfl) (by rfl) (by rfl) (by rfl)
  have joined := Composition.run_join bodyFirst tailMachine _ _ _ prepared last hp hl
  have budgetBound : fuel+1+(4*bits.length+2*capacity+9) ≤ 6*capacity+12 := by omega
  have more := runFrom_moreFuel bodyMachine _
    (6*capacity+12-(fuel+1+(4*bits.length+2*capacity+9))) _
    (Composition.joinedReceipt prepared last) joined
  rw [Nat.add_sub_of_le budgetBound] at more
  refine ⟨Composition.joinedReceipt prepared last,more,?_,?_,lo,ld,?_,lscratch,?_⟩
  · change last.final.heads=_
    rw [lh,bhAll]
    funext i
    by_cases hi : i=643
    · subst i; rfl
    · simp [appendHeads,bodyHeads,hi]
  · exact l0.trans ((oldT 0).trans b0)
  · change last.final.tapes 645=_
    simpa only [max_self] using ll
  · change base.steps+1+last.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.PCPPRequestNodeReuse
