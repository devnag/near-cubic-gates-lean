import Proof.PCP.PCPSerializerReuseTail

/-! One whole reusable serialization call: execute the same cold serializer
inside finite backing, append its canonical framed result, and physically
erase the bank for the next call. The enclosing caller supplies the actual
field-count and outside-bank unary capacity; neither is a new source postulate. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerReuse
open LocalBitMultitape PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bodyFirst := TapeEmbedding.machine 3 serializerMachine
noncomputable def bodyMachine := Composition.machine bodyFirst tailMachine
noncomputable def bodyEntry (capacity log : ℕ) (source : List Bool) (pos count : ℕ) (out : List Bool) :=
  Composition.leftConfig 9 (TapeEmbedding.config (![out.length,0,0] : Fin 3 → ℕ)
    (![out,List.replicate capacity true,List.replicate log false] : Fin 3 → List Bool)
    (serializerEntry capacity source pos count))
def bodyHeads (pos appendPos : ℕ) (i : Fin 132) : ℕ :=
  Fin.addCases (m:=129) (n:=3) (motive:=fun _ => ℕ)
    (serializerHeads pos) (![appendPos,0,0] : Fin 3 → ℕ) i

theorem serializerHeads_zero (pos : ℕ) (i : Fin 129) :
    i≠0 → i≠2 → serializerHeads pos i=0 := by
  refine Fin.addCases (m:=128) (n:=1)
    (motive:=fun j => j≠0 → j≠2 → serializerHeads pos j=0)
    (fun j h0 h2 => ?_) (fun j _ _ => ?_) i
  · have hj0 : j≠0 := by intro he; subst j; exact h0 rfl
    have hj2 : j≠2 := by intro he; subst j; exact h2 rfl
    simp only [serializerHeads,Fin.addCases_left,PCPTraversal.heads,hj0,hj2,ite_false]
  · simp only [serializerHeads,Fin.addCases_right]

theorem body_run (pre : List Bool) (fields : List (List Bool)) (suffix out : List Bool)
    (capacity log : ℕ) (hcap : PCPTraversal.budget (mass fields)+1 ≤ capacity) :
    ∃ r,runFrom bodyMachine
      (2*PCPTraversal.budget (mass fields)+4*(PCPTraversal.code fields).bits.length+2*capacity+12)
      (bodyEntry capacity log (pre++FieldList.stream fields++suffix) pre.length fields.length out)=some r ∧
      r.final.heads=bodyHeads (pre.length+(FieldList.stream fields).length)
        (out++frame (PCPTraversal.code fields).bits).length ∧
      r.final.tapes 0=pre++FieldList.stream fields++suffix ∧
      r.final.tapes 2=RepairSource.VerifierDecoding.CompareMachine.word fields.length ∧
      r.final.tapes 129=out++frame (PCPTraversal.code fields).bits ∧
      r.final.tapes 130=List.replicate capacity true ∧
      r.final.tapes 131=List.replicate (max log (capacity+1)) false ∧
      (∀ j,r.final.tapes (scratchSlots j)=List.replicate capacity false) ∧
      r.steps ≤ 2*PCPTraversal.budget (mass fields)+4*(PCPTraversal.code fields).bits.length+2*capacity+12 := by
  obtain ⟨base,hbase,bh,b0,b2,b77,bsize,blog,bs⟩ := serializer_run pre fields suffix capacity hcap
  let eheads : Fin 3 → ℕ := ![out.length,0,0]
  let etapes : Fin 3 → List Bool := ![out,List.replicate capacity true,List.replicate log false]
  let prepared := TapeEmbedding.receipt eheads etapes base
  have hp := TapeEmbedding.run_embed serializerMachine eheads etapes _ _ base hbase
  have oldT (i : Fin 129) : prepared.final.tapes (i.castAdd 3)=base.final.tapes i := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have oldH (i : Fin 129) : prepared.final.heads (i.castAdd 3)=
      serializerHeads (pre.length+(FieldList.stream fields).length) i := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left,bh]
  have bhAll : prepared.final.heads=bodyHeads (pre.length+(FieldList.stream fields).length) out.length := by
    funext i
    change Fin.addCases (m:=129) (n:=3) (motive:=fun _ => ℕ) base.final.heads eheads i=bodyHeads _ _ i
    rw [bh]
    rfl
  have b77' : prepared.final.tapes 77=ZeroPadding.pad capacity (frame (PCPTraversal.code fields).bits) :=
    (oldT 77).trans b77
  have framedSize : 2*(PCPTraversal.code fields).bits.length+1 ≤ capacity := by
    have hs := bsize 77 (by decide) (by decide)
    rw [b77,ZeroPadding.pad_length,frame_length] at hs
    omega
  let index (j : Fin 127) : Fin 129 := ⟨(scratchSlots j).val,scratch_small j⟩
  have index_cast (j : Fin 127) : (index j).castAdd 3=scratchSlots j := rfl
  have index_ne (j : Fin 127) : index j≠0 ∧ index j≠2 := by
    constructor <;> intro he
    · exact (scratch_not_live j).1 (Fin.ext (congrArg (fun z : Fin 129 => z.val) he))
    · exact (scratch_not_live j).2 (Fin.ext (congrArg (fun z : Fin 129 => z.val) he))
  have localSize (j : Fin 127) : (prepared.final.tapes (scratchSlots j)).length ≤ capacity := by
    rw [←index_cast j,oldT]
    exact (bsize (index j) (index_ne j).1 (index_ne j).2).le
  have localHeads (j : Fin 127) : prepared.final.heads (scratchSlots j)=0 := by
    rw [←index_cast j,oldH]
    exact serializerHeads_zero _ (index j) (index_ne j).1 (index_ne j).2
  obtain ⟨tail,ht,th,t0,t2,tout,td,tl,tscratch,ts⟩ := tail_run capacity log
    (PCPTraversal.code fields).bits
    (List.replicate (capacity-(frame (PCPTraversal.code fields).bits).length) false) out
    prepared.final.heads prepared.final.tapes framedSize localSize localHeads b77'
    (by rfl) (by rfl) ((oldT 128).trans blog) (by rfl) (by rfl) (by rfl) (by rfl)
  have joined := Composition.run_join bodyFirst tailMachine _ _ _ prepared tail hp ht
  have timeEq : (2*PCPTraversal.budget (mass fields)+2)+1+
      (4*(PCPTraversal.code fields).bits.length+2*capacity+9)=
      2*PCPTraversal.budget (mass fields)+4*(PCPTraversal.code fields).bits.length+2*capacity+12 := by omega
  rw [timeEq] at joined
  refine ⟨Composition.joinedReceipt prepared tail,joined,?_,?_,?_,tout,td,tl,tscratch,?_⟩
  · change tail.final.heads=_
    rw [th,bhAll]
    funext i
    refine Fin.addCases (m:=129) (n:=3) (fun j => ?_) (fun j => ?_) i
    · have hn : (j.castAdd 3 : Fin 132)≠129 := by
        intro he; have hv := congrArg Fin.val he; have hj := j.isLt; dsimp at hv; omega
      simp only [appendHeads,hn,ite_false,bodyHeads,Fin.addCases_left]
    · fin_cases j <;> rfl
  · exact t0.trans ((oldT 0).trans b0)
  · exact t2.trans ((oldT 2).trans b2)
  · change base.steps+1+tail.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.PCPSerializerReuse
