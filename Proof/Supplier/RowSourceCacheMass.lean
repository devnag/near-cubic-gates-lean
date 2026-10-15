import Proof.Supplier.RowCacheMass
import Proof.Circuits.DecompositionSourceEntry

/-! Execute the chosen native decomposition source once, then measure that
same cache. Its arity, occurrence count and byte mass are actual paid outputs
of the cold source call, rather than supplied row-bank metadata. -/
namespace NearCubicWires.RepairOrdinary.RowSourceCacheMass
open LocalBitMultitape RepairRepresentation ExecutableInterfaces DecompositionSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)
abbrev tapes := Counted.tapes a+4
def old (i : Fin (Counted.tapes a)) : Fin (tapes a) := i.castAdd 4
def fresh (i : Fin 4) : Fin (tapes a) := i.natAdd (Counted.tapes a)
def sourceTape := old a (Counted.sourceTape a)
def arityTape := old a (Counted.localTape a 12)
def countTape := old a (Counted.fresh a 9)
def massTape := fresh a 2
def selectCore : Fin 3→Fin 5 := ![0,3,4]
def core : Fin 3→Fin (Counted.tapes a) := Entry.recordSlots a ∘ selectCore
theorem core_injective : Function.Injective (core a) :=
  (Entry.recordSlots_injective a).comp (by decide : Function.Injective selectCore)
def permutation : Fin 7→Fin (3+4) := ![0,3,4,1,2,5,6]
def slots : Fin 7→Fin (tapes a) := fun i=>
  Fin.addCases (m:=3) (n:=4) (motive:=fun _=>Fin (tapes a))
    (fun j=>old a (core a j)) (fresh a) (permutation i)
theorem slots_injective : Function.Injective (slots a) := by
  have h : Function.Injective
      (Fin.addCases (m:=3) (n:=4) (motive:=fun _=>Fin (tapes a))
        (fun j=>old a (core a j)) (fresh a)) := by
    intro i j
    refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;>
      refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · intro h
      apply congrArg (fun k : Fin 3=>k.castAdd 4)
      apply core_injective a
      apply Fin.ext
      have hv:=congrArg Fin.val h
      simpa only [Fin.addCases_left,old,Fin.val_castAdd] using hv
    · intro h
      have hv:=congrArg Fin.val h
      have hi:=(core a i).isLt
      simp only [Fin.addCases_left,Fin.addCases_right,old,fresh,Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    · intro h
      have hv:=congrArg Fin.val h
      have hj:=(core a j).isLt
      simp only [Fin.addCases_left,Fin.addCases_right,old,fresh,Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    · intro h
      apply congrArg (fun k : Fin 4=>k.natAdd 3)
      apply Fin.ext
      have hv:=congrArg Fin.val h
      simpa [fresh] using hv
  exact h.comp (by decide : Function.Injective permutation)

noncomputable def first := TapeEmbedding.machine 4 (Counted.machine a)
noncomputable def last := RecoveryFocus.machine (slots a) RowCacheMass.machine
noncomputable def machine := Composition.machine (first a) (last a)
def input (r : ExactDecompositionRequest) : Fin (tapes a)→List Bool :=
  Fin.addCases (Counted.input a r) (fun _=>[])
def budget (r : ExactDecompositionRequest) :=
  Counted.budget a r+1+RowCacheMass.budget (a.output r).children

theorem source_run (request : ExactDecompositionRequest) :
    ∃ r,run (machine a) (budget a request) (input a request)=some r ∧
      r.final.tapes (sourceTape a)=exactListWord (a.output request).children ∧
      r.final.heads (sourceTape a)=0 ∧
      r.final.tapes (massTape a)=List.replicate (exactListWord (a.output request).children).length true ∧
      r.final.heads (massTape a)=0 ∧
      r.final.tapes (arityTape a)=UnaryTemplate.tape request.arity ∧ r.final.heads (arityTape a)=1 ∧
      r.final.tapes (countTape a)=UnaryTemplate.tape (a.output request).children.length ∧
      r.final.heads (countTape a)=1 ∧ r.steps≤budget a request := by
  obtain ⟨base,hb,hbs,bt,bh,bm,bmh,bn,bnh,_,_,_,_⟩ := Counted.counted_run a request
  let prepared := TapeEmbedding.receipt (fun _ : Fin 4=>0) (fun _=>[]) base
  have he := TapeEmbedding.run_embed (Counted.machine a) (fun _ : Fin 4=>0) (fun _=>[]) _ _ base hb
  rw [RepairSource.ProjectionNormalization.StreamPrepare.embed_initial] at he
  obtain ⟨mass,hm,mt,mh,mb,mbh,mn,mnh,mc,mch,ms⟩ := RowCacheMass.mass_run (a.output request).children
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config (slots a) (slots_injective a)
    RowCacheMass.machine prepared.final.heads prepared.final.tapes _ _ mass hm
  have hi : RecoveryFocus.config (slots a) prepared.final.heads prepared.final.tapes
      (RowCacheMass.input (a.output request).children)=Composition.restart prepared.final (last a).start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      all_goals simp [slots,permutation,core,selectCore,old,fresh,Entry.recordSlots,
        prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,RowCacheMass.input,
        Rewind.recording,Rewind.config,DecompositionCachedChild.entry,bh,bnh,bmh]
    · intro i
      fin_cases i
      all_goals simp [slots,permutation,core,selectCore,old,fresh,Entry.recordSlots,
        prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,RowCacheMass.input,
        Rewind.recording,Rewind.config,DecompositionCachedChild.entry,bt,bn,bm]
  rw [hi] at hf
  have hj := Composition.run_join (first a) (last a) _ _ _ prepared focused he hf
  have ht (i : Fin 7) : focused.final.tapes (slots a i)=mass.final.tapes i := by
    simp only [ff,RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a)]
  have hh (i : Fin 7) : focused.final.heads (slots a i)=mass.final.heads i := by
    simp only [ff,RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a)]
  refine ⟨Composition.joinedReceipt prepared focused,hj,(ht 0).trans mt,(hh 0).trans mh,
    (ht 5).trans mb,(hh 5).trans mbh,(ht 3).trans mn,(hh 3).trans mnh,
    (ht 4).trans mc,(hh 4).trans mch,?_⟩
  change base.steps+1+focused.steps≤_
  rw [fs,ms]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RowSourceCacheMass
