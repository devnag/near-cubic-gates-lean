import Proof.Amplification.RecoveryProjectionFieldTail

/-! One complete reusable normalized source-field iteration. It executes
both copies, the original-code evaluator, both output writes, and the whole
scratch sweep. The exact same physical bank is ready for the next field. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionField
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bodyFirst := TapeEmbedding.machine 3 fieldMachine
noncomputable def bodyMachine := Composition.machine bodyFirst tailMachine
def bodyHeads (pos outPos : Nat) (i : Fin 34) : Nat :=
  Fin.addCases (m:=31) (n:=3) (motive:=fun _=>Nat) (heads pos) ![outPos,0,0] i
def bodyInput (cap : Nat) (source randomness tail out : List Bool) (i : Fin 34) : List Bool :=
  Fin.addCases (m:=31) (n:=3) (motive:=fun _=>List Bool) (input cap source randomness tail)
    ![out,List.replicate cap true,List.replicate (cap+1) false] i
def bodyBudget (cap : Nat) := 4*cap+8

theorem body_budget (cap : Nat) (bits randomness : List Bool)
    (hc : RecoveryProjectionEval.budget bits randomness+1 ≤ cap) :
    fieldBudget bits randomness+1+(2*cap+7) ≤ bodyBudget cap := by
  have hsize : bits.length+randomness.length+1 ≤ (bits.length+randomness.length+1)^2 :=
    Nat.le_self_pow (by decide) _
  have hpos : 1 ≤ (bits.length+randomness.length+1)^2 := Nat.one_le_pow _ _ (by omega)
  simp only [fieldBudget,RecoveryProjectionEval.budget,bodyBudget] at *
  nlinarith

theorem append_body_heads (pos before after : Nat) :
    appendHeads (bodyHeads pos before) after=bodyHeads pos after := by
  funext i
  refine Fin.addCases (m:=31) (n:=3) (fun j=>?_) (fun j=>?_) i
  · have hn : (j.castAdd 3 : Fin 34)≠31 := by
      intro h; have hv:=congrArg Fin.val h; have hj:=j.isLt; change j.val=31 at hv; omega
    simp only [appendHeads,hn,ite_false,bodyHeads,Fin.addCases_left]
  · fin_cases j <;> rfl

theorem body_run (cap : Nat) (pre bits suffix randomness tail out : List Bool)
    (hc : RecoveryProjectionEval.budget bits randomness+1 ≤ cap) : ∃ r,
    runFrom bodyMachine (bodyBudget cap)
      ⟨bodyMachine.start,bodyHeads pre.length out.length,
        bodyInput cap (pre++RepairOrdinary.frame bits++suffix) randomness tail out⟩=some r ∧
      r.final.heads=bodyHeads (pre.length+2*bits.length+1)
        (out++[true,RecoveryProjectionEval.outputBit bits randomness]).length ∧
      r.final.tapes=bodyInput cap (pre++RepairOrdinary.frame bits++suffix) randomness tail
        (out++[true,RecoveryProjectionEval.outputBit bits randomness]) ∧ r.steps ≤ bodyBudget cap := by
  obtain ⟨base,hbase,bh,bit,bank,b28,b29,b30,bs⟩ := field_run cap pre bits suffix randomness tail hc
  let eheads : Fin 3→Nat := ![out.length,0,0]
  let etapes : Fin 3→List Bool := ![out,List.replicate cap true,List.replicate (cap+1) false]
  let first := TapeEmbedding.receipt eheads etapes base
  have hfirst := TapeEmbedding.run_embed fieldMachine eheads etapes _ _ base hbase
  have oldH (i : Fin 31) : first.final.heads (i.castAdd 3)=heads (pre.length+2*bits.length+1) i := by
    simp only [first,TapeEmbedding.receipt_heads_old,bh]
  have oldT (i : Fin 31) : first.final.tapes (i.castAdd 3)=base.final.tapes i := by
    simp only [first,TapeEmbedding.receipt_tapes_old]
  have fh : first.final.heads=bodyHeads (pre.length+2*bits.length+1) out.length := by
    funext i
    refine Fin.addCases (m:=31) (n:=3) (fun j=>?_) (fun j=>?_) i
    · simpa only [bodyHeads,Fin.addCases_left] using oldH j
    · simp only [first,TapeEmbedding.receipt_heads_new,bodyHeads,Fin.addCases_right,eheads]
  have fb : ∀ j,(first.final.tapes (bankSlots j)).length ≤ cap := by
    intro j
    change (first.final.tapes ((nativeSlots j).castAdd 3)).length ≤ cap
    rw [oldT]; exact bank j
  have fbh : ∀ j,first.final.heads (bankSlots j)=0 := by
    intro j
    change first.final.heads ((nativeSlots j).castAdd 3)=0
    rw [oldH]
    have hn : nativeSlots j≠28 := by intro h; have hv:=congrArg Fin.val h; have hj:=native_small j; omega
    simp only [heads,hn,ite_false]
  obtain ⟨last,hlast,lh,lb,l28,l29,l30,l31,l32,l33,ls⟩ := tail_run cap (cap+1)
    (RecoveryProjectionEval.outputBit bits randomness) out first.final.heads first.final.tapes fb fbh
    ((oldT 26).trans bit) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  have hall := Composition.run_join bodyFirst tailMachine _ _ _ first last hfirst hlast
  have hbound := body_budget cap bits randomness hc
  have hmore := runFrom_moreFuel bodyMachine (fieldBudget bits randomness+1+(2*cap+7))
    (bodyBudget cap-(fieldBudget bits randomness+1+(2*cap+7))) _ _ hall
  rw [Nat.add_sub_of_le hbound] at hmore
  refine ⟨_,hmore,?_,?_,?_⟩
  · change last.final.heads=_
    rw [lh,fh,append_body_heads]
  · change last.final.tapes=_
    funext i
    refine Fin.addCases (m:=31) (n:=3) (fun j=>?_) (fun j=>?_) i
    · by_cases hj : j.val<28
      · let k : Fin 28 := ⟨j.val,hj⟩
        have he : bankSlots k=j.castAdd 3 := Fin.ext rfl
        have h28 : j≠28 := by intro h; subst j; contradiction
        have h29 : j≠29 := by intro h; subst j; contradiction
        have ht : last.final.tapes (j.castAdd 3)=List.replicate cap false := by rw [←he]; exact lb k
        simpa only [bodyInput,Fin.addCases_left,input,h28,h29,ite_false] using ht
      · have hv : j.val=28 ∨ j.val=29 ∨ j.val=30 := by have htop:=j.isLt; omega
        rcases hv with hv|hv|hv
        · have he : j=28 := Fin.ext hv
          subst j
          exact l28.trans ((oldT 28).trans b28)
        · have he : j=29 := Fin.ext hv
          subst j
          exact l29.trans ((oldT 29).trans b29)
        · have he : j=30 := Fin.ext hv
          subst j
          exact l30.trans ((oldT 30).trans b30)
    · fin_cases j
      · exact l31
      · exact l32
      · change last.final.tapes 33=List.replicate (cap+1) false
        simpa only [max_self] using l33
  · change base.steps+1+last.steps ≤ bodyBudget cap
    omega

end NearCubicWires.RepairSource.RecoveryProjectionField
