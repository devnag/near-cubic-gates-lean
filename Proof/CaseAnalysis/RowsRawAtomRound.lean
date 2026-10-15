import Proof.Supplier.RowMaskBody
import Proof.MachineModel.Encoding

/-! One actual exact-child occurrence emits its absolute index in the
existing incidence stream. The original index copier/incrementer advances
the retained offset and count; only the two monomial delimiters are added. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomRound
open LocalBitMultitape RecoveryExecution RowMaskBodyParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mark (b : Bool) : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q=0 then some
    ⟨1,![none,none,some b,none],![.stay,.stay,.right,.stay]⟩ else none

theorem mark_run (b : Bool) (source : List Bool) (pos j count : ℕ) (out : List Bool) :
    ∃ r,runFrom (mark b) 1 (cfg 0 source pos j count out)=some r ∧
      r.final=cfg 1 source pos j count (out++[b]) ∧ r.steps=1 := by
  have h : step (mark b) (cfg 0 source pos j count out)=
      some (cfg 1 source pos j count (out++[b])) := by
    simp only [step,mark,cfg,↓reduceIte]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]
  exact (Timed.single (by rfl) h).run (by rfl)

noncomputable def first:=Composition.machine (mark true) RowMaskBody.machine
noncomputable def machine:=Composition.machine first (mark false)
def budget (index : ℕ):=4*index+26

theorem round_run (pre tail out : List Bool) (index count : ℕ) :
    ∃ r,runFrom machine (budget index)
      (cfg machine.start (pre++true::tail) pre.length (index+1) count out)=some r ∧
      r.final.heads=(cfg machine.start (pre++true::tail) (pre.length+1) (index+2) (count+1)
        (out++ExtIncidence.monomialWord [index])).heads ∧
      r.final.tapes=(cfg machine.start (pre++true::tail) (pre.length+1) (index+2) (count+1)
        (out++ExtIncidence.monomialWord [index])).tapes ∧ r.steps≤budget index := by
  obtain ⟨a,ha,af,asteps⟩:=mark_run true (pre++true::tail) pre.length (index+1) count out
  obtain ⟨b,hb,bh,bt,bs⟩:=RowMaskBody.body_run pre tail true (index+1) count (out++[true])
  have hi : Composition.restart a.final RowMaskBody.machine.start=
      cfg RowMaskBody.machine.start (pre++true::tail) pre.length (index+1) count (out++[true]) := by
    rw [af];rfl
  rw [←hi] at hb
  have hab:=Composition.run_join (mark true) RowMaskBody.machine _ _ _ a b ha hb
  let ab:=Composition.joinedReceipt a b
  let mid:=(out++[true])++RowIndexField.word (index+1)
  have bh' : b.final.heads=(cfg RowMaskBody.machine.start (pre++true::tail) (pre.length+1)
      (index+2) (count+1) mid).heads := by
    simpa only [RowMaskBody.emitted,ite_true,Bool.toNat_true,Nat.add_assoc] using bh
  have bt' : b.final.tapes=(cfg RowMaskBody.machine.start (pre++true::tail) (pre.length+1)
      (index+2) (count+1) mid).tapes := by
    simpa only [RowMaskBody.emitted,ite_true,Bool.toNat_true,Nat.add_assoc] using bt
  obtain ⟨c,hc,cf,cs⟩:=mark_run false (pre++true::tail) (pre.length+1) (index+2) (count+1) mid
  have hj : Composition.restart ab.final (mark false).start=
      cfg 0 (pre++true::tail) (pre.length+1) (index+2) (count+1) mid := by
    apply configuration_ext
    · rfl
    · exact bh'
    · exact bt'
  rw [←hj] at hc
  have whole:=Composition.run_join first (mark false) _ _ _ ab c hab hc
  have htime : 1+1+(4*(index+1)+18)+1+1=budget index := by unfold budget;omega
  rw [htime] at whole
  have hout : mid++[false]=out++ExtIncidence.monomialWord [index] := by
    simp [mid,ExtIncidence.monomialWord,ExtIncidence.block,RowIndexField.word,List.append_assoc]
  refine ⟨Composition.joinedReceipt ab c,whole,?_,?_,?_⟩
  · change c.final.heads=_
    rw [cf,hout]
    rfl
  · change c.final.tapes=_
    rw [cf,hout]
    rfl
  · change (a.steps+1+b.steps)+1+c.steps≤_
    rw [asteps,cs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomRound
