import Proof.Amplification.RecoveryProjectionFieldLoop
import Proof.PCP.ProjectionNormalizationConstants

/-! A complete projected address row. The executed field loop emits every
address bit; the existing literal printer appends its actual false frame
terminator. The original physical width driver is retained for the next row. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionField
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound VerifierDecoding
open ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def closeSlots (_ : Fin 1) : Fin 35 := 31
theorem close_injective : Function.Injective closeSlots := by intro a b _; exact Subsingleton.elim _ _
noncomputable def closeMachine := RecoveryFocus.machine closeSlots (HierarchyFixedWord.raw [false])
noncomputable def queryMachine := Composition.machine loopMachine closeMachine

def queryHeads (pos outPos : Nat) (i : Fin 35) : Nat :=
  Fin.addCases (m:=34) (n:=1) (motive:=fun _=>Nat) (bodyHeads pos outPos) (fun _=>1) i
def queryInput (cap width : Nat) (source randomness tail out : List Bool) (i : Fin 35) : List Bool :=
  Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool) (bodyInput cap source randomness tail out)
    (fun _=>CompareMachine.word width) i

theorem loop_heads (phase : Fin 5) (cap width : Nat) (source randomness tail out : List Bool) (pos : Nat) :
    (loopCfg phase cap source randomness tail out pos width 1).heads=queryHeads pos out.length := rfl

theorem loop_tapes (phase : Fin 5) (cap width : Nat) (source randomness tail out : List Bool) (pos : Nat) :
    (loopCfg phase cap source randomness tail out pos width 1).tapes=queryInput cap width source randomness tail out := rfl

theorem close_run (out : List Bool) (hs : Fin 35→Nat) (data : Fin 35→List Bool)
    (hh : hs 31=out.length) (ht : data 31=out) : ∃ r,
    runFrom closeMachine 1 ⟨closeMachine.start,hs,data⟩=some r ∧
      r.final.heads=Function.update hs 31 (out++[false]).length ∧
      r.final.tapes=Function.update data 31 (out++[false]) ∧ r.steps=1 := by
  obtain ⟨base,hr,hf,bs⟩ := Constants.write_run [false] out
  obtain ⟨r,hrr,_hcontrol,rsteps,rh,rt,other⟩ := RecoveryFocus.dock closeSlots close_injective
    (HierarchyFixedWord.raw [false]) 1 hs data _
    (by intro j; fin_cases j; simpa [closeSlots,Constants.cfg] using hh)
    (by intro j; fin_cases j; simpa [closeSlots,Constants.cfg] using ht) base hr
  have localH : r.final.heads 31=(out++[false]).length := by
    have h:=rh 0
    rw [hf] at h
    simpa [closeSlots,Constants.cfg] using h
  have localT : r.final.tapes 31=out++[false] := by
    have h:=rt 0
    rw [hf] at h
    exact h
  refine ⟨r,hrr,?_,?_,rsteps.trans bs⟩
  · funext i
    by_cases hi : i=31
    · subst i; simpa using localH
    · simpa only [Function.update_of_ne hi] using (other i (by intro j; exact Ne.symm hi)).1
  · funext i
    by_cases hi : i=31
    · subst i; simpa using localT
    · simpa only [Function.update_of_ne hi] using (other i (by intro j; exact Ne.symm hi)).2

theorem query_heads_update (pos before after : Nat) :
    Function.update (queryHeads pos before) 31 after=queryHeads pos after := by
  funext i
  refine Fin.addCases (m:=34) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=31) (n:=3) (fun k=>?_) (fun k=>?_) j
    · have hn : ((k.castAdd 3).castAdd 1 : Fin 35)≠31 := by
        intro h; have hv:=congrArg Fin.val h; have hk:=k.isLt; change k.val=31 at hv; omega
      simp only [Function.update_of_ne hn,queryHeads,bodyHeads,Fin.addCases_left]
    · fin_cases k <;> rfl
  · fin_cases j; rfl

theorem query_input_update (cap width : Nat) (source randomness tail before after : List Bool) :
    Function.update (queryInput cap width source randomness tail before) 31 after=
      queryInput cap width source randomness tail after := by
  funext i
  refine Fin.addCases (m:=34) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=31) (n:=3) (fun k=>?_) (fun k=>?_) j
    · have hn : ((k.castAdd 3).castAdd 1 : Fin 35)≠31 := by
        intro h; have hv:=congrArg Fin.val h; have hk:=k.isLt; change k.val=31 at hv; omega
      simp only [Function.update_of_ne hn,queryInput,bodyInput,Fin.addCases_left]
    · fin_cases k <;> rfl
  · fin_cases j; rfl

theorem query_run (cap : Nat) (pre : List Bool) (fields : List (List Bool))
    (suffix randomness tail out : List Bool)
    (hc : ∀ bits∈fields,RecoveryProjectionEval.budget bits randomness+1 ≤ cap) : ∃ r,
    runFrom queryMachine (fields.length*(4*cap+11)+5)
      ⟨queryMachine.start,queryHeads pre.length out.length,
        queryInput cap fields.length (pre++FieldList.stream fields++suffix) randomness tail out⟩=some r ∧
      r.final.heads=queryHeads (pre.length+(FieldList.stream fields).length)
        (out++emitted fields randomness++[false]).length ∧
      r.final.tapes=queryInput cap fields.length (pre++FieldList.stream fields++suffix) randomness tail
        (out++emitted fields randomness++[false]) ∧ r.steps ≤ fields.length*(4*cap+11)+5 := by
  obtain ⟨first,hfirst,hf,fs⟩ := loop_run cap pre fields suffix randomness tail out hc
  obtain ⟨last,hlast,lh,lt,ls⟩ := close_run (out++emitted fields randomness) first.final.heads first.final.tapes
    (by rw [hf,loop_heads]; rfl) (by rw [hf,loop_tapes]; rfl)
  have hall := Composition.run_join loopMachine closeMachine _ 1 _ first last hfirst hlast
  have he : (fields.length*(4*cap+11)+3)+1+1=fields.length*(4*cap+11)+5 := by omega
  rw [he] at hall
  refine ⟨_,hall,?_,?_,?_⟩
  · change last.final.heads=_
    rw [lh,hf,loop_heads,query_heads_update]
  · change last.final.tapes=_
    rw [lt,hf,loop_tapes,query_input_update]
  · change first.steps+1+last.steps ≤ _
    omega

end NearCubicWires.RepairSource.RecoveryProjectionField
