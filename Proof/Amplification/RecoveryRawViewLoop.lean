import Proof.Amplification.RecoveryRawViewBodyBudget

/-! Actual outer raw-view iteration. Its ghost cursor records precisely
the physical witness position; the retained source and every literal scan
are charged by the same verified body. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawViewLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawView
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Cursor where
  data : State
  pos : Nat

def nextPos (word : List Bool) (x : Cursor) :=
  match readCount x.data.limit (word.drop x.pos) with
  | none=>x.pos
  | some (n,_)=>x.pos+n+1+2*n*x.data.width
def next (word : List Bool) (x : Cursor) : Bool×Cursor :=
  (RecoveryRawViewBody.answer x.data word x.pos,
    ⟨RecoveryRawViewBody.bodyOutput x.data word x.pos,nextPos word x⟩)
noncomputable def source (x : Cursor) := x.data.cfg RecoveryRawViewBody.machine.start
noncomputable def machine := RepeatMachine.machine RecoveryRawViewBody.machine (fun _ scanned=>scanned 28)
def Inv (width : Nat) (word : List Bool) (x : Cursor) : Prop :=
  x.data.Valid ∧ x.data.width=width ∧ x.data.inner.stream.source=frame word ∧ x.data.inner.stream.pos=2*x.pos
def bodyBudget (width : Nat) := 33554432*(width+1)^3
def budget (width total : Nat) := total*(bodyBudget width+3)+3

theorem next_inv (width : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x)
    (ha : (next word x).1=true) : Inv width word (next word x).2 := by
  have hv := RecoveryRawViewBody.accepted_invariant x.data word x.pos hx.1 ha
  refine ⟨hv.1,hv.2.1.trans hx.2.1,hv.2.2.2.2.trans hx.2.2.1,?_⟩
  obtain ⟨_,n,rest,hp,hcheck⟩ := RecoveryRawViewBody.accepted x.data word x.pos ha
  change (RecoveryRawViewBody.bodyOutput x.data word x.pos).inner.stream.pos=2*nextPos word x
  rw [RecoveryRawViewBody.body_output_some x.data word x.pos n rest hp,
    RecoveryRawViewBody.output_pos x.data hx.1 n hcheck]
  unfold nextPos
  rw [hp,hx.2.2.2]
  ring

theorem supplier (width : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x) :
    ∃ r,runFrom RecoveryRawViewBody.machine (bodyBudget width) (source x)=some r ∧
      r.steps ≤ bodyBudget width ∧ r.final.scanned 28=(next word x).1 ∧
      ((next word x).1=true → r.final.heads=(source (next word x).2).heads ∧
        r.final.tapes=(source (next word x).2).tapes ∧ Inv width word (next word x).2) ∧
      ((next word x).1=false → r.final.heads 28=0 ∧ r.final.tapes 28=[false]) := by
  have hrun := RecoveryRawViewBody.body_run x.data word x.pos hx.1 hx.2.2.1 hx.2.2.2
  obtain ⟨r,hr,hb,hh,ht,hf⟩ := hrun
  have hc : RecoveryRawViewBody.budget x.data ≤ bodyBudget width := by
    have h := RecoveryRawViewBody.budget_bound x.data hx.1
    rw [hx.2.1] at h
    exact h
  have hm := runFrom_moreFuel RecoveryRawViewBody.machine (RecoveryRawViewBody.budget x.data)
    (bodyBudget width-RecoveryRawViewBody.budget x.data) _ r hr
  rw [Nat.add_sub_of_le hc] at hm
  refine ⟨r,hm,hb.trans hc,?_,?_,?_⟩
  · change readTapeBit (r.final.tapes 28) (r.final.heads 28)=_
    rw [hh,ht]
    rfl
  · intro ha
    refine ⟨?_,?_,next_inv width word x hx ha⟩
    · rw [hf ha]; rfl
    · rw [hf ha]; rfl
  · intro ha
    exact ⟨hh,ht.trans (congrArg (fun bit : Bool=>[bit]) ha)⟩

theorem loop_run (width total : Nat) (word : List Bool) (x : Cursor) (hx : Inv width word x) :
    ∃ r,runFrom machine (budget width total) (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps ≤ budget width total ∧
      RepeatMachine.Result source total (RepeatMachine.iterate (next word) total x) r.final ∧
      ((RepeatMachine.iterate (next word) total x).1=false →
        r.final.heads 28=0 ∧ r.final.tapes 28=[false]) := by
  exact RepeatMachine.rejecting_repeat_tape RecoveryRawViewBody.machine (fun _ scanned=>scanned 28)
    source (next word) (Inv width word) (bodyBudget width) 28 (fun _ _=>rfl) (supplier width word) total x hx

theorem budget_bound (width total : Nat) (h : total ≤ 3*(width+1)) :
    budget width total ≤ 134217728*(width+1)^4 := by
  have hlinear : width+1 ≤ (width+1)^4 := by
    nlinarith [Nat.zero_le (width^4),Nat.zero_le (width^3),sq_nonneg (width : Nat)]
  unfold budget bodyBudget
  calc
    _ ≤ 3*(width+1)*(33554432*(width+1)^3+3)+3 := by gcongr
    _ ≤ _ := by nlinarith [show 0<(width+1)^4 by positivity]

end NearCubicWires.RepairOrdinary.RecoveryRawViewLoop
