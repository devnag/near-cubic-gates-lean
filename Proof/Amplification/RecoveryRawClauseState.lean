import Proof.Amplification.RecoveryRawLiteralLoopReturn

/-! The raw clause controller runs the supplied number of literals, then
executes one more actual cell test and negates its presence bit. Missing
cells in the loop stop with false; an unconsumed tail also returns false. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawClause
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RecoveryRawLiteralBound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private def states {t s : Nat} (_ : Machine t s) := s
noncomputable abbrev bodyStates := states RecoveryRawLiteralBound.machine
noncomputable abbrev loopStates := states RecoveryRawLiteralLoop.machine

def cfg {s : Nat} (x : State) (total : Nat) (q : Fin s) : Configuration 36 s :=
  TapeEmbedding.config (fun _ : Fin 1=>1) (fun _=>CompareMachine.word total) (x.cfg q)
def inverted (x : State) : State :=
  {x with stream:={x.stream with data:={x.stream.data with present:=!x.stream.data.present}}}
def invertMachine : Machine 36 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then
    some ⟨1,fun i=>if i=28 then some (!scanned 28) else none,fun _=>.stay⟩ else none
noncomputable def tailMachine := TapeEmbedding.machine 1 RecoveryRawLiteralBound.machine

noncomputable def sizes : Fin 3→Nat := ![loopStates,bodyStates,2]
noncomputable def programs : (j : Fin 3)→Machine 36 (sizes j)
  | ⟨0,_⟩=>RecoveryRawLiteralLoop.machine
  | ⟨1,_⟩=>tailMachine
  | ⟨2,_⟩=>invertMachine
  | ⟨n+3,h⟩=>False.elim (by omega)
noncomputable def next : (j : Fin 3)→Fin (sizes j)→(Fin 36→Bool)→Option (Fin 3)
  | ⟨0,_⟩,q,_=>if q=RepeatMachine.phaseCode bodyStates 3 then some 1 else none
  | ⟨1,_⟩,_,_=>some 2
  | ⟨2,_⟩,_,_=>none
  | ⟨n+3,h⟩,_,_=>False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def budget (width total : Nat) := RecoveryRawLiteralLoop.budget width total+
  RecoveryRawLiteralLoop.bodyBudget width+4
def out (total : Nat) (x : State) := RepeatMachine.iterate RecoveryRawLiteralLoop.next total x
def answer (total : Nat) (x : State) := (out total x).1 && decide (code (out total x).2=0)

theorem invert_run (x : State) (total : Nat) :
    ∃ r,runFrom invertMachine 1 (cfg x total invertMachine.start)=some r ∧
      r.final=cfg (inverted x) total 1 ∧ r.steps=1 := by
  have h : step invertMachine (cfg x total 0)=some (cfg (inverted x) total 1) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem tail_run (x : State) (total : Nat) (hx : x.Valid) :
    ∃ r,runFrom tailMachine (cost x) (cfg x total tailMachine.start)=some r ∧
      r.final=cfg (output x) total r.final.control ∧ r.steps ≤ cost x := by
  have hrun := RecoveryRawLiteralBound.body_run x hx
  obtain ⟨base,hr,hf,hb⟩ := hrun
  have h := TapeEmbedding.run_embed RecoveryRawLiteralBound.machine (fun _ : Fin 1=>1)
    (fun _=>CompareMachine.word total) (cost x) _ base hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>1) (fun _=>CompareMachine.word total) base,h,?_,hb⟩
  change TapeEmbedding.config _ _ base.final=_
  rw [hf]
  rfl

theorem out_inv (width total : Nat) (x : State) (hx : RecoveryRawLiteralLoop.Inv width x) :
    RecoveryRawLiteralLoop.Inv width (out total x).2 := by
  induction total generalizing x with
  | zero=>exact hx
  | succ total ih=>
    have hy : RecoveryRawLiteralLoop.Inv width (output x) :=
      ⟨output_valid x hx.1,(output_width x).trans hx.2⟩
    unfold out RepeatMachine.iterate
    split
    · exact ih (output x) hy
    · exact hy

end NearCubicWires.RepairOrdinary.RecoveryRawClause
