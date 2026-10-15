import Proof.MachineModel.OrdinaryMatrixRankFieldReverse

/-! The supplied U sentinel executes exactly U backwards ranked-field
scans. Its cursor is physically restored to head1 after each row pass. -/
namespace NearCubicWires.RepairOrdinary.MatrixRankRowReverse
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted (_ : Fin 7) (_ : Fin 2 → Bool) := true
noncomputable def machine := RepeatMachine.machine MatrixRankFieldReverse.machine accepted
def budget (H U : ℕ) := U*(MatrixRankFieldReverse.budget H+3)+3
noncomputable def cfg (phase : Fin 5) (source : List Bool) (H U pos : ℕ) :=
  ZeroPadding.config (![0,0,U+2] : Fin 3 → ℕ)
    (RepeatMachine.cfg phase (MatrixRankFieldReverse.cfg 0 source H pos 0) U 1)

theorem iterate_sub (distance count pos : ℕ) :
    RepeatMachine.iterate (fun p : ℕ => (true,p-distance)) count pos=
      (true,pos-count*distance) := by
  induction count generalizing pos with
  | zero => simp [RepeatMachine.iterate]
  | succ count ih =>
    simpa [RepeatMachine.iterate,Nat.sub_sub,Nat.succ_mul,Nat.add_comm] using ih (pos-distance)

theorem row_run (source : List Bool) (H U pos : ℕ) :
    ∃ actual,runFrom machine (budget H U) (cfg 0 source H U pos)=some actual ∧
      actual.steps ≤ budget H U ∧
      actual.final=cfg 3 source H U (pos-U*MatrixRankFieldReverse.distance H) := by
  let state := fun p => MatrixRankFieldReverse.cfg 0 source H p 0
  let next := fun p : ℕ => (true,p-MatrixRankFieldReverse.distance H)
  obtain ⟨base,hb,hs,hf⟩ := RepeatMachine.repeat_run MatrixRankFieldReverse.machine accepted
    state next (fun _ => True) (MatrixRankFieldReverse.budget H) (by intros; rfl)
    (by
      intro p _
      obtain ⟨actual,ha,haf,has⟩ := MatrixRankFieldReverse.reverse_run source H p
      refine ⟨actual,ha,has.le,?_,?_,rfl,by intros; trivial⟩
      · rw [haf]; rfl
      · rw [haf]; rfl) U pos trivial
  have hfinal : base.final=RepeatMachine.cfg 3
      (state (pos-U*MatrixRankFieldReverse.distance H)) U 1 := by
    simpa only [RepeatMachine.Result,next,iterate_sub,↓reduceIte] using hf
  obtain ⟨actual,ha,haf,has,_⟩ := ZeroPadding.run_config machine (![0,0,U+2] : Fin 3 → ℕ) _ _ base hb
  refine ⟨actual,ha,has.trans_le hs,?_⟩
  rw [haf,hfinal]
  rfl

theorem cfg_heads (phase : Fin 5) (source : List Bool) (H U pos : ℕ) :
    (cfg phase source H U pos).heads=![pos,0,1] := by
  funext i
  fin_cases i <;> rfl

theorem cfg_tapes (phase : Fin 5) (source : List Bool) (H U pos : ℕ) :
    (cfg phase source H U pos).tapes=![source,UnaryTemplate.tape H,UnaryTemplate.tape U] := by
  funext i
  fin_cases i <;> simp [cfg,ZeroPadding.config,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    MatrixRankFieldReverse.cfg,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape,Fin.addCases]

end NearCubicWires.RepairOrdinary.MatrixRankRowReverse
