import Proof.MachineModel.OrdinaryMatrixBatchGateLoop

/-! The canonical all-gates run uses the actual sentinel produced by the
raw header parser, including its finite final false cell. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchGateNativeLoop
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open RepairSource.VerifierDecoding
open MatrixBatchGateStore (Store data)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (r : Request) (i : Fin 49) := if i=48 then r.Gates+2 else 0
noncomputable def cfg (r : Request) (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (out : List Bool) (s : Store r) :=
  ZeroPadding.config (padding r) (RepeatMachine.cfg phase (data r source pos out s) r.Gates 1)
noncomputable def output (r : Request) := MatrixBatchGateLoop.packets r (List.finRange r.Gates)
def budget (r : Request) := r.Gates*(MatrixBatchGateStore.budget r+3)+3
def cold (r : Request) : Store r := ⟨0,0,0,fun _ => [],by intro i; simp⟩

theorem all_cuts (r : Request) :
    MatrixBatchGateLoop.cuts r (List.finRange r.Gates)=r.cuts.flatMap (cutWord r.p) := by
  have h := congrArg (List.flatMap (cutWord r.p)) (List.map_get_finRange r.cuts)
  simpa only [MatrixBatchGateLoop.cuts,Request.Gates,List.flatMap_map,Function.comp_def] using h

theorem cfg_heads (r : Request) (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (out : List Bool) (s : Store r) :
    (cfg r phase source pos out s).heads=
      Fin.addCases (m := 48) (n := 1) (motive := fun _ => ℕ)
        (MatrixBatchGateClear.heads pos out.length) (fun _ => 1) := rfl

theorem cfg_tapes (r : Request) (phase : Fin 5) (source : List Bool) (pos : ℕ)
    (out : List Bool) (s : Store r) :
    (cfg r phase source pos out s).tapes=
      Fin.addCases (m := 48) (n := 1) (motive := fun _ => List Bool)
        (MatrixBatchGateClear.tapes r s.assignment s.id s.cap source out s.backing)
        (fun _ => UnaryTemplate.tape r.Gates) := by
  funext i
  refine Fin.addCases (m := 48) (n := 1) (motive := fun j => (cfg r phase source pos out s).tapes j=_) ?_ ?_ i
  · intro j
    have hj : (j.castAdd 1 : Fin 49)≠48 := by
      intro h
      have hh := congrArg Fin.val h
      change j.val=48 at hh
      omega
    simp [cfg,ZeroPadding.config,padding,hj,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      data,RecoveryCalls.restarted,ZeroPadding.pad]
  · intro j
    fin_cases j
    change ZeroPadding.pad (r.Gates+2) (CompareMachine.word r.Gates)=UnaryTemplate.tape r.Gates
    simp [CompareMachine.word,ZeroPadding.pad,UnaryTemplate.tape]

theorem all_run (r : Request) (s : Store r) (out : List Bool) :
    ∃ final : Store r,∃ actual,
      runFrom MatrixBatchGateLoop.machine (budget r) (cfg r 0 (word r) (header r).length out s)=some actual ∧
      actual.final=cfg r 3 (word r) (word r).length (out++output r) final ∧
      actual.steps≤budget r := by
  obtain ⟨final,base,hb,hbf,hbs⟩ := MatrixBatchGateLoop.loop_run r (List.finRange r.Gates)
    (header r) [] out s r.Gates 0 (by simp)
  have hword : header r++MatrixBatchGateLoop.cuts r (List.finRange r.Gates)++[]=word r := by
    rw [all_cuts,List.append_nil]
    rfl
  have hlength : (header r).length+(MatrixBatchGateLoop.cuts r (List.finRange r.Gates)).length=(word r).length := by
    rw [←hword,List.length_append,List.length_nil,Nat.add_zero,List.length_append]
  have hbudget : MatrixBatchGateLoop.budget r (List.finRange r.Gates).length r.Gates=budget r := by
    simp only [MatrixBatchGateLoop.budget,List.length_finRange,budget]
    ring
  rw [hword,hbudget] at hb
  rw [hword,hlength] at hbf
  rw [hbudget] at hbs
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config MatrixBatchGateLoop.machine (padding r) _ _ base hb
  refine ⟨final,actual,ha,?_,hs.trans_le hbs⟩
  rw [hf,hbf]
  rfl

end NearCubicWires.RepairOrdinary.MatrixBatchGateNativeLoop
