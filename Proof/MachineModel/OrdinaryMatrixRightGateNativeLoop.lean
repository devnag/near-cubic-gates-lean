import Proof.MachineModel.OrdinaryMatrixRightGateLoop

/-! Canonical all-gate bucket execution uses the actual finite Gates
sentinel, including its zero-gate branch, and consumes the original ordered
rank-packet stream. Its caller still pays the cold mask/cursor bootstrap. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightGateNativeLoop
open LocalBitMultitape MatrixScoreBatch MatrixRightGateLoop
open MatrixBucketGateLoop (Store)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (r : Request) (i : Fin 38) := if i=37 then r.Gates+2 else 0
noncomputable def cfg (r : Request) (phase : Fin 5) (done : ℕ) (source : List Bool) (pos : ℕ)
    (out : List Bool) (unused : Fin 3 → List Bool) (s : Store r) :=
  ZeroPadding.config (padding r) (RepeatMachine.cfg phase (data r done source pos out unused s) r.Gates 1)
noncomputable def output (r : Request) := MatrixRightGateLoop.output r (List.finRange r.Gates)
def budget (r : Request) := r.Gates*(MatrixRightGateBody.budget r+3)+3

theorem cfg_heads (r : Request) (phase : Fin 5) (done : ℕ) (source : List Bool) (pos : ℕ)
    (out : List Bool) (unused : Fin 3 → List Bool) (s : Store r) :
    (cfg r phase done source pos out unused s).heads=
      Fin.addCases (m := 37) (n := 1) (motive := fun _ => ℕ)
        (MatrixRightGateLayout.heads out.length pos) (fun _ => 1) := rfl

theorem cfg_tapes (r : Request) (phase : Fin 5) (done : ℕ) (source : List Bool) (pos : ℕ)
    (out : List Bool) (unused : Fin 3 → List Bool) (s : Store r) :
    (cfg r phase done source pos out unused s).tapes=
      Fin.addCases (m := 37) (n := 1) (motive := fun _ => List Bool)
        (MatrixRightGateLayout.data r (state r done out s) s.packet unused source) (fun _ => UnaryTemplate.tape r.Gates) := by
  funext i
  refine Fin.addCases (m := 37) (n := 1) (motive := fun j => (cfg r phase done source pos out unused s).tapes j=_) ?_ ?_ i
  · intro j
    have hj : (j.castAdd 1 : Fin 38)≠37 := by
      intro h
      have hh := congrArg Fin.val h
      change j.val=37 at hh
      omega
    simp [cfg,ZeroPadding.config,padding,hj,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      data,MatrixRightGateLayout.cfg,ZeroPadding.pad]
  · intro j
    fin_cases j
    change ZeroPadding.pad (r.Gates+2) (CompareMachine.word r.Gates)=UnaryTemplate.tape r.Gates
    simp [CompareMachine.word,ZeroPadding.pad,UnaryTemplate.tape]

theorem all_run (r : Request) (s : Store r) (out : List Bool) (unused : Fin 3 → List Bool) :
    ∃ final : Store r,∃ actual,
      runFrom MatrixRightGateLoop.machine (budget r)
        (cfg r 0 0 (MatrixBatchGateNativeLoop.output r) 0 out unused s)=some actual ∧
      actual.final=cfg r 3 r.Gates (MatrixBatchGateNativeLoop.output r) (MatrixBatchGateNativeLoop.output r).length
        (out++output r) unused final ∧ actual.steps≤budget r := by
  have hseq : (List.finRange r.Gates).map Fin.val=List.range' 0 (List.finRange r.Gates).length := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  obtain ⟨final,base,hb,bf,bs⟩ := MatrixRightGateLoop.loop_run r (List.finRange r.Gates)
    [] [] out unused s r.Gates 0 (by simp) hseq
  have hsource : []++packets r (List.finRange r.Gates)++[]=MatrixBatchGateNativeLoop.output r := by
    simp only [List.nil_append,List.append_nil]
    rfl
  have hbudget : MatrixRightGateLoop.budget r (List.finRange r.Gates).length r.Gates=budget r := by
    simp only [MatrixRightGateLoop.budget,List.length_finRange,budget]
    ring
  rw [hsource,hbudget] at hb
  rw [hbudget] at bs
  have hpos : ([] : List Bool).length+(packets r (List.finRange r.Gates)).length=(MatrixBatchGateNativeLoop.output r).length := by
    simp only [List.length_nil,Nat.zero_add]
    rfl
  rw [hsource,hpos] at bf
  obtain ⟨actual,ha,hf,hs,_⟩ := ZeroPadding.run_config MatrixRightGateLoop.machine (padding r) _ _ base hb
  refine ⟨final,actual,ha,?_,hs.trans_le bs⟩
  rw [hf,bf]
  rfl

end NearCubicWires.RepairOrdinary.MatrixRightGateNativeLoop
