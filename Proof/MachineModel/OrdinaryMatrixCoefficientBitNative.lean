import Proof.MachineModel.OrdinaryMatrixCoefficientBitLoop

/-! The actual finite Gates-sentinel pass over the retained canonical
coefficient bank. It emits every gate's raw sign/bit predicate in order;
its enclosing caller still pays both sentinel placement and the return. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientBitNative
open LocalBitMultitape MatrixScoreBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficients (r : Request) := r.cuts.map Cut.coefficient
def output (r : Request) (negative : Bool) (t : ℕ) := MatrixCoefficientBitLoop.output negative t (coefficients r)
def padding (r : Request) : Fin 5 → ℕ := ![0,0,0,0,r.Gates+2]
noncomputable def cfg (r : Request) (negative flag : Bool) (t : ℕ) (phase : Fin 5) (pos : ℕ) (out : List Bool) :=
  ZeroPadding.config (padding r) (RepeatMachine.cfg phase
    (MatrixCoefficientBitLeaf.cfg (MatrixCoefficientBitBody.machine negative).start
      (MatrixCoefficientLoop.output r.p r.cuts) pos (2*t) flag out) r.Gates 1)
def budget (r : Request) := r.Gates*(4*r.p+15)+3

theorem cfg_heads (r : Request) (negative flag : Bool) (t : ℕ) (phase : Fin 5) (pos : ℕ) (out : List Bool) :
    (cfg r negative flag t phase pos out).heads=![pos,1,0,out.length,1] := by
  funext i; fin_cases i <;> rfl

theorem cfg_tapes (r : Request) (negative flag : Bool) (t : ℕ) (phase : Fin 5) (pos : ℕ) (out : List Bool) :
    (cfg r negative flag t phase pos out).tapes=
      ![MatrixCoefficientLoop.output r.p r.cuts,UnaryTemplate.tape (2*t),[flag],out,UnaryTemplate.tape r.Gates] := by
  funext i
  fin_cases i <;> simp [cfg,padding,ZeroPadding.config,ZeroPadding.pad,RepeatMachine.cfg,controlConfig,
    TapeEmbedding.config,MatrixCoefficientBitLeaf.cfg,Fin.addCases,CompareMachine.word,UnaryTemplate.tape]

theorem all_run (r : Request) (negative flag : Bool) (t : ℕ) (ht : t<r.p) (out : List Bool) : ∃ actual,
    runFrom (MatrixCoefficientBitLoop.machine negative) (budget r) (cfg r negative flag t 0 0 out)=some actual ∧
    actual.final=cfg r negative (MatrixCoefficientBitLoop.finalFlag negative flag (coefficients r)) t 3
      (MatrixCoefficientLoop.output r.p r.cuts).length (out++output r negative t) ∧ actual.steps≤budget r := by
  have hc : 0+(coefficients r).length=r.Gates := by simp [coefficients,Request.Gates]
  obtain ⟨base,hb,bf,bs⟩ := MatrixCoefficientBitLoop.loop_run negative flag r.p t ht (coefficients r) [] [] out r.Gates 0 hc
  have hsource : []++MatrixScoreCanonical.fields r.p (coefficients r)++[]=MatrixCoefficientLoop.output r.p r.cuts := by
    simp [MatrixScoreCanonical.fields,coefficients,MatrixCoefficientLoop.output,List.flatMap_map]
  have hbudget : MatrixCoefficientBitLoop.budget r.p (coefficients r).length r.Gates=budget r := by
    unfold MatrixCoefficientBitLoop.budget MatrixCoefficientBitCanonical.budget budget coefficients Request.Gates
    simp only [List.length_map]
    ring
  have hlen : ([] : List Bool).length+(MatrixScoreCanonical.fields r.p (coefficients r)).length=
      (MatrixCoefficientLoop.output r.p r.cuts).length := by simpa using congrArg List.length hsource
  rw [hsource,hbudget] at hb
  rw [hsource,hlen] at bf
  rw [hbudget] at bs
  obtain ⟨actual,ha,af,as,_⟩ := ZeroPadding.run_config (MatrixCoefficientBitLoop.machine negative) (padding r) _ _ base hb
  exact ⟨actual,ha,by rw [af,bf]; rfl,as.trans_le bs⟩

end NearCubicWires.RepairOrdinary.MatrixCoefficientBitNative
