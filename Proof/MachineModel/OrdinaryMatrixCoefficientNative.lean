import Proof.MachineModel.OrdinaryMatrixCoefficientLoop

/-! Canonical coefficient extraction on the actual finite width/Gates
sentinels, including zero gates. Each cut carries `width` weights per side (the
center bits `φ(z)`), so the cut-skipping template is the unary `width`. The caller
supplies both sentinels by parsing the original request and pays one final return
after the complete pass. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientNative
open LocalBitMultitape MatrixScoreBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (r : Request) : Fin 4 → ℕ := ![0,0,0,r.Gates+2]
noncomputable def cfg (r : Request) (phase : Fin 5) (pos : ℕ) (out : List Bool) :=
  ZeroPadding.config (padding r) (RepeatMachine.cfg phase
    (MatrixCoefficientFields.cfg MatrixCoefficientGate.machine.start (word r) pos r.width out) r.Gates 1)
def budget (r : Request) := r.Gates*(MatrixCoefficientGate.budget r.width r.p+3)+3

theorem cfg_heads (r : Request) (phase : Fin 5) (pos : ℕ) (out : List Bool) :
    (cfg r phase pos out).heads=![pos,1,out.length,1] := by
  funext i; fin_cases i <;> rfl

theorem cfg_tapes (r : Request) (phase : Fin 5) (pos : ℕ) (out : List Bool) :
    (cfg r phase pos out).tapes=![word r,UnaryTemplate.tape r.width,out,UnaryTemplate.tape r.Gates] := by
  funext i
  fin_cases i <;> simp [cfg,padding,ZeroPadding.config,ZeroPadding.pad,RepeatMachine.cfg,
    controlConfig,TapeEmbedding.config,MatrixCoefficientFields.cfg,Fin.addCases,
    CompareMachine.word,UnaryTemplate.tape]

theorem all_run (r : Request) (out : List Bool) : ∃ actual,
    runFrom MatrixCoefficientLoop.machine (budget r) (cfg r 0 (header r).length out)=some actual ∧
    actual.final=cfg r 3 (word r).length (out++MatrixCoefficientLoop.output r.p r.cuts) ∧
    actual.steps≤budget r := by
  obtain ⟨base,hb,bf,bs⟩ := MatrixCoefficientLoop.loop_run r.width r.p r.cuts (header r) [] out r.Gates 0
    (by simp [Request.Gates]) r.lengths
  have hs : header r++r.cuts.flatMap (cutWord r.p)++[]=word r := by simp only [word,List.append_nil]
  have hlen : (header r).length+(r.cuts.flatMap (cutWord r.p)).length=(word r).length := by simp only [word,List.length_append]
  have hc : MatrixCoefficientLoop.budget r.width r.p r.cuts.length r.Gates=budget r := by
    unfold MatrixCoefficientLoop.budget budget Request.Gates
    ring
  rw [hs,hc] at hb
  rw [hs,hlen] at bf
  rw [hc] at bs
  obtain ⟨actual,ha,af,as,_⟩ := ZeroPadding.run_config MatrixCoefficientLoop.machine (padding r) _ _ base hb
  exact ⟨actual,ha,by rw [af,bf]; rfl,as.trans_le bs⟩

end NearCubicWires.RepairOrdinary.MatrixCoefficientNative
