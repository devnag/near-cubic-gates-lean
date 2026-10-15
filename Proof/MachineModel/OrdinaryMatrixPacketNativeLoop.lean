import Proof.MachineModel.OrdinaryMatrixPacketFirstBit
import Proof.MachineModel.OrdinaryMatrixPacketLoop

/-! The checked p loop consumes the actual terminal-false unary header
driver. Its extra final zero is observed by the same finite controller. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketNativeLoop
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open RepairSource.VerifierDecoding
open MatrixPacketState (State)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding {t : ℕ} (n : ℕ) : Fin (t+1) → ℕ := Fin.addCases (fun _ => 0) (fun _ => n+2)
noncomputable def cfg {t s : ℕ} (phase : Fin 5) (data : Configuration t s) (total head : ℕ) :=
  controlConfig (fun _ => RepeatMachine.phaseCode s phase)
    (TapeEmbedding.config (fun _ : Fin 1 => head) (fun _ => UnaryTemplate.tape total) data)

theorem padded_cfg {t s : ℕ} (phase : Fin 5) (data : Configuration t s) (total head : ℕ) :
    ZeroPadding.config (padding total) (RepeatMachine.cfg phase data total head)=cfg phase data total head := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [ZeroPadding.config,RepeatMachine.cfg,cfg,controlConfig,TapeEmbedding.config,padding,Fin.addCases_left,ZeroPadding.pad_zero]
    · simp only [ZeroPadding.config,RepeatMachine.cfg,cfg,controlConfig,TapeEmbedding.config,padding,Fin.addCases_right]
      simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem loop_run (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (remaining bit : ℕ) (out : List Bool)
    (st : State a E cap r bit out) (hcount : bit+remaining=r.p)
    (hcap : ∀ j<r.p,∀ negative,MatrixVariablePacketWorkspace.footprint a r j negative≤cap) :
    ∃ final : State a E cap r r.p (MatrixPacketLoop.appendPackets r bit remaining out),∃ actual,
      runFrom (MatrixPacketLoop.machine a E) (MatrixPacketLoop.budget r cap remaining)
        (cfg 0 (MatrixPacketSignPair.input a E cap r bit out st) r.p (bit+1))=some actual ∧
      actual.final=cfg 3
        (MatrixPacketSignPair.input a E cap r r.p (MatrixPacketLoop.appendPackets r bit remaining out) final) r.p 1 ∧
      actual.steps≤MatrixPacketLoop.budget r cap remaining := by
  obtain ⟨final,base,hb,bf,bs⟩:=MatrixPacketLoop.loop_run a E cap r remaining bit out st hcount hcap
  obtain ⟨actual,ha,hf,hs,_⟩:=ZeroPadding.run_config (MatrixPacketLoop.machine a E) (padding r.p) _ _ base hb
  rw [padded_cfg] at ha
  refine ⟨final,actual,ha,?_,hs.trans_le bs⟩
  rw [hf,bf,padded_cfg]

theorem appendPackets_range (r : Request) (remaining bit : ℕ) (out : List Bool) :
    MatrixPacketLoop.appendPackets r bit remaining out=
      out++(List.range' bit remaining).flatMap (MatrixPacketSignPair.wordPair r) := by
  induction remaining generalizing bit out with
  | zero => simp [MatrixPacketLoop.appendPackets]
  | succ remaining ih =>
    simp only [MatrixPacketLoop.appendPackets,ih,List.range'_succ,List.flatMap_cons,List.append_assoc]

theorem first_tail_output (r : Request) (hp : 0<r.p) :
    MatrixPacketLoop.appendPackets r 1 (r.p-1) (MatrixPacketSignPair.wordPair r 0)=MatrixScoreBatch.output r := by
  rw [appendPackets_range]
  have h : r.p=(r.p-1)+1 := by omega
  change MatrixPacketSignPair.wordPair r 0++(List.range' 1 (r.p-1)).flatMap (MatrixPacketSignPair.wordPair r)=
    (List.range r.p).flatMap (MatrixPacketSignPair.wordPair r)
  conv_rhs => arg 2; rw [h,List.range_eq_range',List.range'_succ]
  rfl

end NearCubicWires.RepairOrdinary.MatrixPacketNativeLoop
