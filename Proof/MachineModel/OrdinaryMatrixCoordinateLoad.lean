import Proof.MachineModel.OrdinaryMatrixCoordinatePrefix

/-! Bounded coordinate workspace and the actual equal-width field loader.
The table and output cursors remain global streaming cursors. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
open LocalBitMultitape Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (w cap : ℕ) (source : List Bool) (pos : ℕ)
    (record clone rank out : List Bool) : Configuration 12 s :=
  ⟨q,fun i => if i.val=7 then pos else if i.val=10 then out.length else 0,
    ![record,clone,List.replicate (4*w+1) false,List.replicate (8*w+3) false,
      rank,List.replicate (2*w+1) false,List.replicate (24*w+14) false,source,
      frame (List.replicate w false),frame (List.replicate w false),out,List.replicate cap false]⟩
def extraHeads (out : List Bool) : Fin 4 → ℕ := ![0,0,out.length,0]
def extraTapes (w cap : ℕ) (out : List Bool) : Fin 4 → List Bool :=
  ![frame (List.replicate w false),frame (List.replicate w false),out,List.replicate cap false]
def load : Machine 12 21 := TapeEmbedding.machine 4 RecordLoad.machine

theorem load_input (w cap : ℕ) (a b source record clone rank out : List Bool)
    (pos : ℕ) (ha : a.length=w) (hb : b.length=w) :
    TapeEmbedding.config (extraHeads out) (extraTapes w cap out)
      (RecordLoad.config RecordLoad.machine.start (RecordLoad.workspace a b record clone rank) source pos)=
      cfg load.start w cap source pos record clone rank out := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [TapeEmbedding.config,Fin.addCases,RecordLoad.config,RecordLoad.workspace,
      RecordExtractReset.input,RecordExtract.input,RecordClone.input,RecordClone.raw,
      extraTapes,cfg,ha,hb]
    all_goals omega

theorem load_output (w cap : ℕ) (a b source out : List Bool) (pos : ℕ)
    (ha : a.length=w) (hb : b.length=w) :
    TapeEmbedding.config (extraHeads out) (extraTapes w cap out)
      (RecordLoad.config (20 : Fin 21) (RecordExtractReset.output a b) source pos)=
      cfg (20 : Fin 21) w cap source pos (frame (a++b)) (frame (a++b)) (frame b) out := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [TapeEmbedding.config,Fin.addCases,RecordLoad.config,
      RecordExtractReset.output,RecordExtract.finished,extraTapes,cfg,ha,hb]
    all_goals omega

theorem load_run (w cap : ℕ) (a b pre suffix record clone rank out : List Bool)
    (ha : a.length=w) (hb : b.length=w) (hr : record.length ≤ 4*w+1)
    (hc : clone.length ≤ 4*w+1) (hk : rank.length ≤ 2*w+1) :
    ∃ actual : ExecutionReceipt 12 21,
      runFrom load (56*w+34) (cfg load.start w cap (pre++frame (a++b)++suffix)
        pre.length record clone rank out)=some actual ∧
      actual.final=cfg 20 w cap (pre++frame (a++b)++suffix) (pre.length+4*w+1)
        (frame (a++b)) (frame (a++b)) (frame b) out ∧ actual.steps=56*w+34 := by
  obtain ⟨base,hbase,hf,hs,_⟩ := RecordLoad.load_run a b pre suffix record clone rank
    (hb.trans ha.symm) (by simpa [ha] using hr) (by simpa [ha] using hc) (by simpa [ha] using hk)
  have he := TapeEmbedding.run_embed RecordLoad.machine (extraHeads out) (extraTapes w cap out) _ _ base hbase
  rw [load_input w cap a b _ record clone rank out pre.length ha hb] at he
  rw [ha] at he hs
  refine ⟨TapeEmbedding.receipt (extraHeads out) (extraTapes w cap out) base,he,?_,hs⟩
  change TapeEmbedding.config _ _ base.final=_
  rw [hf,ha]
  exact load_output w cap a b _ out _ ha hb

end NearCubicWires.RepairOrdinary.MatrixCoordinateTranspose
