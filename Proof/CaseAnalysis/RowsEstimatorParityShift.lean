import Proof.CaseAnalysis.RowsEstimatorParityScan

/-! Logical-length positioning uses the same retained arity template and keeps every byte. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Shift
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding Glyph
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def body (t : ℕ) (left : Bool):=DecompositionCountPosition.move (Scan.direction t (if left then .left else .right))
noncomputable def machine (t : ℕ) (left : Bool):=CloseoutRowsDegreeLoop.machine (body t left)
def position (left : Bool) (pos Q j : ℕ):=if left then pos+Q-j else pos+j
noncomputable def entry {t : ℕ} (left : Bool) (pos Q : ℕ) (source : List Bool)
    (out : Fin t→List Bool) (j : ℕ) (_unused : List Bool):=cfg (body t left).start source (position left pos Q j) out

theorem shift_run {t : ℕ} (left : Bool) (pos Q : ℕ) (source : List Bool) (out : Fin t→List Bool) :
    Step (machine t left) (4*Q+3)
      (Fin.addCases (heads (if left then pos+Q else pos) out) (fun _ : Fin 1=>1))
      (Fin.addCases (data source out) (fun _ : Fin 1=>CompareMachine.word Q))
      (Fin.addCases (heads (if left then pos else pos+Q) out) (fun _ : Fin 1=>1))
      (Fin.addCases (data source out) (fun _ : Fin 1=>CompareMachine.word Q)) := by
  have supplier : ∀ j<Q,∀ acc,∃ r,runFrom (body t left) 1 (entry left pos Q source out j acc)=some r ∧
      r.final.heads=(entry left pos Q source out (j+1) (acc++[])).heads ∧
      r.final.tapes=(entry left pos Q source out (j+1) (acc++[])).tapes ∧r.steps≤1:=by
    intro j hj acc
    obtain ⟨r,hr,rf,rs⟩:=DecompositionCountPosition.move_run
      (Scan.direction t (if left then .left else .right)) (heads (position left pos Q j) out) (data source out)
    refine ⟨r,hr,?_,by rw [rf];rfl,rs.le⟩
    rw [rf]
    funext i
    refine Fin.cases ?_ (fun _=>rfl) i
    change (if left then HeadMove.left else .right).apply (position left pos Q j)=position left pos Q (j+1)
    cases left <;> simp [position,HeadMove.apply] <;> omega
  obtain ⟨r,hr,rf,_⟩:=CloseoutRowsDegreeLoop.loop_run (body t left)
    (entry left pos Q source out) (fun _=>[]) 1 Q (by intros;rfl) supplier []
  have h:=Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  simpa [machine,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,entry,cfg,position,Nat.mul_comm] using h

noncomputable def scan {t : ℕ} (fs : List (Stroke t)):=Composition.machine (Scan.machine fs) (machine t true)

theorem scan_run {t : ℕ} (fs : List (Stroke t)) (pre bits tail : List Bool) (out : Fin t→List Bool) :
    Step (scan fs) (bits.length*(2*fs.length+9)+7)
      (Fin.addCases (heads pre.length out) (fun _ : Fin 1=>1))
      (Fin.addCases (data (pre++bits++tail) out) (fun _ : Fin 1=>CompareMachine.word bits.length))
      (Fin.addCases (heads pre.length (fun i=>out i++bits.flatMap (fun b=>word fs b i))) (fun _ : Fin 1=>1))
      (Fin.addCases (data (pre++bits++tail) (fun i=>out i++bits.flatMap (fun b=>word fs b i)))
        (fun _ : Fin 1=>CompareMachine.word bits.length)) := by
  have h:=(Scan.scan_run fs pre bits tail out).seq
    (shift_run true pre.length bits.length (pre++bits++tail) (fun i=>out i++bits.flatMap (fun b=>word fs b i)))
  have ht:bits.length*(2*fs.length+5)+3+1+(4*bits.length+3)=bits.length*(2*fs.length+9)+7:=by ring
  rw [ht] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Shift
