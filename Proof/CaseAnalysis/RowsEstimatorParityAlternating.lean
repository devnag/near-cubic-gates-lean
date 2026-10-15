import Proof.CaseAnalysis.RowsEstimatorParityIdentity

/-! Actual alternating-byte printer for both native parity top gates and their raw bottom count. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Alternating
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding Glyph
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flip (t : ℕ) : Machine (t+1) 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q bs=>if q=0 then some ⟨1,Fin.cases (some (!bs 0)) (fun _=>none),fun _=>.stay⟩ else none

theorem flip_run {t : ℕ} (b : Bool) (tail : List Bool) (out : Fin t→List Bool) :
    Step (flip t) 1 (heads 0 out) (data (b::tail) out) (heads 0 out) (data ((!b)::tail) out) := by
  have hs:step (flip t) (cfg 0 (b::tail) 0 out)=some (cfg 1 ((!b)::tail) 0 out):=by
    simp only [step,flip]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;refine Fin.cases rfl (fun _=>rfl) i
    · funext i;refine Fin.cases rfl (fun _=>rfl) i
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

def flag : ℕ→Bool
  | 0=>false
  | n+1=>!flag n
noncomputable def body {t : ℕ} (fs : List (Stroke t)):=Composition.machine (Glyph.machine fs) (flip t)
noncomputable def machine {t : ℕ} (fs : List (Stroke t)):=CloseoutRowsDegreeLoop.machine (body fs)
def emittedPrefix {t : ℕ} (fs : List (Stroke t)) (j : ℕ) (out : Fin t→List Bool):=
  fun i=>out i++(List.range j).flatMap (fun a=>word fs (flag a) i)
noncomputable def entry {t : ℕ} (fs : List (Stroke t)) (tail : List Bool) (out : Fin t→List Bool)
    (j : ℕ) (_unused : List Bool):=cfg (body fs).start (flag j::tail) 0 (emittedPrefix fs j out)

theorem prefix_succ {t : ℕ} (fs : List (Stroke t)) (j : ℕ) (out : Fin t→List Bool) :
    emittedPrefix fs (j+1) out=(fun i=>emittedPrefix fs j out i++word fs (flag j) i) := by
  funext i
  simp [emittedPrefix,List.range_succ,List.flatMap_append,List.append_assoc]

theorem alternating_run {t : ℕ} (fs : List (Stroke t)) (tail : List Bool) (Q : ℕ) (out : Fin t→List Bool) :
    Step (machine fs) (Q*(2*fs.length+5)+3)
      (Fin.addCases (heads 0 out) (fun _ : Fin 1=>1))
      (Fin.addCases (data (false::tail) out) (fun _ : Fin 1=>CompareMachine.word Q))
      (Fin.addCases (heads 0 (emittedPrefix fs Q out)) (fun _ : Fin 1=>1))
      (Fin.addCases (data (flag Q::tail) (emittedPrefix fs Q out)) (fun _ : Fin 1=>CompareMachine.word Q)) := by
  have supplier : ∀ j<Q,∀ acc,∃ r,
      runFrom (body fs) (2*fs.length+2) (entry fs tail out j acc)=some r ∧
      r.final.heads=(entry fs tail out (j+1) (acc++[])).heads ∧
      r.final.tapes=(entry fs tail out (j+1) (acc++[])).tapes ∧r.steps≤2*fs.length+2 := by
    intro j _ acc
    have first:=word_run fs (flag j) (flag j::tail) 0 (emittedPrefix fs j out) rfl
    have actual:=first.seq (flip_run (flag j) tail (fun i=>emittedPrefix fs j out i++word fs (flag j) i))
    simpa only [Step,body,entry,cfg,flag,prefix_succ,show 2*fs.length+1+1=2*fs.length+2 by omega] using actual
  obtain ⟨r,hr,rf,_⟩:=CloseoutRowsDegreeLoop.loop_run (body fs) (entry fs tail out)
    (fun _=>[]) (2*fs.length+2) Q (by intros;rfl) supplier []
  have actual:=Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have h0:emittedPrefix fs 0 out=out:=by funext i;simp [emittedPrefix]
  simpa only [machine,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,entry,cfg,flag,h0,
    show 2*fs.length+2+3=2*fs.length+5 by omega] using actual

def symmetricStrokes : List (Stroke 2):=
  [![some (fun _=>true),some (fun _=>true)],![some not,none]]
def thresholdStrokes : List (Stroke 2):=
  [![some (fun _=>true),some (fun _=>true)],![some id,none],
   ![some (fun _=>true),none],![some (fun _=>true),none],
   ![some (fun _=>true),none],![some (fun _=>false),none],
   ![some (fun _=>true),none],![some (fun _=>true),none]]

theorem symmetric_bytes (b : Bool) : (fun i=>word symmetricStrokes b i)=![[true,!b],[true]] := by
  funext i;fin_cases i <;>rfl

theorem threshold_bytes (b : Bool) : (fun i=>word thresholdStrokes b i)=![Fragment.body [b,true,false,true],[true]] := by
  funext i;fin_cases i <;>rfl

theorem flag_odd (j : ℕ) : flag j=decide (Odd j) := by
  induction j with
  | zero=>simp [flag]
  | succ j ih=>
    rw [flag,ih]
    rcases Nat.even_or_odd j with he | ho
    · simp [Nat.not_odd_iff_even.mpr he,he.add_one]
    · simp [ho,Nat.not_odd_iff_even.mpr ho.add_one]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Alternating
