import Proof.CaseAnalysis.RowsEstimatorParityThreshold
import Proof.MachineModel.Runs

/-! Fixed native byte strokes append simultaneously to a fixed number of streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Glyph
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Stroke (t : ℕ):=Fin t→Option (Bool→Bool)
def byte {t : ℕ} (f : Stroke t) (b : Bool) (i : Fin t):=Option.map (fun g=>g b) (f i)
def emitted {t : ℕ} (f : Stroke t) (b : Bool) (i : Fin t):=(byte f b i).toList
def heads {t : ℕ} (pos : ℕ) (out : Fin t→List Bool) : Fin (t+1)→ℕ:=Fin.cases pos (fun i=>(out i).length)
def data {t : ℕ} (source : List Bool) (out : Fin t→List Bool) : Fin (t+1)→List Bool:=Fin.cases source out
def cfg {t s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) (out : Fin t→List Bool) : Configuration (t+1) s:=
  ⟨q,heads pos out,data source out⟩
def stroke {t : ℕ} (f : Stroke t) : Machine (t+1) 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q bs=>if q=0 then some ⟨1,Fin.cases none (byte f (bs 0)),
    Fin.cases .stay (fun i=>if (f i).isSome then .right else .stay)⟩ else none

theorem stroke_run {t : ℕ} (f : Stroke t) (b : Bool) (source : List Bool)
    (pos : ℕ) (out : Fin t→List Bool) (hb : readTapeBit source pos=b) :
    Step (stroke f) 1 (heads pos out) (data source out)
      (heads pos (fun i=>out i++emitted f b i)) (data source (fun i=>out i++emitted f b i)) := by
  have scanned:(cfg (0 : Fin 2) source pos out).scanned 0=b:=hb
  have hs:step (stroke f) (cfg 0 source pos out)=some (cfg 1 source pos (fun i=>out i++emitted f b i)):=by
    simp only [step,stroke,scanned]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.cases ?_ (fun j=>?_) i
      · rfl
      · cases he:f j <;> simp [applyAction,cfg,heads,emitted,byte,he,HeadMove.apply]
    · funext i
      refine Fin.cases ?_ (fun j=>?_) i
      · rfl
      · cases he:f j <;> simp [applyAction,cfg,heads,data,emitted,byte,he,Streaming.write_append]
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

def idle (t : ℕ) : Machine (t+1) 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
noncomputable def program {t : ℕ} : List (Stroke t)→Σ s,Machine (t+1) s
  | []=>⟨1,idle t⟩
  | f::fs=>⟨_,Composition.machine (stroke f) (program fs).2⟩
noncomputable def machine {t : ℕ} (fs : List (Stroke t)):=(program fs).2
def word {t : ℕ} (fs : List (Stroke t)) (b : Bool) (i : Fin t):=fs.flatMap (fun f=>emitted f b i)

theorem word_run {t : ℕ} (fs : List (Stroke t)) (b : Bool) (source : List Bool)
    (pos : ℕ) (out : Fin t→List Bool) (hb : readTapeBit source pos=b) :
    Step (machine fs) (2*fs.length) (heads pos out) (data source out)
      (heads pos (fun i=>out i++word fs b i)) (data source (fun i=>out i++word fs b i)) := by
  induction fs generalizing out with
  | nil=>
      have hs:=Step.of_run (show runFrom (idle t) 0 (cfg 0 source pos out)=
        some ⟨cfg 0 source pos out,0,(cfg (0 : Fin 1) source pos out).tapeCells⟩ by rfl) rfl rfl
      simpa only [machine,program,word,List.flatMap_nil,List.append_nil,List.length_nil,Nat.mul_zero,cfg] using hs
  | cons f fs ih=>
      have h:=(stroke_run f b source pos out hb).seq (ih (fun i=>out i++emitted f b i))
      have ht:1+1+2*fs.length=2*(f::fs).length:=by simp;omega
      rw [ht] at h
      simpa only [machine,program,word,List.flatMap_cons,List.append_assoc] using h

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Glyph
