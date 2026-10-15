import Proof.MachineModel.OrdinaryMatrixScoreWeightWiden
import Proof.Amplification.RecoveryCursorCalls

/-! Reusable selected-weight carrier. The common capacity is real allocated
zero storage; its producer and the paid clearing loop remain enclosing calls. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWeight
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeros (c : ℕ) := List.replicate c false
def scalar (c w x : ℕ) := ZeroPadding.pad c (frame (binary w x))
def heads (pos apos : ℕ) : Fin 15 → ℕ := ![pos,apos,0,0,0,0,0,0,0,0,0,0,0,0,0]
def tapes (source assignment : List Bool) (c w positive negative : ℕ)
    (pflag nflag native wide flag : List Bool) : Fin 15 → List Bool :=
  ![source,assignment,ZeroPadding.pad c pflag,ZeroPadding.pad c nflag,
    ZeroPadding.pad c native,zeros c,List.replicate w true,ZeroPadding.pad c wide,
    ZeroPadding.pad c flag,zeros c,scalar c w positive,scalar c w negative,zeros c,zeros c,zeros c]
def padding (c : ℕ) : Fin 10 → ℕ := ![0,0,c,c,c,c,0,c,c,c]
def extras (c w positive negative : ℕ) : Fin 5 → List Bool :=
  ![scalar c w positive,scalar c w negative,zeros c,zeros c,zeros c]
noncomputable def wideProgram : Machine 15 13 := TapeEmbedding.machine 5 MatrixScoreWeightWiden.machine

theorem pad_zeros (c n : ℕ) : ZeroPadding.pad c (zeros n)=zeros (max c n) :=
  Rewind.Workspace.pad_zeros c n

theorem padded_accumulate (c w x a : ℕ) (hc : 4*w+3≤c) (hfit : x+a<2^w) :
    ReadyRun MatrixScoreAccumulate.machine (12*w+13)
      ![scalar c w x,scalar c w a,zeros c,zeros c,zeros c]
      ![scalar c w x,scalar c w (x+a),scalar c w (x+a),zeros c,zeros c] := by
  obtain ⟨base,hr,ht,hh,hs⟩ := MatrixScoreAccumulate.accumulate_ready w x a [] hfit (by simp)
  obtain ⟨actual,ha,hf,has,_⟩ := ZeroPadding.run_config MatrixScoreAccumulate.machine (fun _ => c) _ _ base hr
  have hi : ZeroPadding.config (fun _ : Fin 5 => c)
      (initialConfiguration MatrixScoreAccumulate.machine (MatrixScoreAccumulate.input w x a []))=
      initialConfiguration MatrixScoreAccumulate.machine
        ![scalar c w x,scalar c w a,zeros c,zeros c,zeros c] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,MatrixScoreAccumulate.input,
        scalar,zeros,ZeroPadding.pad] <;> omega
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,has.trans hs⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,ht,MatrixScoreAccumulate.output,scalar,
      zeros,Rewind.Workspace.pad_zeros] <;> omega
  · intro i
    rw [hf]
    exact hh i

theorem wide_run (pre suffix apre asuffix bits : List Bool) (c w positive negative : ℕ)
    (sign bit : Bool) (hw : bits.length≤w) (hc : 2*w+1≤c) :
    ∃ actual : ExecutionReceipt 15 13,
      runFrom wideProgram (4*bits.length+4*w+11)
        ⟨0,heads pre.length apre.length,
          tapes (pre++frame (sign::bits)++suffix) (apre++[true,bit]++asuffix) c w positive negative [] [] [] [] []⟩=some actual ∧
      actual.final.heads=heads (pre.length+2*bits.length+3) (apre.length+2) ∧
      actual.final.tapes=tapes (pre++frame (sign::bits)++suffix) (apre++[true,bit]++asuffix)
        c w positive negative [bit && !sign] [bit && sign] (frame bits)
        (frame (binary w (RadixSemantics.value bits))) [true] ∧ actual.steps=4*bits.length+4*w+11 := by
  obtain ⟨base,hb,hbf,hbs⟩ := MatrixScoreWeightWiden.widen_run pre suffix apre asuffix bits w sign bit hw
  obtain ⟨padded,hp,hpf,hps,_⟩ := ZeroPadding.run_config MatrixScoreWeightWiden.machine (padding c) _ _ base hb
  have he := TapeEmbedding.run_embed MatrixScoreWeightWiden.machine (fun _ : Fin 5 => 0)
    (extras c w positive negative) _ _ padded hp
  have hi : TapeEmbedding.config (fun _ : Fin 5 => 0) (extras c w positive negative)
      (ZeroPadding.config (padding c) (MatrixScoreWeightWiden.cfg 0 (pre++frame (sign::bits)++suffix)
        (apre++[true,bit]++asuffix) pre.length apre.length w [] [] [] [] [] 0 0))=
      (⟨0,heads pre.length apre.length,
        tapes (pre++frame (sign::bits)++suffix) (apre++[true,bit]++asuffix) c w positive negative [] [] [] [] []⟩ : Configuration 15 13) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config,Fin.addCases,ZeroPadding.config,padding,
        MatrixScoreWeightWiden.cfg,extras,tapes,zeros,ZeroPadding.pad]
  rw [hi] at he
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 5 => 0) (extras c w positive negative) padded,he,?_,?_,hps.trans hbs⟩
  · funext i
    fin_cases i <;> simp [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,hpf,hbf,
      ZeroPadding.config,MatrixScoreWeightWiden.cfg,heads]
  · funext i
    fin_cases i <;> simp [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,hpf,hbf,
      ZeroPadding.config,padding,MatrixScoreWeightWiden.cfg,extras,tapes,zeros,Rewind.Workspace.pad_zeros] <;> omega

def accumulator (negative : Bool) : Fin 15 := if negative then 11 else 10
def slots (negative : Bool) : Fin 5 → Fin 15 := ![7,accumulator negative,12,13,14]
noncomputable def addProgram (negative : Bool) : Machine 15 13 :=
  RecoveryFocus.machine (slots negative) MatrixScoreAccumulate.machine

theorem slots_injective (negative : Bool) : Function.Injective (slots negative) := by
  cases negative <;> decide

theorem selected_input (negative : Bool) (source assignment : List Bool) (c w p n x : ℕ)
    (pflag nflag native flag : List Bool) (i : Fin 5) :
    tapes source assignment c w p n pflag nflag native (frame (binary w x)) flag (slots negative i)=
      (![scalar c w x,scalar c w (if negative then n else p),zeros c,zeros c,zeros c] : Fin 5 → List Bool) i := by
  cases negative <;> fin_cases i <;> rfl

theorem selected_heads (negative : Bool) (pos apos : ℕ) (i : Fin 5) : heads pos apos (slots negative i)=0 := by
  cases negative <;> fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.MatrixScoreWeight
