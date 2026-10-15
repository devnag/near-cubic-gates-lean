import Proof.Rows.CapDouble
import Proof.MachineModel.OrdinaryMatrixDimensionField
import Proof.MachineModel.OrdinaryMatrixRawDimension

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace CapSentinelInput
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
abbrev word := CapDoublingPass.word

/-- The existing field parser leaves the width template at one. This pass
creates two one-cell sentinels and positions the two reverse cursors. -/
def seek : Machine 4 4 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==3
  rule := fun s bs =>
    if s=0 then some ⟨1,![some false,some false,none,none],
      ![.right,.right,.stay,.stay]⟩
    else if s=1 then
      if bs 3 then some ⟨2,fun _ => none,![.stay,.stay,.right,.stay]⟩
      else some ⟨3,fun _ => none,![.stay,.stay,.left,.left]⟩
    else if s=2 then some ⟨1,fun _ => none,![.stay,.stay,.right,.right]⟩
    else none

def seekData (w : Nat) (bits : List Bool) : Fin 4 → List Bool :=
  ![word 0,word 0,frame bits,UnaryTemplate.tape w]
def seekCfg (s : Fin 4) (w i pos : Nat) (bits : List Bool) : Configuration 4 4 :=
  ⟨s,![1,1,pos,i+1],seekData w bits⟩
def seekEnd (w : Nat) (bits : List Bool) : Configuration 4 4 :=
  ⟨3,![1,1,2*w-1,w],seekData w bits⟩

theorem seek_start (w : Nat) (bits : List Bool) :
    step seek ⟨0,![0,0,0,1],![[],[],frame bits,UnaryTemplate.tape w]⟩=
      some (seekCfg 1 w 0 0 bits) := by
  simp [step,seek]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply,seekCfg]
  · funext i;fin_cases i <;> simp [applyAction,seekCfg,seekData,word,
      CapDoublingPass.word,writeTapeBit]

theorem seek_first (w i : Nat) (bits : List Bool) (hi : i < w) :
    step seek (seekCfg 1 w i (2*i) bits)=
      some (seekCfg 2 w i (2*i+1) bits) := by
  have hr := UnaryTemplate.tape_mark w i hi
  simp [step,seek,seekCfg,seekData,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext j;fin_cases j <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem seek_second (w i : Nat) (bits : List Bool) :
    step seek (seekCfg 2 w i (2*i+1) bits)=
      some (seekCfg 1 w (i+1) (2*(i+1)) bits) := by
  simp [step,seek,seekCfg]
  apply configuration_ext
  · rfl
  · funext j
    fin_cases j <;> simp [applyAction,HeadMove.apply]
    omega
  · rfl

theorem seek_marks (w i remaining : Nat) (bits : List Bool) (hi : i+remaining=w) :
    Timed seek (2*remaining) (seekCfg 1 w i (2*i) bits)
      (seekCfg 1 w w (2*w) bits) := by
  induction remaining generalizing i with
  | zero =>
    have he : i=w := by omega
    subst i
    exact Timed.refl _ _
  | succ remaining ih =>
    have path := ((Timed.single (by rfl) (seek_first w i bits (by omega))).trans
      (Timed.single (by rfl) (seek_second w i bits))).trans (ih (i+1) (by omega))
    have ht : 1+1+2*remaining=2*(remaining+1) := by omega
    rw [ht] at path
    exact path

theorem seek_stop (w : Nat) (bits : List Bool) :
    step seek (seekCfg 1 w w (2*w) bits)=some (seekEnd w bits) := by
  simp [step,seek,seekCfg,seekData,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply,seekEnd]
  · rfl

theorem seek_run (w : Nat) (bits : List Bool) :
    Step seek (2*w+2) (![0,0,0,1] : Fin 4 → Nat)
      ![[],[],frame bits,UnaryTemplate.tape w]
      (![1,1,2*w-1,w] : Fin 4 → Nat) (seekData w bits) := by
  have path := ((Timed.single (by rfl) (seek_start w bits)).trans
    (seek_marks w 0 w bits (by omega))).trans (Timed.single (by rfl) (seek_stop w bits))
  have ht : 1+2*w+1=2*w+2 := by omega
  rw [ht] at path
  obtain ⟨r,hr,hf,_⟩ := path.run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

/-- One reverse bit consumes two framed cells and one width mark. -/
def advance : Machine 4 3 where
  descriptionBits := 0
  start := 0
  halted := fun s => s.val==2
  rule := fun s _ =>
    if s=0 then some ⟨1,fun _ => none,![.stay,.stay,.left,.left]⟩
    else if s=1 then some ⟨2,fun _ => none,![.stay,.stay,.left,.stay]⟩
    else none

theorem advance_run (pos k : Nat) (A : Fin 4 → List Bool) :
    Step advance 2 (![1,1,pos,k] : Fin 4 → Nat) A
      (![1,1,pos-2,k-1] : Fin 4 → Nat) A := by
  let c0 : Configuration 4 3 := ⟨0,![1,1,pos,k],A⟩
  let c1 : Configuration 4 3 := ⟨1,![1,1,pos-1,k-1],A⟩
  let c2 : Configuration 4 3 := ⟨2,![1,1,pos-2,k-1],A⟩
  have h0 : step advance c0=some c1 := by
    simp [step,advance,c0]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply,c1]
    · rfl
  have h1 : step advance c1=some c2 := by
    simp [step,advance,c1]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply,c2,Nat.sub_sub]
    · rfl
  have path := (Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)
  obtain ⟨r,hr,hf,_⟩ := path.run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

def copyCapacity (n : Nat) : Fin 4 → Nat := ![n+2,0,0,0]

/-- A single final copy makes the two raw unary values and a reusable
template. The source's implicit final blank is read without free allocation. -/
theorem copy_run (n : Nat) :
    ∃ H O, Step MatrixDimensionHeader.machine (2*n+3)
      (![1,0,0,0] : Fin 4 → Nat) ![word n,[],[],[]] H O ∧
      O 1=List.replicate n true ∧ H 1=0 ∧
      O 2=List.replicate n true ∧ H 2=0 ∧
      O 3=UnaryTemplate.tape n ∧ H 3=1 := by
  obtain ⟨base,hb,hf,_⟩ := MatrixDimensionHeader.header_run [false] [] n
  let entry : Configuration 4 4 :=
    ⟨MatrixDimensionHeader.machine.start,![1,0,0,0],![word n,[],[],[]]⟩
  have hi : ZeroPadding.config (copyCapacity n) entry=
      MatrixDimensionHeader.input ([false]++List.replicate n true++false::[]) 1 := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;>
        simp [ZeroPadding.config,copyCapacity,entry,MatrixDimensionHeader.input,
          ZeroPadding.pad,word,CapDoublingPass.word]
  change runFrom MatrixDimensionHeader.machine (2*n+3)
    (MatrixDimensionHeader.input ([false]++List.replicate n true++false::[]) 1)=some base at hb
  rw [←hi] at hb
  obtain ⟨r,hr,he,_,_⟩ := ZeroPadding.run_unpad MatrixDimensionHeader.machine
    (copyCapacity n) _ entry base hb
  rw [hf] at he
  have tape (i : Fin 4) := congrArg (fun c : Configuration 4 4 => c.tapes i) he
  have head (i : Fin 4) := congrArg (fun c : Configuration 4 4 => c.heads i) he
  refine ⟨r.final.heads,r.final.tapes,Step.of_run hr rfl rfl,?_,?_,?_,?_,?_,?_⟩
  · simpa [ZeroPadding.config,copyCapacity,ZeroPadding.pad,MatrixDimensionHeader.output] using tape 1
  · exact head 1
  · simpa [ZeroPadding.config,copyCapacity,ZeroPadding.pad,MatrixDimensionHeader.output] using tape 2
  · exact head 2
  · simpa [ZeroPadding.config,copyCapacity,ZeroPadding.pad,MatrixDimensionHeader.output] using tape 3
  · exact head 3

end CapSentinelInput
