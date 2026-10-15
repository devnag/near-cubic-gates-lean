import Proof.MachineModel.OrdinaryMatrixDimensionPrepare

/-! A paid bounded scan over framed payload bits. Each unary mark advances
the source cursor by two physical cells; the width driver returns to one.
The same block is called twice to count a 2*U-bit matrix payload group. -/
namespace NearCubicWires.RepairOrdinary.MatrixFramedBlock
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (q : Fin s) (count head : ℕ) (source : List Bool) (pos : ℕ) : Configuration 2 s :=
  ⟨q,![head,pos],![UnaryTemplate.tape count,source]⟩
def raw : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then
      some (if bits 0 then ⟨1,fun _ => none,![.stay,.right]⟩
        else ⟨2,fun _ => none,fun _ => .stay⟩)
    else if q.val=1 then some ⟨0,fun _ => none,![.right,.right]⟩ else none

theorem marker_step (count k : ℕ) (source : List Bool) (pos : ℕ) (hk : k<count) :
    step raw (config 0 count (k+1) source pos)=some (config 1 count (k+1) source (pos+1)) := by
  simp [step,raw,config,Configuration.scanned,UnaryTemplate.tape_mark count k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem bit_step (count k : ℕ) (source : List Bool) (pos : ℕ) :
    step raw (config 1 count (k+1) source pos)=some (config 0 count (k+2) source (pos+1)) := by
  simp [step,raw,config]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem stop_step (count : ℕ) (source : List Bool) (pos : ℕ) :
    step raw (config 0 count (count+1) source pos)=some (config 2 count (count+1) source pos) := by
  simp [step,raw,config,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem raw_timed (count k remaining : ℕ) (source : List Bool) (pos : ℕ) (hc : k+remaining=count) :
    Timed raw (2*remaining+1) (config 0 count (k+1) source pos)
      (config 2 count (count+1) source (pos+2*remaining)) := by
  induction remaining generalizing k pos with
  | zero =>
    have hk : k=count := by omega
    subst k
    simpa using Timed.single (by rfl) (stop_step count source pos)
  | succ remaining ih =>
    have h0 := Timed.single (by rfl) (marker_step count k source pos (by omega))
    have h1 := Timed.single (by rfl) (bit_step count k source (pos+1))
    have ht := ih (k+1) (pos+2) (by omega)
    have hall := h0.trans (h1.trans (by simpa [Nat.add_assoc] using ht))
    have htime : 1+(1+(2*remaining+1))=2*(remaining+1)+1 := by omega
    have hpos : pos+(2+2*remaining)=pos+2*(remaining+1) := by omega
    simpa only [htime,hpos] using hall

def reset : Machine 2 3 := TapeEmbedding.machine 1 UnaryTemplate.machine
def machine : Machine 2 6 := Composition.machine raw reset

theorem block_run (count : ℕ) (source : List Bool) (pos : ℕ) :
    ∃ r : ExecutionReceipt 2 6,
      runFrom machine (3*count+4) (config 0 count 1 source pos)=some r ∧
      r.final=config 5 count 1 source (pos+2*count) ∧ r.steps=3*count+4 := by
  obtain ⟨first,hr,hf,hs⟩ := (raw_timed count 0 count source pos (by omega)).run (by rfl)
  obtain ⟨last,hl,hlf,hls,_⟩ := UnaryTemplate.reset_run count
  have he := TapeEmbedding.run_embed UnaryTemplate.machine
    (fun _ : Fin 1 => pos+2*count) (fun _ : Fin 1 => source) _ _ last hl
  have hi : TapeEmbedding.config (fun _ : Fin 1 => pos+2*count) (fun _ : Fin 1 => source)
      (UnaryTemplate.config 0 (UnaryTemplate.tape count) (count+1)) =
      Composition.restart first.final reset.start := by
    rw [hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at he
  have hj := Composition.run_join raw reset (2*count+1) (count+2) _ first
    (TapeEmbedding.receipt (fun _ : Fin 1 => pos+2*count) (fun _ : Fin 1 => source) last) hr he
  refine ⟨Composition.joinedReceipt first
    (TapeEmbedding.receipt (fun _ : Fin 1 => pos+2*count) (fun _ : Fin 1 => source) last),?_,?_,?_⟩
  · have ht : 2*count+1+1+(count+2)=3*count+4 := by omega
    rw [ht] at hj
    exact hj
  · change Composition.rightConfig 3
      (TapeEmbedding.config (fun _ : Fin 1 => pos+2*count) (fun _ : Fin 1 => source) last.final)=_
    rw [hlf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  · change first.steps+1+last.steps=_
    omega

def double : Machine 2 12 := Composition.machine machine machine

theorem double_run (count : ℕ) (source : List Bool) (pos : ℕ) :
    ∃ r : ExecutionReceipt 2 12,
      runFrom double (6*count+9) (config 0 count 1 source pos)=some r ∧
      r.final=config 11 count 1 source (pos+4*count) ∧ r.steps=6*count+9 := by
  obtain ⟨first,hr,hf,hs⟩ := block_run count source pos
  obtain ⟨last,hl,hlf,hls⟩ := block_run count source (pos+2*count)
  have hi : Composition.restart first.final machine.start=config 0 count 1 source (pos+2*count) := by rw [hf]; rfl
  rw [← hi] at hl
  have hj := Composition.run_join machine machine (3*count+4) (3*count+4) _ first last hr hl
  refine ⟨Composition.joinedReceipt first last,?_,?_,?_⟩
  · have ht : 3*count+4+1+(3*count+4)=6*count+9 := by omega
    rw [ht] at hj
    exact hj
  · change Composition.rightConfig 6 last.final=_
    rw [hlf]
    have ht : pos+2*count+2*count=pos+4*count := by omega
    rw [ht]
    rfl
  · change first.steps+1+last.steps=_
    omega

end NearCubicWires.RepairOrdinary.MatrixFramedBlock
