import Proof.Circuits.DecompositionAtomStart
import Proof.Circuits.DecompositionAtomLoop

/-! Whole native signed-field stream conversion from actual count,
source and capacity tapes plus blank work. First allocation is executed
before the same M-controlled body; no envelope producer is duplicated. -/
namespace NearCubicWires.RepairOrdinary.DecompositionAtomCold
open LocalBitMultitape DecompositionAtomReuse
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 eraseMachine
noncomputable def machine := Composition.machine first DecompositionAtomLoop.machine
def input (capacity M : ℕ) (source out : List Bool) : Fin 180 → List Bool :=
  Fin.addCases (m:=179) (n:=1) (DecompositionAtomStart.input capacity source out)
    (fun _ => CompareMachine.word M)
def heads (pos appendPos : ℕ) : Fin 180 → ℕ :=
  Fin.addCases (m:=179) (n:=1) (bodyHeads pos appendPos) (fun _ => 1)
noncomputable def entry (capacity M : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :=
  (⟨machine.start,heads pos out.length,input capacity M source out⟩ : Configuration 180 _)
def budget (capacity M : ℕ) : ℕ := 2*capacity+M*(6*capacity+15)+8

private theorem joined_heads {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.heads=s.final.heads := rfl
private theorem joined_tapes {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.tapes=s.final.tapes := rfl

theorem cold_run (pre : List Bool) (values : List ℤ) (suffix out : List Bool)
    (capacity : ℕ)
    (hcap : ∀ z∈values,DecompositionAtom.budget z+1 ≤ capacity) :
    ∃ r,runFrom machine (budget capacity values.length)
      (entry capacity values.length (pre++DecompositionAtomLoop.stream values++suffix) pre.length out)=some r ∧
      r.final.heads=(DecompositionAtomLoop.cfg 3 capacity (pre++DecompositionAtomLoop.stream values++suffix)
        (pre.length+(DecompositionAtomLoop.stream values).length) (out++DecompositionAtomLoop.encoded values) values.length 1).heads ∧
      r.final.tapes=(DecompositionAtomLoop.cfg 3 capacity (pre++DecompositionAtomLoop.stream values++suffix)
        (pre.length+(DecompositionAtomLoop.stream values).length) (out++DecompositionAtomLoop.encoded values) values.length 1).tapes ∧
      r.steps ≤ budget capacity values.length := by
  let source := pre++DecompositionAtomLoop.stream values++suffix
  obtain ⟨p,hp,ph,pt,ps⟩ := DecompositionAtomStart.start_run capacity source pre.length out
  let prepared := TapeEmbedding.receipt (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word values.length) p
  have hprepared := TapeEmbedding.run_embed eraseMachine (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word values.length) _ _ p hp
  obtain ⟨loop,hl,lf,ls⟩ := DecompositionAtomLoop.loop_run pre values suffix out capacity hcap
  have he : Composition.restart prepared.final DecompositionAtomLoop.machine.start=
      DecompositionAtomLoop.cfg 0 capacity source pre.length out values.length 1 := by
    apply configuration_ext
    · rfl
    · change Fin.addCases (m:=179) (n:=1) (motive:=fun _ => ℕ) p.final.heads (fun _ => 1)=_
      rw [ph]
      rfl
    · change Fin.addCases (m:=179) (n:=1) (motive:=fun _ => List Bool)
        p.final.tapes (fun _ => CompareMachine.word values.length)=_
      rw [pt]
      rfl
  rw [←he] at hl
  have joined := Composition.run_join first DecompositionAtomLoop.machine _ _ _ prepared loop hprepared hl
  have ht : (2*capacity+4)+1+(values.length*(6*capacity+15)+3)=budget capacity values.length := by
    unfold budget
    omega
  rw [ht] at joined
  refine ⟨Composition.joinedReceipt prepared loop,joined,?_,?_,?_⟩
  · rw [joined_heads,lf]
  · rw [joined_tapes,lf]
  · change p.steps+1+loop.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.DecompositionAtomCold
