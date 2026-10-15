import Proof.PCP.PCPPRequestNodeStart
import Proof.PCP.PCPPRequestNodeLoop

/-! Whole native Boolean-node stream conversion from actual count,
source and capacity tapes plus blank work. First allocation is executed
before the same M-controlled body; no envelope producer is duplicated. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeList
open LocalBitMultitape PCPPRequestNodeReuse
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 eraseMachine
noncomputable def machine := Composition.machine first PCPPRequestNodeLoop.machine
def input (capacity M : ℕ) (source out : List Bool) : Fin 647 → List Bool :=
  Fin.addCases (m:=646) (n:=1) (PCPPRequestNodeStart.input capacity source out)
    (fun _ => CompareMachine.word M)
def heads (pos appendPos : ℕ) : Fin 647 → ℕ :=
  Fin.addCases (m:=646) (n:=1) (bodyHeads pos appendPos) (fun _ => 1)
noncomputable def entry (capacity M : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :=
  (⟨machine.start,heads pos out.length,input capacity M source out⟩ : Configuration 647 _)
def budget (capacity M : ℕ) : ℕ := 2*capacity+M*(6*capacity+15)+8

private theorem joined_heads {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.heads=s.final.heads := rfl
private theorem joined_tapes {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.tapes=s.final.tapes := rfl

theorem cold_run {n : ℕ} (pre : List Bool) (values : List (BooleanNode n)) (suffix out : List Bool)
    (capacity : ℕ)
    (hcap : ∀ z∈values,PCPPRequestNodeCold.budget z+1 ≤ capacity) :
    ∃ r,runFrom machine (budget capacity values.length)
      (entry capacity values.length (pre++PCPPRequestNodeLoop.stream values++suffix) pre.length out)=some r ∧
      r.final.heads=(PCPPRequestNodeLoop.cfg 3 capacity (pre++PCPPRequestNodeLoop.stream values++suffix)
        (pre.length+(PCPPRequestNodeLoop.stream values).length) (out++PCPPRequestNodeLoop.encoded values) values.length 1).heads ∧
      r.final.tapes=(PCPPRequestNodeLoop.cfg 3 capacity (pre++PCPPRequestNodeLoop.stream values++suffix)
        (pre.length+(PCPPRequestNodeLoop.stream values).length) (out++PCPPRequestNodeLoop.encoded values) values.length 1).tapes ∧
      r.steps ≤ budget capacity values.length := by
  let source := pre++PCPPRequestNodeLoop.stream values++suffix
  obtain ⟨p,hp,ph,pt,ps⟩ := PCPPRequestNodeStart.start_run capacity source pre.length out
  let prepared := TapeEmbedding.receipt (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word values.length) p
  have hprepared := TapeEmbedding.run_embed eraseMachine (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word values.length) _ _ p hp
  obtain ⟨loop,hl,lf,ls⟩ := PCPPRequestNodeLoop.loop_run pre values suffix out capacity hcap
  have he : Composition.restart prepared.final PCPPRequestNodeLoop.machine.start=
      PCPPRequestNodeLoop.cfg 0 capacity source pre.length out values.length 1 := by
    apply configuration_ext
    · rfl
    · change Fin.addCases (m:=646) (n:=1) (motive:=fun _ => ℕ) p.final.heads (fun _ => 1)=_
      rw [ph]
      rfl
    · change Fin.addCases (m:=646) (n:=1) (motive:=fun _ => List Bool)
        p.final.tapes (fun _ => CompareMachine.word values.length)=_
      rw [pt]
      rfl
  rw [←he] at hl
  have joined := Composition.run_join first PCPPRequestNodeLoop.machine _ _ _ prepared loop hprepared hl
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

end NearCubicWires.RepairOrdinary.PCPPRequestNodeList
