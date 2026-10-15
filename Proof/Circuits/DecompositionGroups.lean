import Proof.Circuits.DecompositionGroupsStart

/-! Whole shared serialization of equally sized groups from actual count,
M, source and capacity tapes plus blank work. First allocation is executed
before the same M-controlled body; no envelope producer is duplicated. -/
namespace NearCubicWires.RepairOrdinary.DecompositionGroupsCold
open LocalBitMultitape PCPSerializerReuse
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 eraseMachine
noncomputable def machine := Composition.machine first DecompositionBalancedGroups.machine
def input (capacity count M : ℕ) (source out : List Bool) : Fin 133 → List Bool :=
  Fin.addCases (m:=132) (n:=1) (DecompositionGroupsStart.input capacity count source out)
    (fun _ => CompareMachine.word M)
def heads (pos appendPos : ℕ) : Fin 133 → ℕ :=
  Fin.addCases (m:=132) (n:=1) (bodyHeads pos appendPos) (fun _ => 1)
noncomputable def entry (capacity count M : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :=
  (⟨machine.start,heads pos out.length,input capacity count M source out⟩ : Configuration 133 _)
def budget (capacity M : ℕ) : ℕ := 2*capacity+M*(6*capacity+11)+8

private theorem joined_heads {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.heads=s.final.heads := rfl
private theorem joined_tapes {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.tapes=s.final.tapes := rfl

theorem cold_run (pre : List Bool) (groups : List (List (List Bool))) (suffix out : List Bool)
    (count capacity : ℕ) (hcount : ∀ fields∈groups,fields.length=count)
    (hcap : ∀ fields∈groups,PCPTraversal.budget (PCPSerializerMass.mass fields)+1 ≤ capacity) :
    ∃ r,runFrom machine (budget capacity groups.length)
      (entry capacity count groups.length (pre++DecompositionBalancedGroups.stream groups++suffix) pre.length out)=some r ∧
      r.final.heads=(DecompositionBalancedGroups.cfg 3 count capacity (pre++DecompositionBalancedGroups.stream groups++suffix)
        (pre.length+(DecompositionBalancedGroups.stream groups).length) (out++DecompositionBalancedGroups.encoded groups) groups.length 1).heads ∧
      r.final.tapes=(DecompositionBalancedGroups.cfg 3 count capacity (pre++DecompositionBalancedGroups.stream groups++suffix)
        (pre.length+(DecompositionBalancedGroups.stream groups).length) (out++DecompositionBalancedGroups.encoded groups) groups.length 1).tapes ∧
      r.steps ≤ budget capacity groups.length := by
  let source := pre++DecompositionBalancedGroups.stream groups++suffix
  obtain ⟨p,hp,ph,pt,ps⟩ := DecompositionGroupsStart.start_run capacity count source pre.length out
  let prepared := TapeEmbedding.receipt (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word groups.length) p
  have hprepared := TapeEmbedding.run_embed eraseMachine (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word groups.length) _ _ p hp
  obtain ⟨loop,hl,lf,ls⟩ := DecompositionBalancedGroups.loop_run pre groups suffix out count capacity hcount hcap
  have he : Composition.restart prepared.final DecompositionBalancedGroups.machine.start=
      DecompositionBalancedGroups.cfg 0 count capacity source pre.length out groups.length 1 := by
    apply configuration_ext
    · rfl
    · change Fin.addCases (m:=132) (n:=1) (motive:=fun _ => ℕ) p.final.heads (fun _ => 1)=_
      rw [ph]
      rfl
    · change Fin.addCases (m:=132) (n:=1) (motive:=fun _ => List Bool)
        p.final.tapes (fun _ => CompareMachine.word groups.length)=_
      rw [pt]
      rfl
  rw [←he] at hl
  have joined := Composition.run_join first DecompositionBalancedGroups.machine _ _ _ prepared loop hprepared hl
  have ht : (2*capacity+4)+1+(groups.length*(6*capacity+11)+3)=budget capacity groups.length := by
    unfold budget
    omega
  rw [ht] at joined
  refine ⟨Composition.joinedReceipt prepared loop,joined,?_,?_,?_⟩
  · rw [joined_heads,lf]
  · rw [joined_tapes,lf]
  · change p.steps+1+loop.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.DecompositionGroupsCold
