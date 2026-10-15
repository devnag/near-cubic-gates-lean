import Proof.PCP.PCPTripleStart

/-! Whole repeated clause serialization from the actual M/source/capacity
and blank work. Fixed triple-count printing and first allocation are part of
the program, before the literal M-controlled repeated body. -/
namespace NearCubicWires.RepairOrdinary.PCPTripleCold
open LocalBitMultitape PCPSerializerReuse
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 PCPTripleStart.machine
noncomputable def machine := Composition.machine first PCPTripleLoop.machine
def input (capacity M : ℕ) (source out : List Bool) : Fin 133 → List Bool :=
  Fin.addCases (m:=132) (n:=1) (PCPTripleStart.inputTapes capacity source out)
    (fun _ => CompareMachine.word M)
def heads (pos appendPos : ℕ) : Fin 133 → ℕ :=
  Fin.addCases (m:=132) (n:=1) (PCPTripleStart.inputHeads pos appendPos) (fun _ => 1)
noncomputable def entry (capacity M : ℕ) (source : List Bool) (pos : ℕ) (out : List Bool) :=
  (⟨machine.start,heads pos out.length,input capacity M source out⟩ : Configuration 133 _)
def budget (capacity M : ℕ) : ℕ := 2*capacity+M*(6*capacity+11)+21

private theorem joined_heads {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.heads=s.final.heads := rfl
private theorem joined_tapes {t a b : ℕ} (r : ExecutionReceipt t a) (s : ExecutionReceipt t b) :
    (Composition.joinedReceipt r s).final.tapes=s.final.tapes := rfl

theorem cold_run (pre : List Bool) (groups : List (List (List Bool))) (suffix out : List Bool)
    (capacity : ℕ) (hc : 4 ≤ capacity) (hthree : ∀ fields∈groups,fields.length=3)
    (hcap : ∀ fields∈groups,PCPTraversal.budget (PCPSerializerMass.mass fields)+1 ≤ capacity) :
    ∃ r,runFrom machine (budget capacity groups.length)
      (entry capacity groups.length (pre++PCPTripleLoop.stream groups++suffix) pre.length out)=some r ∧
      r.final.heads=(PCPTripleLoop.cfg 3 capacity (pre++PCPTripleLoop.stream groups++suffix)
        (pre.length+(PCPTripleLoop.stream groups).length) (out++PCPTripleLoop.encoded groups) groups.length 1).heads ∧
      r.final.tapes=(PCPTripleLoop.cfg 3 capacity (pre++PCPTripleLoop.stream groups++suffix)
        (pre.length+(PCPTripleLoop.stream groups).length) (out++PCPTripleLoop.encoded groups) groups.length 1).tapes ∧
      r.steps ≤ budget capacity groups.length := by
  let source := pre++PCPTripleLoop.stream groups++suffix
  obtain ⟨p,hp,ph,pt,ps⟩ := PCPTripleStart.start_run capacity source pre.length out hc
  let prepared := TapeEmbedding.receipt (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word groups.length) p
  have hprepared := TapeEmbedding.run_embed PCPTripleStart.machine (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word groups.length) _ _ p hp
  obtain ⟨loop,hl,lf,ls⟩ := PCPTripleLoop.loop_run pre groups suffix out capacity hthree hcap
  have he : Composition.restart prepared.final PCPTripleLoop.machine.start=
      PCPTripleLoop.cfg 0 capacity source pre.length out groups.length 1 := by
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
  have joined := Composition.run_join first PCPTripleLoop.machine _ _ _ prepared loop hprepared hl
  have ht : (2*capacity+17)+1+(groups.length*(6*capacity+11)+3)=budget capacity groups.length := by
    unfold budget
    omega
  rw [ht] at joined
  refine ⟨Composition.joinedReceipt prepared loop,joined,?_,?_,?_⟩
  · rw [joined_heads,lf]
  · rw [joined_tapes,lf]
  · change p.steps+1+loop.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.PCPTripleCold
