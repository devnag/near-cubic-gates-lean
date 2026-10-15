import Proof.PCP.PCPTraversalBank

/-! Execute a physical producer, then serialize its retained counted
field stream in one fresh bank. This is shared by query and clause lists. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversalBank
open LocalBitMultitape PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def producerMachine {u s : ℕ} (source count : Fin u) (p : Machine u s) :=
  Composition.machine (TapeEmbedding.machine 128 p) (machine source count)

theorem producer_run {u s : ℕ} (source count : Fin u) (hne : source≠count)
    (producer : Machine u s) (fuel : ℕ) (c : Configuration u s)
    (p : ExecutionReceipt u s) (hp : runFrom producer fuel c=some p)
    (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool)
    (hs : p.final.heads source=pre.length) (hc : p.final.heads count=1)
    (ts : p.final.tapes source=pre++FieldList.stream fields++suffix)
    (tc : p.final.tapes count=RepairSource.VerifierDecoding.CompareMachine.word fields.length) :
    ∃ r,runFrom (producerMachine source count producer) (fuel+1+PCPTraversal.budget (mass fields))
      (Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 128 => 0) (fun _ : Fin 128 => []) c))=some r ∧
      r.final.tapes ((77 : Fin 128).natAdd u)=
        ZeroPadding.pad (PCPPairReusable.capacity (mass fields)) (frame (PCPTraversal.code fields).bits) ∧
      r.final.tapes ((78 : Fin 128).natAdd u)=(PCPTraversal.code fields).bits ∧
      r.final.heads ((77 : Fin 128).natAdd u)=0 ∧
      r.final.heads ((78 : Fin 128).natAdd u)=0 ∧
      (∀ i : Fin u,r.final.tapes (i.castAdd 128)=p.final.tapes i) ∧
      (∀ i : Fin u,i≠source → r.final.heads (i.castAdd 128)=p.final.heads i) ∧
      r.steps ≤ fuel+1+PCPTraversal.budget (mass fields) := by
  let prepared := TapeEmbedding.receipt (fun _ : Fin 128 => 0) (fun _ : Fin 128 => []) p
  have hp' := TapeEmbedding.run_embed producer (fun _ : Fin 128 => 0) (fun _ : Fin 128 => []) _ _ p hp
  obtain ⟨last,hl,l77,l78,lh77,lh78,lt,lh,ls⟩ :=
    bank_run source count hne pre fields suffix p.final.heads p.final.tapes hs hc ts tc
  have he : (⟨PCPTraversal.machine.start,heads p.final.heads,tapes p.final.tapes⟩ : Configuration (u+128) _)=
      Composition.restart prepared.final (machine source count).start := rfl
  rw [he] at hl
  have joined := Composition.run_join (TapeEmbedding.machine 128 producer) (machine source count)
    _ _ _ prepared last hp' hl
  have ps := runFrom_steps_le producer fuel c p hp
  refine ⟨Composition.joinedReceipt prepared last,joined,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [PCPTripleGlobal.joined_tapes]
    exact l77
  · rw [PCPTripleGlobal.joined_tapes]
    exact l78
  · rw [PCPTripleGlobal.joined_heads]
    exact lh77
  · rw [PCPTripleGlobal.joined_heads]
    exact lh78
  · rw [PCPTripleGlobal.joined_tapes]
    exact lt
  · rw [PCPTripleGlobal.joined_heads]
    exact lh
  · change p.steps+1+last.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.PCPTraversalBank
