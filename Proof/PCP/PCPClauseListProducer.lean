import Proof.PCP.PCPClauseListBank

/-! Paid producer-to-native-clause-list composition with all unrelated
caller tapes and heads retained for the final four-field encoding. -/
namespace NearCubicWires.RepairOrdinary.PCPClauseBank
open LocalBitMultitape PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def producerMachine {u s : ℕ} (source count : Fin u) (p : Machine u s) :=
  Composition.machine (TapeEmbedding.machine 309 p) (machine source count)

theorem producer_run {u s : ℕ} (source count : Fin u) (hne : source≠count)
    (producer : Machine u s) (fuel : ℕ) (c : Configuration u s)
    (p : ExecutionReceipt u s) (hp : runFrom producer fuel c=some p)
    (groups : List (List (List Bool))) (hthree : ∀ fs∈groups,fs.length=3)
    (hs : p.final.heads source=0) (hc : p.final.heads count=1)
    (ts : p.final.tapes source=PCPTripleLoop.stream groups)
    (tc : p.final.tapes count=RepairSource.VerifierDecoding.CompareMachine.word groups.length) :
    ∃ r,runFrom (producerMachine source count producer) (fuel+1+PCPClauseList.budget groups)
      (Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 309 => 0) (fun _ : Fin 309 => []) c))=some r ∧
      r.final.tapes ((258 : Fin 309).natAdd u)=
        ZeroPadding.pad (PCPPairReusable.capacity (mass (PCPClauseList.fields groups)))
          (frame (PCPTraversal.code (PCPClauseList.fields groups)).bits) ∧
      r.final.tapes ((259 : Fin 309).natAdd u)=(PCPTraversal.code (PCPClauseList.fields groups)).bits ∧
      r.final.heads ((258 : Fin 309).natAdd u)=0 ∧
      r.final.heads ((259 : Fin 309).natAdd u)=0 ∧
      (∀ i : Fin u,i≠source → i≠count →
        r.final.tapes (i.castAdd 309)=p.final.tapes i ∧ r.final.heads (i.castAdd 309)=p.final.heads i) ∧
      r.steps ≤ fuel+1+PCPClauseList.budget groups := by
  let prepared := TapeEmbedding.receipt (fun _ : Fin 309 => 0) (fun _ : Fin 309 => []) p
  have hp' := TapeEmbedding.run_embed producer (fun _ : Fin 309 => 0) (fun _ : Fin 309 => []) _ _ p hp
  obtain ⟨last,hl,l258,l259,lh258,lh259,other,ls⟩ :=
    bank_run source count hne groups hthree p.final.heads p.final.tapes hs hc ts tc
  have he : (⟨PCPClauseList.machine.start,heads p.final.heads,tapes p.final.tapes⟩ : Configuration (u+309) _)=
      Composition.restart prepared.final (machine source count).start := rfl
  rw [he] at hl
  have joined := Composition.run_join (TapeEmbedding.machine 309 producer) (machine source count)
    _ _ _ prepared last hp' hl
  have ps := runFrom_steps_le producer fuel c p hp
  refine ⟨Composition.joinedReceipt prepared last,joined,?_,?_,?_,?_,?_,?_⟩
  · rw [PCPTripleGlobal.joined_tapes]
    exact l258
  · rw [PCPTripleGlobal.joined_tapes]
    exact l259
  · rw [PCPTripleGlobal.joined_heads]
    exact lh258
  · rw [PCPTripleGlobal.joined_heads]
    exact lh259
  · rw [PCPTripleGlobal.joined_tapes,PCPTripleGlobal.joined_heads]
    exact other
  · change p.steps+1+last.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.PCPClauseBank
