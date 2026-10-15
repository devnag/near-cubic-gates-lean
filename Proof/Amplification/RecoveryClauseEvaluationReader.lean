import Proof.Amplification.RecoveryClauseEvaluationLookupReady
import Proof.Amplification.RecoveryClauseEvaluationBoundary

/-! The fixed three-cell reader returns its real bounded state and preserves
the retained valuation storage at the common clause boundary. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem state_ready_extend {n time : Nat} (p : Machine 28 n) (s out : State) (e : Extra)
    (h : ReadyRun p time s.tapes out.tapes) (hl : out.bits.length=s.bits.length) :
    ReadyRun (TapeEmbedding.machine 14 p) time (tapes s e) (tapes out e) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := h
  have hrun := TapeEmbedding.run_embed p (fun _ : Fin 14=>0) (e.tapes s) _ _ base hr
  have hin : TapeEmbedding.config (fun _ : Fin 14=>0) (e.tapes s) (initialConfiguration p s.tapes)=
      initialConfiguration (TapeEmbedding.machine 14 p) (tapes s e) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;>
        simp [TapeEmbedding.config,initialConfiguration]
    · rfl
  have he : e.tapes s=e.tapes out := by
    simp [Extra.tapes,RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hl]
  rw [hin] at hrun
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 14=>0) (e.tapes s) base,hrun,?_,?_,hs⟩
  · change (Fin.addCases (m:=28) (n:=14) (motive:=fun _=>List Bool) base.final.tapes (e.tapes s))=_
    rw [ht,he]
    rfl
  · intro i
    change Fin.addCases base.final.heads (fun _ : Fin 14=>0) i=0
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa using hh j
    · simp

theorem after_capacity_mono (s : State) (which : Fin 3) : s.capacity ≤ (s.after which).capacity := by
  unfold State.after
  split
  · exact Nat.le_max_left _ _
  · exact (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)

theorem reader_properties (s : State) (hs : s.Valid) :
    (RecoveryThreeCellReader.endState s).Valid ∧
      (RecoveryThreeCellReader.endState s).bits.length=s.bits.length ∧
      s.capacity ≤ (RecoveryThreeCellReader.endState s).capacity := by
  let P (out : State) := out.Valid ∧ out.bits.length=s.bits.length ∧ s.capacity ≤ out.capacity
  have hp (out : State) (which : Fin 3) (h : P out) : P (out.after which) :=
    ⟨after_valid out which h.1,(after_length out which).trans h.2.1,
      h.2.2.trans (after_capacity_mono out which)⟩
  have h0 : P (RecoveryThreeCellReader.s0 s) := ⟨hs,rfl,Nat.le_refl _⟩
  have h1 := hp (RecoveryThreeCellReader.s0 s) 0 h0
  have h2 := hp (RecoveryThreeCellReader.s1 s) 1 h1
  have h3 := hp (RecoveryThreeCellReader.s2 s) 2 h2
  have h4 := hp (RecoveryThreeCellReader.s3 s) 0 h3
  unfold RecoveryThreeCellReader.endState
  split
  · split
    · split
      · split
        · exact h4
        · exact h4
      · exact h3
    · exact h2
  · exact h1

theorem extra_transport (s out : State) (e : Extra) (word : List Bool)
    (he : e.Valid s word) (hl : out.bits.length=s.bits.length) (hc : s.capacity ≤ out.capacity) :
    e.Valid out word := by
  have hcap : RecoveryReusableUnpair.capacity out.bits=RecoveryReusableUnpair.capacity s.bits := by
    simp [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hl]
  refine ⟨he.source,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [hl] using he.row
  · simpa [hcap] using he.counter
  · simpa [hl] using he.count
  · simpa [hl] using he.committed
  · simpa [hl] using he.cap
  · simpa [hl] using he.prefixBound
  · rw [hcap]
    exact he.reset.trans hc

theorem reader_ready (s : State) (e : Extra) (hs : s.Valid) :
    ReadyRun (programs 1) (RecoveryThreeCellReader.time s) (tapes s e)
      (tapes (RecoveryThreeCellReader.endState s) e) :=
  state_ready_extend RecoveryThreeCellReader.machine s (RecoveryThreeCellReader.endState s) e
    (RecoveryThreeCellReader.reader_ready s hs) (reader_properties s hs).2.1

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
