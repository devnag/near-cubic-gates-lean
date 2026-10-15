import Proof.Hierarchy.CompetitorSameBucketCandidateFields

/-! The checked scalar emitter is embedded without moving the right-bank
cursor or its physical drivers. The only unbounded local tape is output34. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def native := TapeEmbedding.machine 5 CompetitorSameBucketPairEmit.machine
def extraHeads (pos : ℕ) : Fin 5 → ℕ := ![0,0,1,pos,0]
def replace (ambient : Fin 41 → List Bool) (localTapes : Fin 36 → List Bool) : Fin 41 → List Bool :=
  Fin.addCases (m := 36) (n := 5) (motive := fun _ => List Bool) localTapes (fun i => ambient (Fin.natAdd 36 i))

theorem replace_low (ambient : Fin 41 → List Bool) (localTapes : Fin 36 → List Bool) (i : Fin 36) :
    replace ambient localTapes (i.castAdd 5)=localTapes i := by simp [replace]
theorem replace_high (ambient : Fin 41 → List Bool) (localTapes : Fin 36 → List Bool) (i : Fin 5) :
    replace ambient localTapes (Fin.natAdd 36 i)=ambient (Fin.natAdd 36 i) := by simp [replace]
theorem replace_same (ambient : Fin 41 → List Bool) (localTapes : Fin 36 → List Bool)
    (h : ∀ i,ambient (i.castAdd 5)=localTapes i) : replace ambient localTapes=ambient := by
  funext i
  refine Fin.addCases (m := 36) (n := 5) (fun j => ?_) (fun j => ?_) i
  · exact (replace_low ambient localTapes j).trans (h j).symm
  · exact replace_high ambient localTapes j

theorem embed {s : ℕ} (q : Fin s) (pos : ℕ) (out : List Bool)
    (ambient : Fin 41 → List Bool) (localTapes : Fin 36 → List Bool) :
    TapeEmbedding.config (extraHeads pos) (fun i : Fin 5 => ambient (Fin.natAdd 36 i))
      (⟨q,CompetitorSameBucketPairEmit.heads out,localTapes⟩ : Configuration 36 s)=
      cfg q pos out.length (replace ambient localTapes) := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem native_run (fuel pos : ℕ) (input output : List Bool)
    (ambient : Fin 41 → List Bool) (before after : Fin 36 → List Bool)
    (hin : ∀ i,ambient (i.castAdd 5)=before i)
    (h : ∃ r,runFrom CompetitorSameBucketPairEmit.machine fuel
        ⟨CompetitorSameBucketPairEmit.machine.start,CompetitorSameBucketPairEmit.heads input,before⟩=some r ∧
      r.final.heads=CompetitorSameBucketPairEmit.heads output ∧ r.final.tapes=after ∧ r.steps≤fuel) :
    ∃ r,runFrom native fuel (cfg native.start pos input.length ambient)=some r ∧
      r.final.heads=heads pos output.length ∧ r.final.tapes=replace ambient after ∧ r.steps≤fuel := by
  obtain ⟨base,hb,bh,bt,bs⟩ := h
  have hr := TapeEmbedding.run_embed CompetitorSameBucketPairEmit.machine (extraHeads pos)
    (fun i : Fin 5 => ambient (Fin.natAdd 36 i)) _ _ base hb
  rw [embed,replace_same ambient before hin] at hr
  have he : base.final=⟨base.final.control,CompetitorSameBucketPairEmit.heads output,after⟩ :=
    configuration_ext rfl bh bt
  refine ⟨TapeEmbedding.receipt (extraHeads pos) (fun i : Fin 5 => ambient (Fin.natAdd 36 i)) base,hr,?_,?_,bs⟩
  · change (TapeEmbedding.config (extraHeads pos) (fun i : Fin 5 => ambient (Fin.natAdd 36 i)) base.final).heads=_
    rw [he,embed]
    rfl
  · change (TapeEmbedding.config (extraHeads pos) (fun i : Fin 5 => ambient (Fin.natAdd 36 i)) base.final).tapes=_
    rw [he,embed]
    rfl

theorem Store.replace {cap : ℕ} {ambient : Fin 41 → List Bool} (h : Store cap ambient)
    (localTapes : Fin 36 → List Bool) (support : ∀ i,i≠34 → (localTapes i).length≤cap) : Store cap (replace ambient localTapes) := by
  constructor
  · exact (replace_high ambient localTapes 0).trans h.driver
  · exact (replace_high ambient localTapes 1).trans h.reset
  · intro i
    fin_cases i <;> first | exact support _ (by decide) | exact h.support 29

theorem Fields.replace {cap k u p : ℕ} {coefficient : ℤ} {left out : List Bool} {ambient : Fin 41 → List Bool}
    (localTapes : Fin 36 → List Bool)
    (h : ∀ i : Fin 7,localTapes (⟨(fixedSlots i).val,by fin_cases i <;> decide⟩ : Fin 36)=fixed cap k u p coefficient left out i) :
    Fields cap k u p coefficient left out (replace ambient localTapes) := by
  intro i
  fin_cases i <;> exact h _

theorem initial_fields (cap k u p : ℕ) (coefficient : ℤ) (left right out : List Bool) :
    ∀ i : Fin 7,(part cap k u p coefficient left right out).tapes
      (⟨(fixedSlots i).val,by fin_cases i <;> decide⟩ : Fin 36)=fixed cap k u p coefficient left out i := by
  intro i
  fin_cases i <;> rfl

theorem present_fields (cap s k u p : ℕ) (sa sb coefficient : ℤ) (a b ra rb : ℕ) (out : List Bool) :
    ∀ i : Fin 7,(CompetitorSameBucketPairEmit.cfg CompetitorSameBucketPairEmit.machine.start
        (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3) cap p k coefficient out).tapes
      (⟨(fixedSlots i).val,by fin_cases i <;> decide⟩ : Fin 36)=
      fixed cap k u p coefficient (CompetitorSameBucketRankFields.source s k sa a ra) out i := by
  intro i
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
