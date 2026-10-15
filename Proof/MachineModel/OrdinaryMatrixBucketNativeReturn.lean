import Proof.MachineModel.OrdinaryMatrixBucketNativeCall

/-! Return the consumed Buckets driver without traversing the key output.
This closes the actual reuse boundary of one complete gate bucket call. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketNativeReturn
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 1 → Fin 23 := fun _ => 22
theorem pick_slots (i : Fin 23) : RecoveryFocus.pick slots i=if i=22 then some 0 else none := by
  by_cases hi : i=22
  · subst i
    exact RecoveryFocus.pick_slot slots (by decide) 0
  · simp [RecoveryFocus.pick,slots,hi,Ne.symm hi]
noncomputable def machine := RecoveryFocus.machine slots UnaryTemplate.machine

theorem return_run (r : Request) (inner boundary rank : ℕ) (upper record clone source out : List Bool) :
    ∃ actual,runFrom machine (r.Buckets+2)
      (MatrixBucketNativeCall.cfg r 0 inner boundary rank upper record clone source out (r.Buckets+1))=some actual ∧
      actual.final=MatrixBucketNativeCall.cfg r 2 inner boundary rank upper record clone source out 1 ∧
      actual.steps=r.Buckets+2 := by
  obtain ⟨base,hb,bf,bs,_⟩ := UnaryTemplate.reset_run r.Buckets
  obtain ⟨padded,hp,pf,ps,_⟩ := ZeroPadding.run_config UnaryTemplate.machine
    (fun _ : Fin 1 => MatrixScoreReusableRanks.D r) _ _ base hb
  let entry := MatrixBucketNativeCall.cfg r (0 : Fin 3) inner boundary rank upper record clone source out (r.Buckets+1)
  let part := ZeroPadding.config (fun _ : Fin 1 => MatrixScoreReusableRanks.D r)
    (UnaryTemplate.config 0 (UnaryTemplate.tape r.Buckets) (r.Buckets+1))
  obtain ⟨actual,ha,haf,has⟩ := RecoveryFocus.run_config slots (by decide) UnaryTemplate.machine
    entry.heads entry.tapes _ part padded hp
  have hi : RecoveryFocus.config slots entry.heads entry.tapes part=entry := by
    apply WilliamsSourceCrop.focus_same slots entry part
    · intro i; fin_cases i; rfl
    · intro i; fin_cases i; rfl
  rw [hi] at ha
  refine ⟨actual,ha,?_,has.trans (ps.trans bs)⟩
  rw [haf,pf,bf]
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i=22
    · subst i
      simp only [RecoveryFocus.config,pick_slots]
      rfl
    · simp only [RecoveryFocus.config,pick_slots,hi,ite_false]
      fin_cases i <;> first | contradiction | rfl
  · funext i
    by_cases hi : i=22
    · subst i
      simp only [RecoveryFocus.config,pick_slots]
      rfl
    · simp only [RecoveryFocus.config,pick_slots,hi,ite_false]
      rfl

noncomputable def gateMachine := Composition.machine KeyBucketLoop.machine machine
def budget (r : Request) := MatrixBucketNativeCall.budget r+1+(r.Buckets+2)

theorem gate_run (r : Request) (gate : Fin r.Gates) (rank : ℕ) (upper record clone out : List Bool)
    (hu : upper.length ≤ 2*H r+1) (hr : record.length ≤ 4*H r+1) (hc : clone.length ≤ 4*H r+1) :
    ∃ finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2*H r+1 ∧ finalRecord.length ≤ 4*H r+1 ∧ finalClone.length ≤ 4*H r+1 ∧
      ∃ actual,runFrom gateMachine (budget r)
        (Composition.leftConfig 3 (MatrixBucketNativeCall.cfg r KeyBucketLoop.machine.start
          (gate.val*r.Buckets) 0 rank upper record clone (MatrixScoreRawRanks.output r gate) out 1))=some actual ∧
        actual.final=Composition.rightConfig 154 (MatrixBucketNativeCall.cfg r 2 ((gate.val+1)*r.Buckets)
          (r.Buckets*(r.bucketSize+1)) finalRank finalUpper finalRecord finalClone
          (MatrixScoreRawRanks.output r gate) (out++MatrixBucketNativeCall.output r gate) 1) ∧
        actual.steps ≤ budget r := by
  obtain ⟨phase,finalRank,finalUpper,finalRecord,finalClone,hu',hr',hc',body,hb,bf,bs⟩ :=
    MatrixBucketNativeCall.bucket_run r gate rank upper record clone out hu hr hc
  obtain ⟨last,hl,lf,ls⟩ := return_run r ((gate.val+1)*r.Buckets) (r.Buckets*(r.bucketSize+1))
    finalRank finalUpper finalRecord finalClone (MatrixScoreRawRanks.output r gate)
    (out++MatrixBucketNativeCall.output r gate)
  have he : Composition.restart body.final machine.start=
      MatrixBucketNativeCall.cfg r 0 ((gate.val+1)*r.Buckets) (r.Buckets*(r.bucketSize+1))
        finalRank finalUpper finalRecord finalClone (MatrixScoreRawRanks.output r gate)
        (out++MatrixBucketNativeCall.output r gate) (r.Buckets+1) := by rw [bf]; rfl
  rw [←he] at hl
  have whole := Composition.run_join KeyBucketLoop.machine machine _ _ _ body last hb hl
  refine ⟨finalRank,finalUpper,finalRecord,finalClone,hu',hr',hc',_,whole,?_,?_⟩
  · change Composition.rightConfig 154 last.final=_
    rw [lf]
  · change body.steps+1+last.steps ≤ budget r
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixBucketNativeReturn
