import Proof.MachineModel.OrdinaryMatrixBucketGateLoad

/-! One actual reusable gate: clear the old local packet and boundary,
load the next rank packet, traverse every native bucket, return the bucket
driver. The global source and aggregate key output remain streaming. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketGateBody
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints MatrixBucketGatePrepare
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraHeads (pos : ℕ) (i : Fin 12) := if i=11 then pos else 0
noncomputable def last := TapeEmbedding.machine 12 MatrixBucketNativeReturn.gateMachine
noncomputable def machine := Composition.machine MatrixBucketGateLoad.machine last
def budget (r : Request) := MatrixBucketGateLoad.budget r+1+MatrixBucketNativeReturn.budget r
noncomputable def config (r : Request) (inner boundary rank : ℕ) (upper record clone packet out : List Bool)
    (unused : Fin 3 → List Bool) (source : List Bool) (pos : ℕ) : Configuration 35 176 :=
  ⟨machine.start,heads out.length pos,data r inner boundary rank upper record clone packet out unused source⟩

theorem embedded_eq {s : ℕ} (r : Request) (q : Fin s) (inner boundary rank : ℕ)
    (upper record clone packet out : List Bool) (unused : Fin 3 → List Bool) (source : List Bool) (pos : ℕ) :
    TapeEmbedding.config (extraHeads pos) (extra r unused source)
      (MatrixBucketNativeCall.cfg r q inner boundary rank upper record clone packet out 1)=
      ⟨q,heads out.length pos,data r inner boundary rank upper record clone packet out unused source⟩ := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem body_run (r : Request) (gate : Fin r.Gates) (boundary rank : ℕ)
    (upper record clone packet out : List Bool) (unused : Fin 3 → List Bool) (pre suffix : List Bool)
    (hu : upper.length ≤ 2*H r+1) (hr : record.length ≤ 4*H r+1) (hc : clone.length ≤ 4*H r+1)
    (hp : packet.length ≤ MatrixScoreReusableRanks.D r) :
    ∃ finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2*H r+1 ∧ finalRecord.length ≤ 4*H r+1 ∧ finalClone.length ≤ 4*H r+1 ∧
      ∃ actual,runFrom machine (budget r)
        (config r (gate.val*r.Buckets) boundary rank upper record clone packet out unused
          (pre++MatrixScoreRawRanks.output r gate++suffix) pre.length)=some actual ∧
        actual.final.heads=heads (out++MatrixBucketNativeCall.output r gate).length
          (pre.length+(MatrixScoreRawRanks.output r gate).length) ∧
        actual.final.tapes=data r ((gate.val+1)*r.Buckets) (r.Buckets*(r.bucketSize+1))
          finalRank finalUpper finalRecord finalClone (MatrixScoreRawRanks.output r gate)
          (out++MatrixBucketNativeCall.output r gate) unused
          (pre++MatrixScoreRawRanks.output r gate++suffix) ∧ actual.steps≤budget r := by
  let source := pre++MatrixScoreRawRanks.output r gate++suffix
  let pos := pre.length+(MatrixScoreRawRanks.output r gate).length
  obtain ⟨loaded,hl,lh,lt,ls⟩ := MatrixBucketGateLoad.load_run r gate (gate.val*r.Buckets) boundary rank
    upper record clone packet out unused pre suffix hp
  obtain ⟨finalRank,finalUpper,finalRecord,finalClone,hu',hr',hc',base,hb,bf,bs⟩ :=
    MatrixBucketNativeReturn.gate_run r gate rank upper record clone out hu hr hc
  let receipt := TapeEmbedding.receipt (extraHeads pos) (extra r unused source) base
  have he := TapeEmbedding.run_embed MatrixBucketNativeReturn.gateMachine (extraHeads pos)
    (extra r unused source) _ _ base hb
  have hi : TapeEmbedding.config (extraHeads pos) (extra r unused source)
      (Composition.leftConfig 3 (MatrixBucketNativeCall.cfg r KeyBucketLoop.machine.start
        (gate.val*r.Buckets) 0 rank upper record clone (MatrixScoreRawRanks.output r gate) out 1))=
      Composition.restart loaded.final last.start := by
    change TapeEmbedding.config (extraHeads pos) (extra r unused source)
      (MatrixBucketNativeCall.cfg r MatrixBucketNativeReturn.gateMachine.start (gate.val*r.Buckets)
        0 rank upper record clone (MatrixScoreRawRanks.output r gate) out 1)=_
    rw [embedded_eq]
    apply configuration_ext
    · rfl
    · exact lh.symm
    · exact lt.symm
  rw [hi] at he
  have joined := Composition.run_join MatrixBucketGateLoad.machine last _ _ _ loaded receipt hl he
  have hfinal : receipt.final=
      ⟨(2 : Fin 3).natAdd 154,heads (out++MatrixBucketNativeCall.output r gate).length pos,
        data r ((gate.val+1)*r.Buckets) (r.Buckets*(r.bucketSize+1))
          finalRank finalUpper finalRecord finalClone (MatrixScoreRawRanks.output r gate)
          (out++MatrixBucketNativeCall.output r gate) unused source⟩ := by
    change TapeEmbedding.config (extraHeads pos) (extra r unused source) base.final=_
    rw [bf]
    exact embedded_eq r _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨finalRank,finalUpper,finalRecord,finalClone,hu',hr',hc',
    Composition.joinedReceipt loaded receipt,joined,?_,?_,?_⟩
  · change receipt.final.heads=_
    exact congrArg Configuration.heads hfinal
  · change receipt.final.tapes=_
    exact congrArg Configuration.tapes hfinal
  · change loaded.steps+1+base.steps≤budget r
    rw [ls]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixBucketGateBody
