import Proof.MachineModel.OrdinaryMatrixRightGateScan

/-! A complete reusable right gate: physically clear/load its rank packet,
copy the retained B boundary, run every right bucket, and retain the exact
next-gate bank together with the streaming source/output cursors. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightGateBody
open LocalBitMultitape MatrixScoreBatch
open MatrixBatchBucketEndpoints (H)
open MatrixRightGateLayout (data heads cfg)
open MatrixRightAdvance (Store)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def loadMachine := TapeEmbedding.machine 2 MatrixBucketGateLoad.machine
noncomputable def prefixMachine := Composition.machine loadMachine MatrixRightGateBoundary.machine
noncomputable def machine := Composition.machine prefixMachine MatrixRightGateScan.machine
def budget (r : Request) := MatrixBucketGateLoad.budget r+1+(8*H r+8)+1+MatrixRightNativeCall.budget r
def loaded (v : Store) : Store := {v with a:=0}

theorem load_run (r : Request) (g : Fin r.Gates) (v : Store) (packet : List Bool)
    (unused : Fin 3 → List Bool) (pre suffix : List Bool) (hp : packet.length≤MatrixScoreReusableRanks.D r) :
    ∃ actual,runFrom loadMachine (MatrixBucketGateLoad.budget r)
      (cfg loadMachine.start r v packet unused (pre++MatrixScoreRawRanks.output r g++suffix) pre.length)=some actual ∧
      actual.final=cfg actual.final.control r (loaded v) (MatrixScoreRawRanks.output r g) unused
        (pre++MatrixScoreRawRanks.output r g++suffix) (pre.length+(MatrixScoreRawRanks.output r g).length) ∧
      actual.steps=MatrixBucketGateLoad.budget r := by
  obtain ⟨base,hb,bh,bt,bs⟩ := MatrixBucketGateLoad.load_run r g v.inner v.a v.rank
    v.upper v.record v.clone packet v.out unused pre suffix hp
  have he := TapeEmbedding.run_embed MatrixBucketGateLoad.machine (fun _ : Fin 2 => 0)
    (fun _ : Fin 2 => MatrixScoreWeight.zeros (MatrixScoreReusableRanks.D r)) _ _ base hb
  have hi : TapeEmbedding.config (fun _ : Fin 2 => 0)
      (fun _ : Fin 2 => MatrixScoreWeight.zeros (MatrixScoreReusableRanks.D r))
      (MatrixBucketGateLoad.input r v.inner v.a v.rank v.upper v.record v.clone packet v.out unused
        (pre++MatrixScoreRawRanks.output r g++suffix) pre.length)=
      cfg loadMachine.start r v packet unused (pre++MatrixScoreRawRanks.output r g++suffix) pre.length := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at he
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 2 => 0)
    (fun _ : Fin 2 => MatrixScoreWeight.zeros (MatrixScoreReusableRanks.D r)) base,he,?_,bs⟩
  apply configuration_ext
  · rfl
  · change (TapeEmbedding.config _ _ base.final).heads=_
    simp only [TapeEmbedding.config,bh]
    rfl
  · change (TapeEmbedding.config _ _ base.final).tapes=_
    simp only [TapeEmbedding.config,bt]
    rfl

theorem body_run (r : Request) (g : Fin r.Gates) (v : Store) (packet : List Bool)
    (unused : Fin 3 → List Bool) (pre suffix : List Bool) (hB : v.b=r.bucketSize+1)
    (hi : v.inner=g.val*r.Buckets) (hu : v.upper.length≤2*H r+1)
    (hr : v.record.length≤4*H r+1) (hc : v.clone.length≤4*H r+1)
    (hp : packet.length≤MatrixScoreReusableRanks.D r) :
    ∃ final : Store,final.b=r.bucketSize+1 ∧ final.upper.length≤2*H r+1 ∧
      final.record.length≤4*H r+1 ∧ final.clone.length≤4*H r+1 ∧
      final.a=(r.bucketSize+1)+r.Buckets*(r.bucketSize+1) ∧
      final.inner=(g.val+1)*r.Buckets ∧ final.out=v.out++MatrixRightNativeCall.output r g ∧
      ∃ actual,runFrom machine (budget r)
        (cfg machine.start r v packet unused (pre++MatrixScoreRawRanks.output r g++suffix) pre.length)=some actual ∧
        actual.final=cfg actual.final.control r final (MatrixScoreRawRanks.output r g) unused
          (pre++MatrixScoreRawRanks.output r g++suffix) (pre.length+(MatrixScoreRawRanks.output r g).length) ∧
        actual.steps≤budget r := by
  let source := pre++MatrixScoreRawRanks.output r g++suffix
  let pos := pre.length+(MatrixScoreRawRanks.output r g).length
  obtain ⟨first,hfirst,ff,fs⟩ := load_run r g v packet unused pre suffix hp
  obtain ⟨middle,hm,mf,ms⟩ := MatrixRightGateBoundary.boundary_run r (loaded v)
    (MatrixScoreRawRanks.output r g) unused source pos
  have hmid : Composition.restart first.final MatrixRightGateBoundary.machine.start=
      cfg MatrixRightGateBoundary.machine.start r (loaded v) (MatrixScoreRawRanks.output r g) unused source pos := by
    rw [ff]
    rfl
  have hm' : runFrom MatrixRightGateBoundary.machine (8*H r+8)
      (Composition.restart first.final MatrixRightGateBoundary.machine.start)=some middle := by
    rw [hmid]
    exact hm
  have hpref := Composition.run_join loadMachine MatrixRightGateBoundary.machine _ _ _ first middle hfirst hm'
  let prepared := Composition.joinedReceipt first middle
  let state := MatrixRightGateBoundary.next r (loaded v)
  obtain ⟨final,hfb,hfu,hfr,hfc,hfa,hfi,hfo,last,hl,lf,ls⟩ := MatrixRightGateScan.scan_run r g state
    unused source pos rfl hB hi hu hr hc
  have hlast : Composition.restart prepared.final MatrixRightGateScan.machine.start=
      cfg MatrixRightGateScan.machine.start r state (MatrixScoreRawRanks.output r g) unused source pos := by
    change Composition.restart (Composition.rightConfig _ middle.final) MatrixRightGateScan.machine.start=_
    rw [mf]
    rfl
  have hl' : runFrom MatrixRightGateScan.machine (MatrixRightNativeCall.budget r)
      (Composition.restart prepared.final MatrixRightGateScan.machine.start)=some last := by
    rw [hlast]
    exact hl
  have joined := Composition.run_join prefixMachine MatrixRightGateScan.machine _ _ _ prepared last hpref hl'
  refine ⟨final,hfb,hfu,hfr,hfc,hfa,hfi,hfo,Composition.joinedReceipt prepared last,joined,?_,?_⟩
  · change Composition.rightConfig _ last.final=_
    rw [lf]
    rfl
  · change first.steps+1+middle.steps+1+last.steps≤budget r
    rw [fs,ms]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixRightGateBody
