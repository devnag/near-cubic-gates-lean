import Proof.MachineModel.OrdinaryMatrixRightStableLoop

/-! Exact shared bank projection for a reusable right-gate call. The
existing ranked-packet loader keeps its 35-tape ABI; two allocated scratch
tapes supply the right complement and restored B copy. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightGateLayout
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints MatrixScoreWeight
open MatrixRightAdvance (Store)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 26 → Fin 37 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,35,25,36,21,22]
theorem slots_injective : Function.Injective slots := by decide
def data (r : Request) (v : Store) (packet : List Bool) (unused : Fin 3 → List Bool) (source : List Bool) : Fin 37 → List Bool :=
  Fin.addCases (m := 35) (n := 2) (motive := fun _ => List Bool)
    (MatrixBucketGatePrepare.data r v.inner v.a v.rank v.upper v.record v.clone packet v.out unused source)
    (fun _ => zeros (MatrixScoreReusableRanks.D r))
def heads (outLen pos : ℕ) : Fin 37 → ℕ :=
  Fin.addCases (m := 35) (n := 2) (motive := fun _ => ℕ) (MatrixBucketGatePrepare.heads outLen pos) (fun _ => 0)
def cfg {s : ℕ} (q : Fin s) (r : Request) (v : Store) (packet : List Bool)
    (unused : Fin 3 → List Bool) (source : List Bool) (pos : ℕ) : Configuration 37 s :=
  ⟨q,heads v.out.length pos,data r v packet unused source⟩

noncomputable def core (r : Request) (g : Fin r.Gates) (v : Store) : Fin 25 → List Bool :=
  ![frame (SignedSortKey.binary (H r) v.a),frame (SignedSortKey.binary (H r) v.b),
    v.upper,zeros (2*H r+1),frame (SignedSortKey.binary (H r) v.rank),[false],[true],zeros (6*H r+6),
    v.out,v.record,v.clone,zeros (4*H r+1),zeros (8*H r+3),zeros (2*H r+1),zeros (24*H r+14),
    MatrixScoreRawRanks.output r g,frame (SignedSortKey.binary r.M 0),frame (SignedSortKey.binary r.M v.inner),
    frame (SignedSortKey.binary r.M 0),zeros (MatrixScoreReusableRanks.D r),zeros (MatrixScoreReusableRanks.D r),
    zeros (2*H r+1),frame (SignedSortKey.binary (H r) (r.bucketSize+1)),zeros (2*H r+1),zeros (4*H r+3)]

theorem core_tapes {s : ℕ} (q : Fin s) (r : Request) (g : Fin r.Gates) (v : Store) :
    (MatrixRightBucket.cfg q (MatrixRightNativeCall.params r g) v).tapes=core r g v := by
  funext i
  fin_cases i <;> rfl

theorem driver_tapes (r : Request) (g : Fin r.Gates) (phase : Fin 5) (v : Store) :
    (ZeroPadding.config (MatrixRightNativeCall.driverCaps r)
      (RepeatMachine.cfg phase (MatrixRightBucket.cfg MatrixRightBucket.machine.start (MatrixRightNativeCall.params r g) v)
        r.Buckets 1)).tapes=
      Fin.addCases (m := 25) (n := 1) (motive := fun _ => List Bool) (core r g v) (fun _ => UnaryTemplate.tape r.Buckets) := by
  funext i
  refine Fin.addCases (m := 25) (n := 1) (motive := fun j =>
    (ZeroPadding.config (MatrixRightNativeCall.driverCaps r)
      (RepeatMachine.cfg phase (MatrixRightBucket.cfg MatrixRightBucket.machine.start (MatrixRightNativeCall.params r g) v)
        r.Buckets 1)).tapes j =
    Fin.addCases (m := 25) (n := 1) (motive := fun _ => List Bool) (core r g v) (fun _ => UnaryTemplate.tape r.Buckets) j) ?_ ?_ i
  · intro j
    have hj : (j.castAdd 1 : Fin 26)≠25 := by
      intro h
      have hv := congrArg Fin.val h
      change j.val=25 at hv
      omega
    simp only [ZeroPadding.config,MatrixRightNativeCall.driverCaps,hj,ite_false,ZeroPadding.pad_zero,
      RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left]
    exact congrFun (core_tapes _ r g v) j
  · intro j
    fin_cases j
    change ZeroPadding.pad (r.Buckets+2) (CompareMachine.word r.Buckets)=UnaryTemplate.tape r.Buckets
    simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem native_tapes (r : Request) (g : Fin r.Gates) (phase : Fin 5) (v : Store) :
    (MatrixRightNativeCall.cfg r g phase v).tapes=fun i => ZeroPadding.pad (MatrixRightNativeCall.caps r i)
      (Fin.addCases (m := 25) (n := 1) (motive := fun _ => List Bool) (core r g v) (fun _ => UnaryTemplate.tape r.Buckets) i) := by
  change (fun i => ZeroPadding.pad _ ((ZeroPadding.config _ _).tapes i))=_
  rw [driver_tapes]

theorem selected_tapes (r : Request) (g : Fin r.Gates) (phase : Fin 5) (v : Store)
    (hB : v.b=r.bucketSize+1) (unused : Fin 3 → List Bool) (source : List Bool) :
    ∀ j,data r v (MatrixScoreRawRanks.output r g) unused source (slots j)=
      (MatrixRightNativeCall.cfg r g phase v).tapes j := by
  have hcap : 2*H r+1≤MatrixScoreReusableRanks.D r := by
    have h := MatrixBucketCallBounds.workspace_fit r
    omega
  intro j
  rw [native_tapes]
  fin_cases j
  all_goals simp [data,slots,Fin.addCases,MatrixBucketGatePrepare.data,MatrixBucketGatePrepare.native_core,
    MatrixBucketGatePrepare.core,MatrixBucketGatePrepare.extra,core,MatrixRightNativeCall.caps,hB,
    pad_zeros,max_eq_left hcap]

theorem selected_heads (r : Request) (g : Fin r.Gates) (phase : Fin 5) (v : Store) (pos : ℕ) :
    ∀ j,heads v.out.length pos (slots j)=(MatrixRightNativeCall.cfg r g phase v).heads j := by
  intro j
  fin_cases j <;> rfl

end NearCubicWires.RepairOrdinary.MatrixRightGateLayout
