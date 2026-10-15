import Proof.MachineModel.OrdinaryMatrixRightGateLayout

/-! The right-gate lower boundary is physically copied from the retained
native B field after the ranked packet loader has completed. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightGateBoundary
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints MatrixScoreWeight
open RecoveryRootRound (ReadyRun copyMachine)
open MatrixRightGateLayout (data heads cfg)
open MatrixRightAdvance (Store)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4 → Fin 37 := ![25,0,31,32]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def machine := RecoveryFocus.machine slots copyMachine
def next (r : Request) (v : Store) : Store := {v with a:=r.bucketSize+1}

theorem copy_ready (r : Request) (a : ℕ) :
    ReadyRun copyMachine (8*H r+8)
      ![frame (SignedSortKey.binary (H r) (r.bucketSize+1)),scalar (MatrixScoreReusableRanks.D r) (H r) a,
        zeros (MatrixScoreReusableRanks.D r),zeros (MatrixScoreReusableRanks.D r)]
      ![frame (SignedSortKey.binary (H r) (r.bucketSize+1)),scalar (MatrixScoreReusableRanks.D r) (H r) (r.bucketSize+1),
        zeros (MatrixScoreReusableRanks.D r),zeros (MatrixScoreReusableRanks.D r)] := by
  let D := MatrixScoreReusableRanks.D r
  have h4 : 4*H r+3≤D := (MatrixBatchBucketBankFields.capacity_fit r).1
  have h2 : 2*H r+1≤D := by omega
  obtain ⟨base,hb,bt,bh,bs⟩ := RecoveryRootRound.copy_ready (SignedSortKey.binary (H r) (r.bucketSize+1))
    (frame (SignedSortKey.binary (H r) a)) D D (by simp)
  simp only [SignedSortKey.binary_length,max_eq_left h2,max_eq_left h4] at hb bt bs
  obtain ⟨actual,ha,af,as,_⟩ := ZeroPadding.run_config copyMachine (![0,D,0,0] : Fin 4 → ℕ) _ _ base hb
  have hi : ZeroPadding.config (![0,D,0,0] : Fin 4 → ℕ)
      (initialConfiguration copyMachine ![frame (SignedSortKey.binary (H r) (r.bucketSize+1)),
        frame (SignedSortKey.binary (H r) a),zeros D,zeros D])=
      initialConfiguration copyMachine ![frame (SignedSortKey.binary (H r) (r.bucketSize+1)),
        scalar D (H r) a,zeros D,zeros D] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,scalar]
  change runFrom copyMachine (8*H r+8) (ZeroPadding.config (![0,D,0,0] : Fin 4 → ℕ)
    (initialConfiguration copyMachine ![frame (SignedSortKey.binary (H r) (r.bucketSize+1)),
      frame (SignedSortKey.binary (H r) a),zeros D,zeros D]))=some actual at ha
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,as.trans bs⟩
  · rw [af]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,bt,scalar,zeros,D]
  · intro i
    rw [af]
    exact bh i

theorem other_tapes (r : Request) (v : Store) (packet : List Bool) (unused : Fin 3 → List Bool)
    (source : List Bool) (i : Fin 37) (hi : i≠0) :
    data r v packet unused source i=data r (next r v) packet unused source i := by
  revert hi
  refine Fin.addCases (m := 35) (n := 2) (motive := fun j => j≠0 →
    data r v packet unused source j=data r (next r v) packet unused source j) ?_ ?_ i
  · intro j hj
    by_cases h0 : j=0
    · subst j; exact (hj rfl).elim
    by_cases h15 : j=15
    · subst j
      simp only [data,Fin.addCases_left]
      simp [MatrixBucketGatePrepare.data,Fin.addCases,
        MatrixBucketGatePrepare.native_core,MatrixBucketGatePrepare.core]
    simp only [data,Fin.addCases_left,next]
    exact (MatrixBucketGatePrepare.data_same r v.inner v.a v.rank v.upper v.record v.clone packet v.out unused source j h0 h15).trans
      (MatrixBucketGatePrepare.data_same r v.inner (r.bucketSize+1) v.rank v.upper v.record v.clone packet v.out unused source j h0 h15).symm
  · intro j _
    simp only [data,Fin.addCases_right]

theorem boundary_run (r : Request) (v : Store) (packet : List Bool) (unused : Fin 3 → List Bool)
    (source : List Bool) (pos : ℕ) : ∃ actual,
    runFrom machine (8*H r+8) (cfg machine.start r v packet unused source pos)=some actual ∧
    actual.final=cfg actual.final.control r (next r v) packet unused source pos ∧ actual.steps=8*H r+8 := by
  obtain ⟨body,hb,bt,bh,bs⟩ := copy_ready r v.a
  let entry := cfg machine.start r v packet unused source pos
  let part := initialConfiguration copyMachine
    ![frame (SignedSortKey.binary (H r) (r.bucketSize+1)),scalar (MatrixScoreReusableRanks.D r) (H r) v.a,
      zeros (MatrixScoreReusableRanks.D r),zeros (MatrixScoreReusableRanks.D r)]
  have hi : RecoveryFocus.config slots entry.heads entry.tapes part=entry := by
    apply WilliamsSourceCrop.focus_same slots entry part
    · intro j; fin_cases j <;> rfl
    · intro j
      fin_cases j <;> simp [entry,cfg,data,slots,part,initialConfiguration,Fin.addCases,
        MatrixBucketGatePrepare.data,MatrixBucketGatePrepare.native_core,MatrixBucketGatePrepare.core,
        MatrixBucketGatePrepare.extra,scalar]
  obtain ⟨actual,ha,af,as⟩ := RecoveryFocus.run_config slots slots_injective copyMachine
    entry.heads entry.tapes _ part body hb
  rw [hi] at ha
  refine ⟨actual,ha,?_,as.trans bs⟩
  rw [af]
  apply configuration_ext
  · rfl
  · funext i
    cases hx : RecoveryFocus.pick slots i with
    | none => simp only [RecoveryFocus.config,hx]; rfl
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hx
      subst i
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bh]
      fin_cases j <;> rfl
  · funext i
    cases hx : RecoveryFocus.pick slots i with
    | none =>
      have h0 : i≠0 := by
        intro h
        subst i
        have h := RecoveryFocus.pick_slot slots slots_injective 1
        change RecoveryFocus.pick slots 0=some 1 at h
        rw [hx] at h
        contradiction
      simp only [RecoveryFocus.config,hx]
      exact other_tapes r v packet unused source i h0
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hx
      subst i
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,bt]
      fin_cases j <;> simp [cfg,data,next,slots,Fin.addCases,MatrixBucketGatePrepare.data,
        MatrixBucketGatePrepare.native_core,MatrixBucketGatePrepare.core,MatrixBucketGatePrepare.extra,scalar]

end NearCubicWires.RepairOrdinary.MatrixRightGateBoundary
