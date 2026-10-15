import Proof.MachineModel.OrdinaryMatrixRightGateBoundary

/-! One right-gate native bucket traversal on the reusable 37-tape bank.
The global packet cursor and all fixed fields survive the whole call. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightGateScan
open LocalBitMultitape MatrixScoreBatch
open MatrixBatchBucketEndpoints (H)
open MatrixRightGateLayout (data heads cfg slots slots_injective)
open MatrixRightAdvance (Store)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RecoveryFocus.machine slots MatrixRightLoop.machine

theorem outside_tapes (r : Request) (v w : Store) (packet : List Bool) (unused : Fin 3 → List Bool)
    (source : List Bool) (i : Fin 37) (hi : ∀ j,slots j≠i) :
    data r v packet unused source i=data r w packet unused source i := by
  have allowed : ∀ i : Fin 37,(∀ j,slots j≠i) →
      i=23 ∨ i=24 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 := by decide
  rcases allowed i hi with h | h | h | h | h | h | h | h | h | h | h
  all_goals subst i
  all_goals simp [data,Fin.addCases,MatrixBucketGatePrepare.data,MatrixBucketGatePrepare.extra]

theorem scan_run (r : Request) (g : Fin r.Gates) (v : Store) (unused : Fin 3 → List Bool)
    (source : List Bool) (pos : ℕ) (ha : v.a=r.bucketSize+1) (hB : v.b=r.bucketSize+1)
    (hi : v.inner=g.val*r.Buckets) (hu : v.upper.length≤2*H r+1)
    (hr : v.record.length≤4*H r+1) (hc : v.clone.length≤4*H r+1) :
    ∃ final : Store,final.b=r.bucketSize+1 ∧ final.upper.length≤2*H r+1 ∧
      final.record.length≤4*H r+1 ∧ final.clone.length≤4*H r+1 ∧
      final.a=(r.bucketSize+1)+r.Buckets*(r.bucketSize+1) ∧
      final.inner=(g.val+1)*r.Buckets ∧ final.out=v.out++MatrixRightNativeCall.output r g ∧
      ∃ actual,runFrom machine (MatrixRightNativeCall.budget r)
        (cfg machine.start r v (MatrixScoreRawRanks.output r g) unused source pos)=some actual ∧
        actual.final=cfg actual.final.control r final (MatrixScoreRawRanks.output r g) unused source pos ∧
        actual.steps≤MatrixRightNativeCall.budget r := by
  obtain ⟨final,hfb,hfu,hfr,hfc,hfa,hfi,hfo,body,hb,bf,bs⟩ := MatrixRightStableLoop.native_run r g v ha hB hi hu hr hc
  let entry := cfg machine.start r v (MatrixScoreRawRanks.output r g) unused source pos
  have he : RecoveryFocus.config slots entry.heads entry.tapes (MatrixRightNativeCall.cfg r g 0 v)=entry := by
    apply WilliamsSourceCrop.focus_same slots entry (MatrixRightNativeCall.cfg r g 0 v)
    · exact MatrixRightGateLayout.selected_heads r g 0 v pos
    · exact MatrixRightGateLayout.selected_tapes r g 0 v hB unused source
  obtain ⟨actual,hact,af,as⟩ := RecoveryFocus.run_config slots slots_injective MatrixRightLoop.machine
    entry.heads entry.tapes _ _ body hb
  rw [he] at hact
  refine ⟨final,hfb,hfu,hfr,hfc,hfa,hfi,hfo,actual,hact,?_,as.trans_le bs⟩
  rw [af,bf]
  apply configuration_ext
  · rfl
  · funext i
    cases hx : RecoveryFocus.pick slots i with
    | none =>
      have h8 : i≠8 := by
        intro h
        subst i
        have h := RecoveryFocus.pick_slot slots slots_injective 8
        change RecoveryFocus.pick slots 8=some 8 at h
        rw [hx] at h
        contradiction
      simp only [RecoveryFocus.config,hx]
      fin_cases i <;> first | exact (h8 rfl).elim | rfl
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hx
      subst i
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
      exact (MatrixRightGateLayout.selected_heads r g 3 final pos j).symm
  · funext i
    cases hx : RecoveryFocus.pick slots i with
    | none =>
      have hn : ∀ j,slots j≠i := by
        intro j hj
        have hp := RecoveryFocus.pick_slot slots slots_injective j
        rw [hj,hx] at hp
        contradiction
      simp only [RecoveryFocus.config,hx]
      exact outside_tapes r v final (MatrixScoreRawRanks.output r g) unused source i hn
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hx
      subst i
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
      exact (MatrixRightGateLayout.selected_tapes r g 3 final hfb unused source j).symm

end NearCubicWires.RepairOrdinary.MatrixRightGateScan
