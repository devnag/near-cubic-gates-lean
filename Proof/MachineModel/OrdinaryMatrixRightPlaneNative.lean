import Proof.MachineModel.OrdinaryMatrixRightPlaneLayout

/-! Native completed right records through the actual transpose/sort/
selection/padding program and a paid final rewind. The entry is exactly the
retained bank format; output is the natural raw Capacity-by-U Boolean plane. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightPlaneNative
open LocalBitMultitape RecoveryExecution MatrixScoreBatch SupplierPrinter
open MatrixRightPlaneLayout (target caps)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boot : Machine 23 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun _ => none,fun i => if i=20 ∨ i=21 ∨ i=22 then .right else .stay⟩
noncomputable def forward := Composition.machine boot MatrixRightHandoff.machine
noncomputable def machine := Rewind.machine forward
noncomputable def handoffBudget (r : Request) := MatrixRightHandoff.budget r.M r.U r.Used r.Capacity
  (MatrixRightRecords.records r).length
noncomputable def forwardBudget (r : Request) := 1+1+handoffBudget r
noncomputable def budget (r : Request) := 2*forwardBudget r+2
noncomputable def input (r : Request) :=
  Fin.addCases (m := 23) (n := 1) (motive := fun _ => List Bool) (MatrixRightPlaneLayout.input r) (fun _ => [])
noncomputable def plane (r : Request) := WilliamsLoaderForms.rowMajorBitMatrix
  (padBooleanInner (Capacity := r.Capacity)
    (reindexedLaterBucketRight (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize)))

theorem boot_run (r : Request) : ∃ actual,
    run boot 1 (MatrixRightPlaneLayout.input r)=some actual ∧
    actual.final.heads=(target r).heads ∧ actual.final.tapes=(target r).tapes ∧ actual.steps=1 := by
  let final : Configuration 23 2 := ⟨1,(target r).heads,(target r).tapes⟩
  have hs : step boot (initialConfiguration boot (MatrixRightPlaneLayout.input r))=some final := by
    simp only [step,boot]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=20 ∨ i=21 ∨ i=22
      all_goals simp [applyAction,initialConfiguration,HeadMove.apply,final,MatrixRightPlaneLayout.target_heads,hi]
    · exact MatrixRightPlaneLayout.target_tapes r |>.symm
  obtain ⟨actual,ha,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨actual,ha,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht⟩

theorem handoff_run (r : Request) : ∃ actual,
    runFrom MatrixRightHandoff.machine (handoffBudget r) (target r)=some actual ∧
    actual.final.tapes 19=plane r ∧ actual.steps≤handoffBudget r := by
  have hinner : r.Used≤2^r.M := (MatrixScoreBatch.capacity r).trans
    ((WilliamsPaddedRequest.inner_le r.U).trans ((Nat.le_add_right r.U r.U).trans (MatrixScoreRawRanks.size_fit r)))
  obtain ⟨base,hb,bt,_,bs⟩ := MatrixRightHandoff.plane_run (U := r.U) (Used := r.Used) (Capacity := r.Capacity)
    r.M (MatrixRightRecords.payload r) (MatrixRightRecords.order r) (MatrixRightRecords.order_perm r)
    (MatrixScoreRawRanks.size_fit r) hinner (MatrixScoreBatch.capacity r) []
  obtain ⟨actual,ha,af,as,_⟩ := ZeroPadding.run_config MatrixRightHandoff.machine (caps r) _ _ base hb
  refine ⟨actual,ha,?_,as.trans_le bs⟩
  rw [af]
  change ZeroPadding.pad 0 (base.final.tapes 19)=_
  rw [ZeroPadding.pad_zero,bt]
  simp only [List.nil_append]
  unfold MatrixRightRecords.payload
  exact congrArg (fun A => WilliamsLoaderForms.rowMajorBitMatrix
    (padBooleanInner (Capacity := r.Capacity) A))
    (MatrixRightPaper.right_eq r.bucketSize (leftScore r) (rightScore r))

theorem forward_run (r : Request) : ∃ actual,
    run forward (forwardBudget r) (MatrixRightPlaneLayout.input r)=some actual ∧
    actual.final.tapes 19=plane r ∧ actual.steps≤forwardBudget r := by
  obtain ⟨first,hf,fh,ft,fs⟩ := boot_run r
  obtain ⟨last,hl,lt,ls⟩ := handoff_run r
  have hi : Composition.restart first.final MatrixRightHandoff.machine.start=target r := by
    apply configuration_ext
    · rfl
    · exact fh
    · exact ft
  rw [←hi] at hl
  have joined := Composition.run_join boot MatrixRightHandoff.machine _ _ _ first last hf hl
  exact ⟨Composition.joinedReceipt first last,joined,lt,by change first.steps+1+last.steps≤_; unfold forwardBudget; omega⟩

theorem plane_run (r : Request) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧ actual.final.tapes 19=plane r ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps≤budget r := by
  obtain ⟨base,hb,bt,bs⟩ := forward_run r
  obtain ⟨actual,ha,outT,ah,as,_⟩ := Rewind.reset_run forward _ _ base hb
  have hs : 2*base.steps+2≤budget r := by unfold budget; omega
  have he := run_moreFuel machine _ (budget r-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hs] at he
  exact ⟨actual,he,(outT 19).trans bt,ah,as.trans_le hs⟩

end NearCubicWires.RepairOrdinary.MatrixRightPlaneNative
