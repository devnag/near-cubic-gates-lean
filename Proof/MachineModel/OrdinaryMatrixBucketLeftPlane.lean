import Proof.MachineModel.OrdinaryMatrixBucketCrossGrid

/-! Paid driver bootstrap, actual left-grid traversal with physical zero
padding, and one final rewind. The retained U/Used/pad templates are inputs
already produced by the original-request caller. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketLeftPlane
open LocalBitMultitape RecoveryExecution MatrixScoreBatch SupplierPrinter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def source (r : Request) := StablePartition.stream (SortCarrier.sorted (MatrixBucketKeyRecords.request r))
noncomputable def left (r : Request) := reindexedLaterBucketLeft
  (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize) (fun _ => 1)
noncomputable def plane (r : Request) := WilliamsLoaderForms.rowMajorBitMatrix (fun row inner =>
  LeftPlaneCell.coefficientBit false (padSignedInner (Capacity := r.Capacity) (left r) row inner) 0)
noncomputable def rowBudget (r : Request) :=
  (MatrixRows.fields (GridRows.leftRows r.M r.M (MatrixBucketCrossGrid.payload r))).length+
    r.U*(3*r.Used+2*(r.Capacity-r.Used)+11)+1
noncomputable def rawInput (r : Request) : Fin 5 → List Bool :=
  ![source r,[],UnaryTemplate.tape r.Used,UnaryTemplate.tape (r.Capacity-r.Used),UnaryTemplate.tape r.U]
noncomputable def rawOutput (r : Request) : Fin 5 → List Bool :=
  ![source r,plane r,UnaryTemplate.tape r.Used,UnaryTemplate.tape (r.Capacity-r.Used),UnaryTemplate.tape r.U]
def boot : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun _ => none,fun (i : Fin 5) =>
    if (2 : ℕ) ≤ i.val then HeadMove.right else HeadMove.stay⟩
def forward : Machine 5 50 := Composition.machine boot MatrixRows.machine
def machine : Machine 6 52 := Rewind.machine forward
noncomputable def forwardBudget (r : Request) := rowBudget r+2
noncomputable def budget (r : Request) := 2*forwardBudget r+2
def caps (r : Request) : Fin 6 → ℕ := fun i => if i=0 then MatrixScoreReusableRanks.D r else 0
noncomputable def input (r : Request) : Fin 6 → List Bool :=
  ![MatrixBucketCoordinateSort.output r,[],UnaryTemplate.tape r.Used,
    UnaryTemplate.tape (r.Capacity-r.Used),UnaryTemplate.tape r.U,[]]

theorem boot_run (r : Request) : ∃ actual,
    run boot 1 (rawInput r)=some actual ∧ actual.final.heads=![0,0,1,1,1] ∧
    actual.final.tapes=rawInput r ∧ actual.steps=1 := by
  let final : Configuration 5 2 := ⟨1,![0,0,1,1,1],rawInput r⟩
  have hs : step boot (initialConfiguration boot (rawInput r))=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨actual,ha,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨actual,ha,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht⟩

theorem forward_run (r : Request) : ∃ actual,
    run forward (forwardBudget r) (rawInput r)=some actual ∧
    actual.final.tapes=rawOutput r ∧ actual.steps≤forwardBudget r := by
  obtain ⟨prepared,hp,ph,pt,ps⟩ := boot_run r
  have hleft : ∀ row inner,MatrixBucketCrossGrid.payload r (row.castAdd r.U) inner=
      LeftPlaneCell.coefficientBit false (left r row inner) 0 := by
    intro row inner
    exact CrossGrid.left_entry r.bucketSize (leftScore r) (rightScore r) (fun _ => 1) false 0 row inner
  obtain ⟨phase,body,hb,bf,bs,_⟩ := LeftMatrix.selected_run r.M r.M (MatrixBucketCrossGrid.payload r)
    (left r) false 0 (MatrixScoreBatch.capacity r) hleft []
  rw [← MatrixBucketCrossGrid.sorted_grid] at hb bf
  have hi : Composition.restart prepared.final MatrixRows.machine.start=
      MatrixRows.config MatrixRows.machine.start (source r) 0 [] r.Used (r.Capacity-r.Used) 1 r.U := by
    apply configuration_ext
    · rfl
    · change prepared.final.heads=_
      rw [ph]
      funext i; fin_cases i <;> rfl
    · change prepared.final.tapes=_
      rw [pt]
      funext i; fin_cases i <;> rfl
  have hn : runFrom MatrixRows.machine (rowBudget r)
      (Composition.restart prepared.final MatrixRows.machine.start)=some body := by
    rw [hi]
    exact hb
  have hj := Composition.run_join boot MatrixRows.machine 1 (rowBudget r) _ prepared body hp hn
  have he : 1+1+rowBudget r=forwardBudget r := by unfold forwardBudget; omega
  rw [he] at hj
  refine ⟨Composition.joinedReceipt prepared body,hj,?_,?_⟩
  · change body.final.tapes=_
    rw [bf]
    funext i
    fin_cases i <;> simp [MatrixRows.config,PaddedRow.config,PayloadCounted.config,TapeEmbedding.config,
      Fin.addCases,rawOutput,source,plane]
    all_goals rfl
  · change prepared.steps+1+body.steps≤forwardBudget r
    rw [ps,bs]
    change 1+1+rowBudget r≤rowBudget r+2
    omega

theorem plane_run (r : Request) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 0=MatrixBucketCoordinateSort.output r ∧ actual.final.tapes 1=plane r ∧
    actual.final.tapes 2=UnaryTemplate.tape r.Used ∧
    actual.final.tapes 3=UnaryTemplate.tape (r.Capacity-r.Used) ∧
    actual.final.tapes 4=UnaryTemplate.tape r.U ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps≤budget r := by
  obtain ⟨body,hb,bt,bs⟩ := forward_run r
  obtain ⟨reset,hr,rt,rh,rs,_⟩ := Rewind.reset_run forward _ _ body hb
  let raw : Fin 6 → List Bool := Fin.addCases (motive := fun _ : Fin (5+1) => List Bool) (rawInput r) (fun _ : Fin 1 => [])
  change run machine (2*body.steps+2) raw=some reset at hr
  obtain ⟨padded,hp,pf,ps,_⟩ := ZeroPadding.run_config machine (caps r) _ _ reset hr
  have hi : ZeroPadding.config (caps r) (initialConfiguration machine raw)=initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,caps,raw,rawInput,input,Fin.addCases,
        MatrixBucketCoordinateSort.output,source,initialConfiguration]
  rw [hi] at hp
  have hbound : 2*body.steps+2≤budget r := by unfold budget; omega
  have hm := runFrom_moreFuel machine (2*body.steps+2) (budget r-(2*body.steps+2)) _ _ hp
  rw [Nat.add_sub_of_le hbound] at hm
  have fields (i : Fin 5) : padded.final.tapes (i.castAdd 1)=ZeroPadding.pad (caps r (i.castAdd 1)) (rawOutput r i) := by
    rw [pf]
    exact congrArg (ZeroPadding.pad _) ((rt i).trans (congrFun bt i))
  refine ⟨padded,hm,fields 0,?_,?_,?_,?_,?_,?_⟩
  · exact (fields 1).trans (ZeroPadding.pad_zero _)
  · exact (fields 2).trans (ZeroPadding.pad_zero _)
  · exact (fields 3).trans (ZeroPadding.pad_zero _)
  · exact (fields 4).trans (ZeroPadding.pad_zero _)
  · intro i
    rw [pf]
    exact rh i
  · rw [ps,rs]
    exact hbound

end NearCubicWires.RepairOrdinary.MatrixBucketLeftPlane
