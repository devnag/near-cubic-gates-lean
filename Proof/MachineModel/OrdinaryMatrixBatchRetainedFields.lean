import Proof.MachineModel.OrdinaryMatrixBatchDimensionsBounds

/-! The complete canonical-dimension execution retains the actual raw
rank producer's scalar fields. This exposes them at the next bucket caller
without assuming any field hidden by an earlier existential receipt. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRetainedFields
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem retained_run (r : Request) :
    ∃ state : MatrixBatchGateStore.Store r,∃ ranked,∃ actual,
      run MatrixBatchAllRanks.machine (MatrixBatchAllRanks.budget r) (MatrixBatchGateColdEntry.input r)=some ranked ∧
      (∀ i,ranked.final.tapes (MatrixBatchGateLayout.slots i)=
        (MatrixBatchGateNativeLoop.cfg r 3 (word r) (word r).length (MatrixBatchGateNativeLoop.output r) state).tapes i) ∧
      (∀ i,ranked.final.heads (MatrixBatchGateLayout.slots i)=
        (MatrixBatchGateNativeLoop.cfg r 3 (word r) (word r).length (MatrixBatchGateNativeLoop.output r) state).heads i) ∧
      run MatrixBatchBucketUsage.machine (MatrixBatchBucketUsage.budget r) (MatrixBatchBucketUsage.input r)=some actual ∧
      (∀ i : Fin 166,actual.final.tapes (i.castAdd 123)=ranked.final.tapes i) ∧
      (∀ i : Fin 166,actual.final.heads (i.castAdd 123)=if i=39 ∨ i=89 then 0 else ranked.final.heads i) ∧
      ranked.final.tapes 0=physicalInput r ∧ ranked.final.heads 0=0 ∧
      ranked.final.tapes 162=MatrixBatchGateNativeLoop.output r ∧ ranked.final.heads 162=(MatrixBatchGateNativeLoop.output r).length ∧
      ranked.final.tapes 40=List.replicate r.p true ∧ ranked.final.heads 40=0 ∧
      ranked.final.tapes 80=List.replicate (natBitLength r.Gates) true ∧ ranked.final.heads 80=0 ∧
      ranked.final.tapes 83=frame (SignedSortKey.binary (natBitLength r.Gates) r.Gates) ∧ ranked.final.heads 83=0 ∧
      actual.steps≤MatrixBatchBucketUsage.budget r := by
  obtain ⟨state,base,hb,bh,bt,b162,h162,b0,h0,b40,h40,b80,h80,b83,h83,bs⟩ := MatrixBatchAllRanks.all_run r
  have b39 : base.final.tapes 39=UnaryTemplate.tape r.U := (bt 27).trans (MatrixBatchRootCapacity.native_u r state)
  have h39 : base.final.heads 39=1 := bh 27
  have b130 : base.final.tapes 130=List.replicate (MatrixScoreReusableRanks.D r) true := (bt 44).trans (MatrixBatchRootCapacity.native_d r state)
  have h130 : base.final.heads 130=0 := bh 44
  have b89 : base.final.tapes 89=UnaryTemplate.tape r.Gates := by
    change base.final.tapes (MatrixBatchGateLayout.slots 48)=_
    rw [bt,MatrixBatchGateNativeLoop.cfg_tapes]
    rfl
  have h89 : base.final.heads 89=1 := bh 48
  obtain ⟨root,hr,rt,rh,r166,h166,rs⟩ := MatrixBatchRootCapacity.capacity_run r base hb b39 h39 b130 h130 bs
  obtain ⟨funded,hf,ft,fh,f196,h196,fs⟩ := MatrixBatchBucketBudget.budget_run r root hr r166 h166
    ((rt 89).trans b89) ((rh 89).trans h89) rs
  have f39 : funded.final.tapes 39=UnaryTemplate.tape r.U := (ft 39).trans ((rt 39).trans b39)
  have f39h : funded.final.heads 39=0 := (fh 39).trans (rh 39)
  obtain ⟨sized,hz,zt,zh,_,_,_,_,_,_,_,_,zs⟩ := MatrixBatchBucketSizes.sizes_run r funded hf f39 f39h f196 h196 fs
  have z32 : sized.final.tapes 32=frame (SignedSortKey.binary r.M r.U) :=
    (zt 32 (by decide)).trans ((ft 32).trans ((rt 32).trans ((bt 23).trans (MatrixBatchNativeWidth.native_u r state))))
  have z32h : sized.final.heads 32=0 := (zh 32).trans ((fh 32).trans ((rh 32).trans (bh 23)))
  obtain ⟨width,hw,wt,wh,_,_,_,_,_,_,ws⟩ := MatrixBatchNativeWidth.width_run r sized hz z32 z32h zs
  obtain ⟨same,hs,w225,h225,w166,h166,w216,h216,w222,h222,_⟩ := MatrixBatchNativeDimensions.source_fields r
  have heq : same=width := Option.some.inj (hs.symm.trans hw)
  subst same
  obtain ⟨native,hn,nt,nh,_,_,_,_,_,_,ns⟩ := MatrixBatchNativeDimensions.native_run r width hw
    w225 h225 w166 h166 w216 h216 w222 h222 ws
  have n89 : native.final.tapes 89=UnaryTemplate.tape r.Gates :=
    (nt 89).trans ((wt 89).trans ((zt 89 (by decide)).trans ((ft 89).trans ((rt 89).trans b89))))
  have n89h : native.final.heads 89=0 := (nh 89).trans ((wh 89).trans ((zh 89).trans (fh 89)))
  obtain ⟨actual,ha,atapes,ah,_,_,_,_,as⟩ := MatrixBatchBucketUsage.usage_run r native hn n89 n89h
    ((nt 222).trans w222) ((nh 222).trans h222) ((nt 166).trans w166) ((nh 166).trans h166) ns
  refine ⟨state,base,actual,hb,bt,bh,ha,?_,?_,b0,h0,b162,h162,b40,h40,b80,h80,b83,h83,as⟩
  · intro i
    have h196 : (⟨i.val,by omega⟩ : Fin 198)≠196 := by
      intro h
      have hv := congrArg (fun a : Fin 198 => a.val) h
      change i.val=196 at hv
      omega
    exact (atapes ⟨i.val,by omega⟩).trans ((nt ⟨i.val,by omega⟩).trans
      ((wt ⟨i.val,by omega⟩).trans ((zt ⟨i.val,by omega⟩ h196).trans
        ((ft (i.castAdd 25)).trans (rt i)))))
  · intro i
    have hi89 : (i.castAdd 25 : Fin 191)=89 ↔ i=89 := by
      constructor
      · intro h; exact Fin.ext (congrArg (fun a : Fin 191 => a.val) h)
      · intro h; subst i; rfl
    have tail := (ah ⟨i.val,by omega⟩).trans ((nh ⟨i.val,by omega⟩).trans
      ((wh ⟨i.val,by omega⟩).trans (zh ⟨i.val,by omega⟩)))
    apply tail.trans
    have hb' := fh (i.castAdd 25)
    simp only [hi89] at hb'
    change funded.final.heads ((i.castAdd 25).castAdd 7)=_
    rw [hb']
    by_cases h89' : i=89
    · simp [h89']
    simp only [h89',ite_false]
    rw [rh]
    by_cases h39' : i=39 <;> simp [h39']

end NearCubicWires.RepairOrdinary.MatrixBatchRetainedFields
