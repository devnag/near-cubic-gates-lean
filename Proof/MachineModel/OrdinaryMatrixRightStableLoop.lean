import Proof.MachineModel.OrdinaryMatrixRightBankEntry

/-! The existing right controller preserves the restored fixed B operand.
This strengthens its literal loop receipt at the reusable next-gate caller;
the program and its cost are unchanged. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightStableLoop
open LocalBitMultitape RecoveryExecution
open MatrixRightAdvance (Store)
open MatrixRightBucket (Params width fuel cfg)
open MatrixRightLoop (machine cost output)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stable_run (p : Params) (total n pos : ℕ) (v : Store) (hb : v.b=p.B) (hn : pos+n=total)
    (ha : v.a+n*p.B<2^width p) (hi : v.inner+n<2^p.I)
    (hu : v.upper.length ≤ 2*width p+1) (hr : v.record.length ≤ 4*width p+1)
    (hc : v.clone.length ≤ 4*width p+1) :
    ∃ final : Store,final.b=p.B ∧ final.upper.length ≤ 2*width p+1 ∧ final.record.length ≤ 4*width p+1 ∧
      final.clone.length ≤ 4*width p+1 ∧ final.a=v.a+n*p.B ∧ final.inner=v.inner+n ∧
      final.out=v.out++output p v.a v.inner n ∧
      ∃ actual,runFrom machine (n*(cost p+2)+total+3)
        (RepeatMachine.cfg 0 (cfg MatrixRightBucket.machine.start p v) total (pos+1))=some actual ∧
        actual.steps ≤ n*(cost p+2)+total+3 ∧
        actual.final=RepeatMachine.cfg 3 (cfg MatrixRightBucket.machine.start p final) total 1 := by
  induction n generalizing pos v with
  | zero =>
    have hp : pos=total := by omega
    subst pos
    obtain ⟨r,hrun,hf,hs⟩ := (RepeatMachine.exhaust MatrixRightBucket.machine (fun _ _ => true)
      (cfg MatrixRightBucket.machine.start p v) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨v,hb,hu,hr,hc,by omega,by omega,by simp [output],r,?_,?_,hf⟩
    · simpa only [machine,Nat.zero_mul,Nat.zero_add] using hrun
    · simpa using hs.le
  | succ n ih =>
    have ha1 : v.a+p.B<2^width p := by
      have hb : p.B ≤ (n+1)*p.B := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hi1 : v.inner+1<2^p.I := by omega
    obtain ⟨rank,record,clone,hrecord,hclone,body,hbody,hbf,hbs⟩ := MatrixRightBucket.bucket_run p v ha1 hi1 hu hr hc
    let state : Store :=
      {v with
        a := v.a+p.B
        b := p.B
        inner := v.inner+1
        rank := rank
        upper := frame (SignedSortKey.binary (width p) (v.a+p.B))
        record := record
        clone := clone
        out := v.out++MatrixRightBucket.output p v.a v.inner}
    have hstate : body.final=cfg 85 p state := hbf
    have hat : state.a+n*p.B<2^width p := by
      simpa only [state,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ha
    have hit : state.inner+n<2^p.I := by dsimp [state]; omega
    have hut : state.upper.length ≤ 2*width p+1 := by simp [state]
    obtain ⟨final,hfb,hfu,hfr,hfc,hfa,hfi,hfo,tail,htail,hts,htf⟩ := ih (pos+1) state rfl (by omega) hat hit hut hrecord hclone
    have hp := RepeatMachine.iteration MatrixRightBucket.machine (fun _ _ => true)
      (cfg MatrixRightBucket.machine.start p v) total pos body rfl (by omega) hbody
    simp only [↓reduceIte] at hp
    have he : RepeatMachine.cfg 0 body.final total (pos+2)=
        RepeatMachine.cfg 0 (cfg MatrixRightBucket.machine.start p state) total (pos+2) := by
      rw [hstate]
      rfl
    rw [he] at hp
    rcases hp with ⟨space,hp⟩
    have htail' : runFrom machine (n*(cost p+2)+total+3)
        (RepeatMachine.cfg 0 (cfg MatrixRightBucket.machine.start p state) total (pos+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    obtain ⟨actual,haRun,hf,hs,_⟩ := hp.followedBy tail htail'
    have hbnd : body.steps+2+(n*(cost p+2)+total+3) ≤ (n+1)*(cost p+2)+total+3 := by
      change body.steps ≤ cost p at hbs
      nlinarith only [hbs]
    have hm := runFrom_moreFuel machine _
      ((n+1)*(cost p+2)+total+3-(body.steps+2+(n*(cost p+2)+total+3))) _ actual haRun
    rw [Nat.add_sub_of_le hbnd] at hm
    refine ⟨final,hfb,hfu,hfr,hfc,?_,?_,?_,actual,hm,?_,hf.trans htf⟩
    · simpa only [state,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hfa
    · dsimp [state] at hfi
      omega
    · simpa only [state,output,List.append_assoc] using hfo
    · rw [hs]
      change body.steps ≤ cost p at hbs
      nlinarith only [hbs,hts]

theorem native_run (r : MatrixScoreBatch.Request) (g : Fin r.Gates) (v : Store)
    (ha : v.a=r.bucketSize+1) (hB : v.b=r.bucketSize+1) (hi : v.inner=g.val*r.Buckets)
    (hu : v.upper.length≤2*MatrixBatchBucketEndpoints.H r+1)
    (hr : v.record.length≤4*MatrixBatchBucketEndpoints.H r+1)
    (hc : v.clone.length≤4*MatrixBatchBucketEndpoints.H r+1) :
    ∃ final : Store,final.b=r.bucketSize+1 ∧ final.upper.length≤2*MatrixBatchBucketEndpoints.H r+1 ∧
      final.record.length≤4*MatrixBatchBucketEndpoints.H r+1 ∧ final.clone.length≤4*MatrixBatchBucketEndpoints.H r+1 ∧
      final.a=(r.bucketSize+1)+r.Buckets*(r.bucketSize+1) ∧
      final.inner=(g.val+1)*r.Buckets ∧ final.out=v.out++MatrixRightNativeCall.output r g ∧
      ∃ actual,runFrom machine (MatrixRightNativeCall.budget r) (MatrixRightNativeCall.cfg r g 0 v)=some actual ∧
        actual.final=MatrixRightNativeCall.cfg r g 3 final ∧ actual.steps≤MatrixRightNativeCall.budget r := by
  have hfa : v.a+r.Buckets*(MatrixRightNativeCall.params r g).B<2^width (MatrixRightNativeCall.params r g) := by
    rw [ha]
    exact MatrixRightNativeCall.boundary_fit r
  have hfi : v.inner+r.Buckets<2^(MatrixRightNativeCall.params r g).I := by
    rw [hi]
    exact MatrixBucketCallBounds.inner_fit r g
  obtain ⟨final,hfb,hfu,hfr,hfc,hfa,hfi,hfo,base,hb,bs,bf⟩ :=
    stable_run (MatrixRightNativeCall.params r g) r.Buckets r.Buckets 0 v hB (by omega) hfa hfi hu hr hc
  have ht : r.Buckets*(cost (MatrixRightNativeCall.params r g)+2)+r.Buckets+3=MatrixRightNativeCall.budget r := by
    unfold cost fuel width MatrixRightNativeCall.params
    rw [MatrixBucketCallBounds.entries_length]
    unfold MatrixRightNativeCall.budget MatrixBucketCallBounds.resetBudget MatrixBatchBucketEndpoints.H
    ring
  rw [ht] at hb bs
  obtain ⟨native,hn,nf,ns,_⟩ := ZeroPadding.run_config machine (MatrixRightNativeCall.driverCaps r) _ _ base hb
  obtain ⟨actual,hact,af,actS,_⟩ := ZeroPadding.run_config machine (MatrixRightNativeCall.caps r) _ _ native hn
  refine ⟨final,hfb,hfu,hfr,hfc,?_,?_,?_,actual,hact,?_,actS.trans_le (ns.trans_le bs)⟩
  · simpa only [ha,MatrixRightNativeCall.params] using hfa
  · rw [hi] at hfi
    convert hfi using 1
    ring
  · simpa only [ha,hi,MatrixRightNativeCall.output] using hfo
  · rw [af,nf,bf]
    rfl

end NearCubicWires.RepairOrdinary.MatrixRightStableLoop
