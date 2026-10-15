import Proof.Hierarchy.CompetitorSameBucketPairEmitAppend

/-! Actual guarded pair contribution. The emitted signed key is selected
by the physical classifier result; all branch/return transitions are paid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketPairEmit
open LocalBitMultitape SignedSortKey MatrixScoreBatch RecoveryExecution RecoveryRootRound
open CompetitorSameBucketPairFields (data)
open CompetitorSameBucketPairCompare (fires)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : ℕ} (_ : Machine t s) := s
noncomputable def sizes : Fin 2 → ℕ := ![stateCount classify,stateCount append]
noncomputable def programs : (j : Fin 2) → Machine 36 (sizes j)
  | ⟨0,_⟩ => classify
  | ⟨1,_⟩ => append
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (bits : Fin 36 → Bool) : Option (Fin 2) :=
  if j=0 ∧ bits 29 then some 1 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def budget (s k p : ℕ) := CompetitorSameBucketPairGuard.budget s k+(4*p+8*k+17)+2

def output (p k u a b ra rb : ℕ) (coefficient : ℤ) (out : List Bool) :=
  if fires u a b ra rb then out++CompetitorSameBucketKeyAppend.word p k coefficient a b else out

theorem present_run (cap s k u p : ℕ) (sa sb coefficient : ℤ) (a b ra rb : ℕ) (out : List Bool)
    (hc : 30*(k+s+2)≤cap) (hu : u<2^k) (ha : a<2^k) (hb : b<2^k)
    (hra : ra<2^(k+s+1)) (hrb : rb<2^(k+s+1)) (hp : 2*(p+1)≤cap) :
    ∃ r,runFrom machine (budget s k p) (cfg machine.start (data cap s k u sa sb a b ra rb 0) cap p k coefficient out)=some r ∧
      r.final.heads=heads (output p k u a b ra rb coefficient out) ∧
      r.final.tapes=(cfg machine.start (data cap s k u sa sb a b ra rb 3) cap p k coefficient
        (output p k u a b ra rb coefficient out)).tapes ∧ r.steps≤budget s k p := by
  obtain ⟨base,hbase,bh,bt,_⟩ := classify_present cap s k u p sa sb coefficient a b ra rb out hc hu ha hb hra hrb
  have flag : base.final.scanned 29=fires u a b ra rb := by
    simp only [Configuration.scanned,bh,bt,heads]
    change readTapeBit (ZeroPadding.pad cap [fires u a b ra rb]) 0=_
    exact ZeroPadding.read_pad cap [fires u a b ra rb] 0
  cases hfire : fires u a b ra rb with
  | false =>
    obtain ⟨n,hn,path⟩ := stop_receipt sizes programs 0 next 0 (CompetitorSameBucketPairGuard.budget s k)
      (cfg classify.start (data cap s k u sa sb a b ra rb 0) cap p k coefficient out) base hbase
      (by simp [next]; exact flag.trans hfire)
    obtain ⟨actual,hr,hf,hs⟩ := path.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have bound : n≤budget s k p := by unfold budget; omega
    have hr' : runFrom machine n (cfg machine.start (data cap s k u sa sb a b ra rb 0) cap p k coefficient out)=some actual := hr
    have hm := runFrom_moreFuel machine n (budget s k p-n) _ actual hr'
    rw [Nat.add_sub_of_le bound] at hm
    refine ⟨actual,hm,?_,?_,hs.le.trans bound⟩
    · rw [hf]
      change base.final.heads=heads (output p k u a b ra rb coefficient out)
      simpa only [output,hfire,Bool.false_eq_true,ite_false] using bh
    · rw [hf]
      change base.final.tapes=(cfg classify.start (data cap s k u sa sb a b ra rb 3) cap p k coefficient (output p k u a b ra rb coefficient out)).tapes
      simpa only [output,hfire,Bool.false_eq_true,ite_false] using bt
  | true =>
    obtain ⟨last,hl,lh,lt,_⟩ := append_run cap s k u p sa sb coefficient a b ra rb out hp (by omega)
    have he : RecoveryCalls.restarted append (heads out) base.final.tapes=
        cfg append.start (data cap s k u sa sb a b ra rb 3) cap p k coefficient out := by
      apply configuration_ext
      · rfl
      · rfl
      · exact bt
    rw [←he] at hl
    obtain ⟨n0,hn0,path0⟩ := call_receipt sizes programs 0 next 0 1 (CompetitorSameBucketPairGuard.budget s k)
      (cfg classify.start (data cap s k u sa sb a b ra rb 0) cap p k coefficient out) base hbase
      (by simp [next]; exact flag.trans hfire)
    rw [bh] at path0
    obtain ⟨n1,hn1,path1⟩ := stop_receipt sizes programs 0 next 1 (4*p+8*k+17)
      (RecoveryCalls.restarted append (heads out) base.final.tapes) last hl (by simp [next])
    have path := path0.trans path1
    obtain ⟨actual,hr,hf,hs⟩ := path.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have bound : n0+n1≤budget s k p := by unfold budget; omega
    have hr' : runFrom machine (n0+n1) (cfg machine.start (data cap s k u sa sb a b ra rb 0) cap p k coefficient out)=some actual := hr
    have hm := runFrom_moreFuel machine (n0+n1) (budget s k p-(n0+n1)) _ actual hr'
    rw [Nat.add_sub_of_le bound] at hm
    refine ⟨actual,hm,?_,?_,hs.le.trans bound⟩
    · rw [hf]
      change last.final.heads=heads (output p k u a b ra rb coefficient out)
      simpa only [output,hfire,ite_true] using lh
    · rw [hf]
      change last.final.tapes=(cfg append.start (data cap s k u sa sb a b ra rb 3) cap p k coefficient (output p k u a b ra rb coefficient out)).tapes
      simpa only [output,hfire,ite_true] using lt

theorem absent_run (work : Fin 31 → List Bool) (cap p k : ℕ) (coefficient : ℤ) (out : List Bool)
    (habsent : work 0=List.replicate cap false ∨ work 13=List.replicate cap false)
    (hflag : readTapeBit (work 29) 0=false) :
    ∃ r,runFrom machine 2 (cfg machine.start work cap p k coefficient out)=some r ∧
      r.final.heads=heads out ∧ r.final.tapes=(cfg machine.start work cap p k coefficient out).tapes ∧ r.steps≤2 := by
  obtain ⟨base,hbase,bh,bt,_⟩ := classify_absent work cap p k coefficient out habsent
  have flag : base.final.scanned 29=false := by
    simp only [Configuration.scanned,bh,bt,heads]
    exact hflag
  obtain ⟨n,hn,path⟩ := stop_receipt sizes programs 0 next 0 1 (cfg classify.start work cap p k coefficient out) base hbase
    (by simp [next]; exact flag)
  obtain ⟨actual,hr,hf,hs⟩ := path.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hr' : runFrom machine n (cfg machine.start work cap p k coefficient out)=some actual := hr
  have hm := runFrom_moreFuel machine n (2-n) _ actual hr'
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨actual,hm,?_,?_,hs.le.trans hn⟩
  · rw [hf]
    exact bh
  · rw [hf]
    exact bt

theorem budget_eq (s k p : ℕ) : budget s k p=100*(k+s+1)+32*k+4*p+133 := by
  unfold budget CompetitorSameBucketPairGuard.budget CompetitorSameBucketPairFields.budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketPairEmit
