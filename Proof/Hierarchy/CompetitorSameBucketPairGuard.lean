import Proof.Hierarchy.CompetitorSameBucketPairFields

/-! The actual first-marker guard skips absent padded records before either
record decoder runs. Its branch and final return are paid transitions. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketPairGuard
open LocalBitMultitape SignedSortKey RecoveryRootRound RecoveryExecution
open CompetitorSameBucketPairFields (data)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def gate : Machine 31 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
private abbrev stateCount {t s : ℕ} (_ : Machine t s) := s
noncomputable def sizes : Fin 2 → ℕ := ![1,stateCount CompetitorSameBucketPairFields.machine]
noncomputable def programs : (j : Fin 2) → Machine 31 (sizes j)
  | ⟨0,_⟩ => gate
  | ⟨1,_⟩ => CompetitorSameBucketPairFields.machine
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (bits : Fin 31 → Bool) : Option (Fin 2) :=
  if j=0 ∧ bits 0 && bits 13 then some 1 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem source_present (cap s k : ℕ) (score : ℤ) (id rank : ℕ) :
    readTapeBit (ZeroPadding.pad cap (CompetitorSameBucketRankFields.source s k score id rank)) 0=true := by
  rw [ZeroPadding.read_pad]
  have hn : KeyLoop.word s k (score,id,rank)++binary (k+s+1) rank≠[] := by
    intro he
    have hl := congrArg List.length he
    simp only [List.length_append,KeyLoop.word_length,binary_length,List.length_nil] at hl
    omega
  obtain ⟨bit,bits,hbits⟩ := List.exists_cons_of_ne_nil hn
  simp only [CompetitorSameBucketRankFields.source,hbits]
  rfl

theorem absent_ready (ambient : Fin 31 → List Bool)
    (habsent : (readTapeBit (ambient 0) 0 && readTapeBit (ambient 13) 0)=false) :
    ClockJoin.ReadyRun machine 1 ambient ambient := by
  have hstep := RecoveryCalls.stop_step sizes programs 0 next 0
    (initialConfiguration gate ambient) (by rfl) (by simpa [next,Configuration.scanned,initialConfiguration] using habsent)
  have path := Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hstep
  obtain ⟨actual,hr,hf,hs⟩ := path.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨actual,hr,congrArg Configuration.tapes hf,by intro i; rw [hf]; rfl,hs.le⟩

theorem absent_zeros_ready (ambient : Fin 31 → List Bool) (cap : ℕ)
    (habsent : ambient 0=List.replicate cap false ∨ ambient 13=List.replicate cap false) :
    ClockJoin.ReadyRun machine 1 ambient ambient := by
  apply absent_ready
  rcases habsent with h|h
  · rw [h,Streaming.read_zeros]
    rfl
  · rw [h,Streaming.read_zeros]
    exact Bool.and_false _

def budget (s k : ℕ) := CompetitorSameBucketPairFields.budget s k+2

theorem present_ready (cap s k u : ℕ) (sa sb : ℤ) (a b ra rb : ℕ)
    (hc : 30*(k+s+2)≤cap) (hu : u<2^k) (ha : a<2^k) (hb : b<2^k)
    (hra : ra<2^(k+s+1)) (hrb : rb<2^(k+s+1)) :
    ClockJoin.ReadyRun machine (budget s k) (data cap s k u sa sb a b ra rb 0)
      (data cap s k u sa sb a b ra rb 3) := by
  have h0 : readTapeBit (data cap s k u sa sb a b ra rb 0 0) 0=true := source_present cap s k sa a ra
  have h13 : readTapeBit (data cap s k u sa sb a b ra rb 0 13) 0=true := source_present cap s k sb b rb
  have hstep := RecoveryCalls.return_step sizes programs 0 next 0 1
    (initialConfiguration gate (data cap s k u sa sb a b ra rb 0)) (by rfl)
    (by simp [next,Configuration.scanned,initialConfiguration,h0,h13])
  have first := Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hstep
  obtain ⟨base,hb,bt,bh,_⟩ := CompetitorSameBucketPairFields.present_ready cap s k u sa sb a b ra rb hc hu ha hb hra hrb
  obtain ⟨n,hn,last⟩ := stop_receipt sizes programs 0 next 1 (CompetitorSameBucketPairFields.budget s k)
    (initialConfiguration CompetitorSameBucketPairFields.machine (data cap s k u sa sb a b ra rb 0)) base hb
    (by simp [next])
  have path := first.trans last
  obtain ⟨actual,hr,hf,hs⟩ := path.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have ht : 1+n≤budget s k := by unfold budget; omega
  have hr' : runFrom machine (1+n) (initialConfiguration machine (data cap s k u sa sb a b ra rb 0))=some actual := hr
  have hm := runFrom_moreFuel machine (1+n) (budget s k-(1+n)) _ actual hr'
  rw [Nat.add_sub_of_le ht] at hm
  refine ⟨actual,hm,?_,?_,hs.le.trans ht⟩
  · rw [hf]
    exact bt
  · intro i
    rw [hf]
    exact bh i

end NearCubicWires.RepairOrdinary.CompetitorSameBucketPairGuard
