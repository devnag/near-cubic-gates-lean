import Proof.PCP.VerifierDecodingReady

/-! The existing decoder's rejecting path stops before width/table work.
This sharper all-input bound is needed at the ordinary U entry: a long
malformed code costs a linear scan even when its physical limit is small. -/
namespace NearCubicWires.RepairSource.VerifierDecoding
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Dimensions
theorem rejected_prefix (word : List Bool) (limit : ℕ)
    (hv : GuardedPreparation.valid word limit=false) :
    ∃ n final, n≤12*word.length+28 ∧ Timed machine n (initial word limit) final ∧
      machine.halted final.control=true ∧ final.scanned 5=false := by
  obtain ⟨n,base,hn,hguard,hh,hout⟩ := GuardedPreparation.guarded_prefix word limit
  obtain ⟨r,hr,hf,hs⟩ := hguard.run hh
  have he := TapeEmbedding.run_embed GuardedPreparation.machine (fun _ : Fin 5 => 0)
    (fun _ : Fin 5 => []) _ _ r hr
  let first := TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) r
  have htime : first.steps=n := hs
  have hbit : first.final.scanned 5=false := by
    change readTapeBit (r.final.tapes 5) (r.final.heads 5)=_
    rw [hf]
    exact hout.1.trans hv
  have hp := stop_prefix 0 n _ first he (by simp [next]; exact hbit)
  rw [htime] at hp
  refine ⟨_,_,by omega,hp,?_,?_⟩
  · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
  · simpa only [RecoveryCalls.stopped,Configuration.scanned] using hbit
end Dimensions

namespace Front
theorem rejected_prefix (word : List Bool) (limit : ℕ)
    (hv : GuardedPreparation.valid word limit=false) :
    ∃ n final, n≤12*word.length+29 ∧ Timed machine n (initial word limit) final ∧
      machine.halted final.control=true ∧ final.scanned 12=false := by
  obtain ⟨n,base,hn,hdim,hh,hout⟩ := Dimensions.rejected_prefix word limit hv
  obtain ⟨r,hr,hf,hs⟩ := hdim.run hh
  have he := TapeEmbedding.run_embed Dimensions.machine (fun _ : Fin 3 => 0)
    ![[],[false],[]] _ _ r hr
  let first := TapeEmbedding.receipt (fun _ : Fin 3 => 0) ![[],[false],[]] r
  have htime : first.steps=n := hs
  have hbit : first.final.scanned 5=false := by
    change readTapeBit (r.final.tapes 5) (r.final.heads 5)=_
    rw [hf]
    exact hout
  have hp := stop_prefix 0 n _ first he (by simp [next]; exact hbit)
  rw [htime] at hp
  refine ⟨_,_,by omega,hp,?_,?_⟩
  · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
  · simp [RecoveryCalls.stopped,Configuration.scanned,first,TapeEmbedding.receipt,
      TapeEmbedding.config,Fin.addCases,readTapeBit]
end Front

namespace Whole
theorem rejected_prefix (word : List Bool) (limit : ℕ)
    (hv : GuardedPreparation.valid word limit=false) :
    ∃ n final, n≤12*word.length+32 ∧ Timed machine n (initial word limit) final ∧
      machine.halted final.control=true ∧ final.scanned 19=false := by
  obtain ⟨n,base,hn,hfront,hh,hout⟩ := Front.rejected_prefix word limit hv
  obtain ⟨r,hr,hf,hs⟩ := hfront.run hh
  have he := TapeEmbedding.run_embed Front.machine (fun _ : Fin 6 => 0)
    (FrontTable.extras word.length) _ _ r hr
  let first := TapeEmbedding.receipt (fun _ : Fin 6 => 0) (FrontTable.extras word.length) r
  have htime : first.steps=n := hs
  have hbit : first.final.scanned 12=false := by
    change readTapeBit (r.final.tapes 12) (r.final.heads 12)=_
    rw [hf]
    exact hout
  have hp := call_prefix 0 4 n _ first he (by simp [next]; exact hbit)
  have hall := hp.trans (reject_tail first.final.heads first.final.tapes)
  refine ⟨_,_,?_,hall,?_,rejected_bit _ _⟩
  · rw [htime]; omega
  · simp [machine,RecoveryCalls.machine,rejected,RecoveryCalls.stopped]
end Whole

namespace Ready
theorem rejected_prefix (word : List Bool) (limit : ℕ)
    (hv : GuardedPreparation.valid word limit=false) :
    ∃ n final, n≤12*word.length+33 ∧ Timed machine n (initial word limit) final ∧
      machine.halted final.control=true ∧ Outcome word limit final := by
  obtain ⟨n,base,hn,hwhole,hh,hout⟩ := Whole.rejected_prefix word limit hv
  obtain ⟨r,hr,hf,hs⟩ := hwhole.run hh
  have he := TapeEmbedding.run_embed Whole.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => []) _ _ r hr
  let first := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) r
  have htime : first.steps=n := hs
  have hbit : first.final.scanned 19=false := by
    change readTapeBit (r.final.tapes 19) (r.final.heads 19)=_
    rw [hf]
    exact hout
  have hp := stop_prefix 0 n _ first he (by simp [next]; exact hbit)
  rw [htime] at hp
  have hvalid : Whole.valid word limit=false := by simp [Whole.valid,Front.valid,hv]
  refine ⟨_,_,by omega,hp,?_,?_,by simp [hvalid]⟩
  · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
  · simpa only [RecoveryCalls.stopped,Configuration.scanned,hvalid] using hbit

def limitedBudget (c limit : ℕ) : ℕ := 128*(c+1)*(limit+1)

theorem limited_prefix (word : List Bool) (limit : ℕ) :
    ∃ n final, n≤limitedBudget word.length limit ∧ Timed machine n (initial word limit) final ∧
      machine.halted final.control=true ∧ Outcome word limit final := by
  by_cases hc : word.length≤limit
  · obtain ⟨n,final,hn,hp,hh,hout⟩ := ready_prefix word limit
    refine ⟨n,final,hn.trans ?_,hp,hh,hout⟩
    dsimp [budget,limitedBudget]
    nlinarith
  · have hv : GuardedPreparation.valid word limit=false := by simp [GuardedPreparation.valid,hc]
    obtain ⟨n,final,hn,hp,hh,hout⟩ := rejected_prefix word limit hv
    refine ⟨n,final,hn.trans ?_,hp,hh,hout⟩
    dsimp [limitedBudget]
    nlinarith

theorem limited_run (N : ℕ) (word : List Bool) :
    ∃ r, runFrom machine (limitedBudget word.length (Nat.log 2 N))
        (blankEntry word (Nat.log 2 N))=some r ∧
      r.steps≤limitedBudget word.length (Nat.log 2 N) ∧
      (r.final.scanned 19=true ↔ ∃ v,decode N word=some v) ∧
      Outcome word (Nat.log 2 N) (ZeroPadding.config (inputCapacity word) r.final) := by
  obtain ⟨n,final,hn,hp,hh,hout⟩ := limited_prefix word (Nat.log 2 N)
  obtain ⟨r,hr,hf,hs⟩ := hp.run hh
  have hi := blank_padding word (Nat.log 2 N)
  rw [←hi] at hr
  obtain ⟨actual,ha,hfa,hsa,_⟩ := ZeroPadding.run_unpad machine (inputCapacity word) _ _ r hr
  have hm := runFrom_moreFuel machine n (limitedBudget word.length (Nat.log 2 N)-n) _ actual ha
  rw [Nat.add_sub_of_le hn] at hm
  have hend : ZeroPadding.config (inputCapacity word) actual.final=final := hfa.trans hf
  have hbit : actual.final.scanned 19=Whole.valid word (Nat.log 2 N) := by
    rw [←ZeroPadding.scanned_config (inputCapacity word) actual.final,hend]
    exact hout.1
  exact ⟨actual,hm,by omega,by rw [hbit,Whole.valid_decode_iff],by rw [hend]; exact hout⟩
end Ready
end NearCubicWires.RepairSource.VerifierDecoding
