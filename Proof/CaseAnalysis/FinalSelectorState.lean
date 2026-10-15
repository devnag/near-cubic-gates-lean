import Proof.CaseAnalysis.RowsTouchingSelectorOutput
import Proof.CaseAnalysis.RowsTouchingLiveCountMath

/-! A.4 cold start, part 1: the blank entry state of the deterministic
touching selector, and the exact paper live count it must carry.

`Selector.loop_run` is quantified over an arbitrary `initial : State q`
subject to `Valid w P 0 initial`, `initial.selected = ∅` and
`initial.k = K`.  This file pins the ONE blank state that a cold machine
can actually leave behind (every private field empty, both score
accumulators zero, no carry), discharges those three premises, and fixes
`K` to the paper's `normalizedLiveCount`, which for a fixed scale 1 and
`2 ≤ q` is exactly the physically computable `Nat.clog 2 (q+2)`. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalSelector
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
open CloseoutRowsTouching CloseoutRowsGateSupport
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ### The blank state -/

def coldGate : Gate.Store:=⟨fun _=>[],[],[],[],0,0⟩
def coldStore : Coordinate.Store:=⟨coldGate,[],[],false,false⟩
def coldState (q K : ℕ) : Selector.State q:=⟨∅,K,q-K,coldStore⟩

theorem cold_gate_valid (q w P : ℕ):Gate.Valid q w P coldGate:=
  ⟨fun _=>Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩

theorem cold_store_valid (q w P : ℕ):Coordinate.Valid q w P coldStore:=
  ⟨cold_gate_valid q w P,Nat.zero_le _,Nat.zero_le _⟩

theorem cold_selected (q K : ℕ):(coldState q K).selected=(∅ : Finset (Fin q)):=rfl
theorem cold_k (q K : ℕ):(coldState q K).k=K:=rfl
theorem cold_h (q K : ℕ):(coldState q K).h=q-K:=rfl

theorem cold_valid {q : ℕ} (K w P : ℕ) (hK:K≤q):Selector.Valid w P 0 (coldState q K):=by
  refine ⟨?_,cold_store_valid q w P,rfl,rfl,fun _=>rfl⟩
  change K+(q-K)=q-0
  omega

/-! ### The paper live count is physically computable -/

theorem pow_gap (n : ℕ):n+3<2^(n+2):=by
  induction n with
  | zero=>decide
  | succ m ih=>
    have h:1≤(2:ℕ)^(m+2):=Nat.one_le_two_pow
    have e:(2:ℕ)^(m+1+2)=2^(m+2)*2:=by ring
    omega

theorem bitlength_le (q : ℕ) (hq:2≤q):natBitLength (q+1)≤q:=by
  have h:=pow_gap (q-2)
  have e:q-2+3=q+1:=by omega
  have e2:q-2+2=q:=by omega
  rw [e,e2] at h
  have hl:Nat.log 2 (q+1)<q:=Nat.log_lt_of_lt_pow (by omega) h
  change Nat.log 2 (q+1)+1≤q
  omega

theorem cold_count_le (q kappa : ℕ):SupplierEstimator.normalizedLiveCount q kappa≤q:=by
  rw [LiveCount.live_count]
  exact Nat.min_le_left _ _

/-- With the fixed scale 1 the paper's normalized live count is exactly the
ceiling logarithm produced by the accepted `CloseoutSchedule.Clog` machine. -/
theorem cold_count (q : ℕ) (hq:2≤q):SupplierEstimator.normalizedLiveCount q 1=Nat.clog 2 (q+2):=by
  rw [LiveCount.live_count,Nat.one_mul,Nat.min_eq_right (bitlength_le q hq)]
  exact (LiveCount.logarithm q).symm

/-! ### The selector, started cold -/

theorem cold_loop_run {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P C D E : ℕ)
    (tail : List Bool) (hK:K≤q)
    (hwidth:q+G+1≤w) (hprod:2*q+G≤w) (hP:q+1≤P)
    (hC:P+1≤C) (hScan:2*q+3≤C) (hW:2*w+3≤C)
    (hLookup:Lookup.budget (PascalReady.width q) (q+1) q q+2≤C)
    (hD:GateFold.budget q w P G≤D) (hE:4*q+3≤E):
    ∃ r,runFrom Selector.machine (Selector.budget q G w P)
      (RepeatMachine.cfg 0 (Selector.entry support K w P C D E (coldState q K) tail 0 []) q 1)=some r ∧
      r.final=RepeatMachine.cfg 3
        (Selector.entry support K w P C D E (coldState q K) tail q []) q 1 ∧
      r.steps≤Selector.budget q G w P:=
  Selector.loop_run support K w P C D E (coldState q K) tail (cold_valid K w P hK)
    hwidth hprod hP hC hScan hW hLookup hD hE

theorem cold_final_mask {q G : ℕ} (support : Fin G→Finset (Fin q)) (K w P C D E : ℕ)
    (tail : List Bool) (hP:q+1≤P) (hK:K≤q):
    (RepeatMachine.cfg 3 (Selector.entry support K w P C D E (coldState q K) tail q []) q 1).tapes
        ((1 : Fin 35).castAdd 1)=gateMembers (SupplierTouching.touchingSelect support K):=
  Selector.final_mask support K w P C D E (coldState q K) tail hP (cold_valid K w P hK) rfl rfl

end NearCubicWires.RepairOrdinary.CloseoutFinalSelector
