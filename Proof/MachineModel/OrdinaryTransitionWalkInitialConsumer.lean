import Proof.MachineModel.OrdinaryTransitionWalkInitial

/-! Direct consumers of the guarded initial store: exact raw-checker input
for every successful literal evaluation, and the actual walk's paid budget
in the fixed-U resource ledger's event-count and short-width currency. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape SignedSortKey ClaimedTrace MemoryLog
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem initial_evaluation_ready (N : ℕ) (v : OrdinaryVerifier)
    (input witness : List Bool) (m : ℕ) (bits : List Bool)
    (finalView : View v.tapeCount v.stateCount) (trace : List Event)
    (hN : 2 ≤ N) (hn : input.length ≤ witness.length)
    (hB : witness.length ≤ ClockDyadicLedger.limit N) (hm : m ≤ witness.length)
    (hc : (code v).length ≤ Nat.log 2 N)
    (heval : evaluate v (view (initialConfiguration v.machine (v.inputTapes input witness))) m bits =
      some (finalView,trace)) :
    MemoryChecker.ListReady (2*ClockDyadicLedger.width N) (ClockDyadicLedger.width N)
      (MemoryInitialization.events input witness ++ trace) := by
  obtain ⟨claims,_,hlen,_,hcheck⟩ := evaluate_implies_trace v m _ bits finalView trace heval
  obtain ⟨hmw,htw,hnw,hBw,hE⟩ := guarded_scalar_bounds N input.length witness.length m
    v.tapeCount (code v).length hN hn hB hm (tapes_le_code_length v) hc
  apply MemoryChecker.initialized_ready v input witness claims finalView trace
    (ClockDyadicLedger.width N) hcheck
  · rw [hlen]
    exact hE.le
  · exact htw.le
  · exact hnw
  · exact hBw
  · rw [hlen]
    omega

theorem initial_event_input (N : ℕ) (v : OrdinaryVerifier) (codePos : ℕ) (scans : List Bool)
    (scanPos : ℕ) (input witness : List Bool) (m : ℕ) (trace : List Event)
    (hready : MemoryChecker.ListReady (2*ClockDyadicLedger.width N) (ClockDyadicLedger.width N)
      (MemoryInitialization.events input witness ++ trace)) :
    let d := initialStore N v codePos scans scanPos input witness m
    (d.out ++ MemoryInitialEmission.fields (2*d.w) (2*d.w+2) d.w d.serial trace) ++ [false] =
      (MemoryChecker.listRequest hready).input := by
  dsimp only
  change (MemoryInitialEmission.fields (2*ClockDyadicLedger.width N) (2*ClockDyadicLedger.width N+2)
      (ClockDyadicLedger.width N) 0 (MemoryInitialization.events input witness) ++
    MemoryInitialEmission.fields (2*ClockDyadicLedger.width N) (2*ClockDyadicLedger.width N+2)
      (ClockDyadicLedger.width N) (2*input.length+2*witness.length+2) trace) ++ [false] = _
  rw [← MemoryInitialization.initial_count input witness]
  exact MemoryChecker.initialized_input input witness trace hready

theorem initial_cycle_bound (N : ℕ) (v : OrdinaryVerifier) (codePos : ℕ) (scans : List Bool)
    (scanPos : ℕ) (input witness : List Bool) (m : ℕ) :
    cycleBudget (initialStore N v codePos scans scanPos input witness m) ≤
      2048*(ClockDyadicLedger.width N+(code v).length+1)^2 := by
  obtain ⟨ht,_,hj,_,_⟩ := (initial_canonical N v codePos scans scanPos).dimensions (fun _ => false)
  change v.tapeCount ≤ (code v).length at ht
  change natBitLength v.stateCount ≤ (code v).length at hj
  have hC := UWalkCapacity.amount_short (ClockDyadicLedger.width N) v.tapeCount
    (natBitLength v.stateCount) (code v).length ht hj
  change 256*((code v).length+1)^2 +
    4*UWalkCapacity.amount (ClockDyadicLedger.width N) v.tapeCount (natBitLength v.stateCount) +
    64*(ClockDyadicLedger.width N+(code v).length+1) ≤ _
  nlinarith [sq_nonneg (ClockDyadicLedger.width N), sq_nonneg ((code v).length)]

theorem initial_walk_budget (N : ℕ) (v : OrdinaryVerifier) (codePos : ℕ) (scans : List Bool)
    (scanPos : ℕ) (input witness : List Bool) (m : ℕ) :
    (m+1)*cycleBudget (initialStore N v codePos scans scanPos input witness m) ≤
      2048*(PCPResourceLedger.events input.length witness.length m v.tapeCount+1)*
        (ClockDyadicLedger.width N+(code v).length+1)^2 := by
  have hcycle := initial_cycle_bound N v codePos scans scanPos input witness m
  have hm : m+1 ≤ PCPResourceLedger.events input.length witness.length m v.tapeCount+1 := by
    have ht := v.twoTapes
    dsimp only [PCPResourceLedger.events]
    nlinarith
  have hb := Nat.mul_le_mul hm hcycle
  simpa only [Nat.mul_assoc, Nat.mul_left_comm _ 2048] using hb

end NearCubicWires.RepairOrdinary.TransitionWalk
