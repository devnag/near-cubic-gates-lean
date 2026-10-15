import Proof.MachineModel.OrdinaryMemoryCheckerTraceBounds
import Proof.MachineModel.UWalkCapacity
import Proof.MachineModel.ClockDyadicLedger

/-! The exact mathematical store supplied by U's executed initialization
and numeric bootstrap. Its reusable walk invariant follows solely from the
decoded verifier and the input/witness guards; physical focus is external. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape SignedSortKey ClaimedTrace
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def initialLookup (N : ℕ) (v : OrdinaryVerifier) (codePos : ℕ) (scans : List Bool)
    (scanPos : ℕ) : LookupRuntime.Store where
  code := code v
  codePos := codePos
  t := v.tapeCount
  s := v.stateCount
  j := natBitLength v.stateCount
  state := binary (natBitLength v.stateCount) v.machine.start.val
  scans := scans
  scanPos := scanPos
  halt := false
  accept := false
  present := false
  nextState := []
  tags := []
  flag := false
  flagQuery := []
  flagCounter := []
  query := []
  counter := []
  scanCopy := []
  cap := UWalkCapacity.amount (ClockDyadicLedger.width N) v.tapeCount (natBitLength v.stateCount)

def initialStore (N : ℕ) (v : OrdinaryVerifier) (codePos : ℕ) (scans : List Bool)
    (scanPos : ℕ) (input witness : List Bool) (m : ℕ) : Store where
  lookup := initialLookup N v codePos scans scanPos
  tagPos := 0
  head := ⟨0,[],false,.left⟩
  serial := 2*input.length+2*witness.length+2
  tape := 0
  out := MemoryInitialEmission.fields (2*ClockDyadicLedger.width N)
    (2*ClockDyadicLedger.width N+2) (ClockDyadicLedger.width N) 0
    (MemoryInitialization.events input witness)
  read := false
  after := false
  array := ZeroPadding.pad
    (UWalkCapacity.amount (ClockDyadicLedger.width N) v.tapeCount (natBitLength v.stateCount))
    ((List.ofFn fun _ : Fin v.tapeCount => frame (binary (ClockDyadicLedger.width N) 0)).flatten)
  arrayOut := List.replicate
    (UWalkCapacity.amount (ClockDyadicLedger.width N) v.tapeCount (natBitLength v.stateCount)) false
  w := ClockDyadicLedger.width N
  cap := UWalkCapacity.amount (ClockDyadicLedger.width N) v.tapeCount (natBitLength v.stateCount)
  C := UWalkCapacity.amount (ClockDyadicLedger.width N) v.tapeCount (natBitLength v.stateCount)
  m := m
  index := 0
  countFlag := false

theorem initial_canonical (N : ℕ) (v : OrdinaryVerifier) (codePos : ℕ) (scans : List Bool)
    (scanPos : ℕ) : LookupRuntime.Canonical (initialLookup N v codePos scans scanPos) v v.machine.start :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem guarded_scalar_bounds (N n B m t c : ℕ) (hN : 2 ≤ N)
    (hn : n ≤ B) (hB : B ≤ ClockDyadicLedger.limit N) (hm : m ≤ B)
    (ht : t ≤ c) (hc : c ≤ Nat.log 2 N) :
    m+1 < 2^ClockDyadicLedger.width N ∧ t < 2^ClockDyadicLedger.width N ∧
    2*n < 2^ClockDyadicLedger.width N ∧ 2*B < 2^ClockDyadicLedger.width N ∧
    PCPResourceLedger.events n B m t < 2^(2*ClockDyadicLedger.width N) := by
  have hNL : N ≤ ClockDyadicLedger.limit N :=
    (Nat.le_self_pow (by simp [PowerSlice.degree]) N).trans
      (ClockDyadicLedger.limit_bounds N (by omega)).1
  have hce : c ≤ PCPResourceLedger.ell N := hc.trans
    ((Nat.log_mono_right (Nat.le_succ N)).trans (Nat.log_le_clog 2 (N+1)))
  have heN : PCPResourceLedger.ell N ≤ N := by
    apply Nat.clog_le_of_le_pow
    exact Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hcL := hce.trans (heN.trans hNL)
  have hw := (ClockDyadicLedger.width_bounds N).1
  have hE := (ClockDyadicLedger.guarded_bounds N n B m t c hN hn hB hm ht hc).1
  exact ⟨by omega,by omega,by omega,by omega,hE⟩

theorem initial_ready (N : ℕ) (v : OrdinaryVerifier) (codePos : ℕ) (scans : List Bool)
    (scanPos : ℕ) (input witness : List Bool) (m : ℕ)
    (hN : 2 ≤ N) (hn : input.length ≤ witness.length)
    (hB : witness.length ≤ ClockDyadicLedger.limit N) (hm : m ≤ witness.length)
    (hc : (code v).length ≤ Nat.log 2 N) (hpos : codePos ≤ 2*(code v).length+1) :
    Ready (initialStore N v codePos scans scanPos input witness m) v
      (view (initialConfiguration v.machine (v.inputTapes input witness))) := by
  have ht := tapes_le_code_length v
  obtain ⟨hmw,htw,_,_,hE⟩ := guarded_scalar_bounds N input.length witness.length m
    v.tapeCount (code v).length hN hn hB hm ht hc
  obtain ⟨harray,hhead,hlookup⟩ := UWalkCapacity.amount_bounds (ClockDyadicLedger.width N)
    v.tapeCount (natBitLength v.stateCount)
  refine ⟨?_,initial_canonical N v codePos scans scanPos,?_,?_,rfl,htw,?_,?_,?_,hhead,?_,rfl,rfl⟩
  · refine ⟨rfl,hpos,hlookup,?_,?_,?_,?_,?_,?_,?_⟩ <;> exact Nat.zero_le _
  · change m < 2^ClockDyadicLedger.width N
    omega
  · exact Nat.zero_le _
  · change 2*input.length+2*witness.length+2+(m-0)*v.tapeCount < 2^(2*ClockDyadicLedger.width N)
    simpa only [PCPResourceLedger.events, Nat.sub_zero, Nat.mul_comm m v.tapeCount] using hE
  · intro i
    change 0+(m-0)+1 < 2^ClockDyadicLedger.width N
    simpa only [Nat.sub_zero, Nat.zero_add] using hmw
  · exact Nat.zero_le _
  · change TransitionArray.loopBudget (ClockDyadicLedger.width N) v.tapeCount ≤
      UWalkCapacity.amount (ClockDyadicLedger.width N) v.tapeCount (natBitLength v.stateCount)
    simpa only [TransitionArray.loopBudget, TransitionArray.bodyBudget, Nat.add_assoc] using harray

theorem initial_serial (N : ℕ) (v : OrdinaryVerifier) (codePos : ℕ) (scans : List Bool)
    (scanPos : ℕ) (input witness : List Bool) (m : ℕ) :
    (initialStore N v codePos scans scanPos input witness m).serial =
      (MemoryInitialization.events input witness).length :=
  (MemoryInitialization.initial_count input witness).symm

end NearCubicWires.RepairOrdinary.TransitionWalk
