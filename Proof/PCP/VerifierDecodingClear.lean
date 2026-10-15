import Proof.PCP.VerifierDecodingUnaryFrame

/-! Paid reuse of a bounded dimension counter as zero workspace. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.ClearMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem erase_mark (cap k : ℕ) (hk : k < cap) :
    writeTapeBit (CapMachine.counter cap (k+1)) (k+1) false = CapMachine.counter cap k := by
  have ha : cap+2-((k+1)+1) = cap-k := by omega
  have hb : cap+2-(k+1) = cap-k+1 := by omega
  simp only [CapMachine.counter,ZeroPadding.pad,List.length_cons,List.length_replicate,ha,hb,List.cons_append]
  change false::writeTapeBit (List.replicate (k+1) true ++ List.replicate (cap-k) false) k false = _
  rw [Streaming.erase_counter]

def cfg (state : Fin 3) (cap value head : ℕ) : Configuration 1 3 :=
  ⟨state,fun _ => head,fun _ => CapMachine.counter cap value⟩
def action (next : Fin 3) (move : HeadMove) (write : Option Bool := none) : Action 1 3 :=
  ⟨next,fun _ => write,fun _ => move⟩
def machine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val = 2
  rule := fun state bits =>
    ![some (action 1 .left),some (if bits 0 then action 1 .left (some false) else action 2 .right),none] state

@[simp] theorem cfg_cells (state : Fin 3) (cap value head : ℕ) (hv : value ≤ cap) :
    (cfg state cap value head).tapeCells = cap+2 := by
  simp [cfg,Configuration.tapeCells,CapMachine.counter_length _ _ hv]

theorem start_step (cap value : ℕ) :
    step machine (cfg 0 cap value (value+1)) = some (cfg 1 cap value value) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,action,HeadMove.apply]
  · rfl

theorem erase_step (cap k : ℕ) (hk : k < cap) :
    step machine (cfg 1 cap (k+1) (k+1)) = some (cfg 1 cap k k) := by
  simp [step,machine,cfg,Configuration.scanned,CapMachine.counter_read]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,action,HeadMove.apply]
  · funext i; simp [applyAction,action,erase_mark cap k hk]

theorem stop_step (cap : ℕ) :
    step machine (cfg 1 cap 0 0) = some (cfg 2 cap 0 1) := by
  simp [step,machine,cfg,Configuration.scanned,CapMachine.counter_zero]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,action,HeadMove.apply]
  · rfl

theorem erase_prefix (cap value : ℕ) (hv : value ≤ cap) :
    Prefix machine (cap+2) (value+1) (cfg 1 cap value value) (cfg 2 cap 0 1) := by
  induction value with
  | zero => exact Prefix.step (by simp) (by rfl) (stop_step cap) (Prefix.refl _ (by simp))
  | succ value ih =>
    exact Prefix.step (by simp [hv]) (by rfl)
      (erase_step cap value (by omega)) (ih (by omega))

theorem clear_run (cap value : ℕ) (hv : value ≤ cap) :
    ∃ receipt : ExecutionReceipt 1 3,
      runFrom machine (value+2) (cfg 0 cap value (value+1)) = some receipt ∧
      receipt.final = cfg 2 cap 0 1 ∧ receipt.steps = value+2 ∧ receipt.peakTapeCells ≤ cap+2 := by
  exact (Prefix.step (by simp [hv]) (by rfl) (start_step cap value) (erase_prefix cap value hv)).run
    (by rfl) (by simp)

end NearCubicWires.RepairSource.VerifierDecoding.ClearMachine
