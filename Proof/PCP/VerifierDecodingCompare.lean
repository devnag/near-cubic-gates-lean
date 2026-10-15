import Proof.PCP.VerifierDecodingSentinel

/-! Compare physically supplied sentinel unary dimensions. The result lives
in the finite halt state; both tapes and both input heads are restored. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.CompareMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (n : ℕ) := false::List.replicate n true
def cfg (state : Fin 7) (n m head : ℕ) : Configuration 2 7 :=
  ⟨state,fun _ => head,![word n,word m]⟩
def action (next : Fin 7) (move : HeadMove) : Action 2 7 :=
  ⟨next,fun _ => none,fun _ => move⟩
def machine : Machine 2 7 where
  descriptionBits := 0
  start := 0
  halted := fun state => 5 ≤ state.val
  rule := fun state bits =>
    ![some (if bits 0 then if bits 1 then action 0 .right else action 3 .stay else action 1 .stay),
      some (action 2 .left),
      some (if bits 0 then action 2 .left else action 5 .right),
      some (action 4 .left),
      some (if bits 0 then action 4 .left else action 6 .right),none,none] state

@[simp] theorem cfg_cells (state : Fin 7) (n m head : ℕ) :
    (cfg state n m head).tapeCells = n+m+2 := by
  simp [cfg, word, Configuration.tapeCells, Fin.sum_univ_succ]
  omega
@[simp] theorem read_mark (n pos : ℕ) : readTapeBit (word n) (pos+1) = decide (pos < n) :=
  SliceMachine.read_unary n pos
@[simp] theorem read_zero (n : ℕ) : readTapeBit (word n) 0 = false := rfl

theorem scan_step (n m pos : ℕ) (hn : pos < n) (hm : pos < m) :
    step machine (cfg 0 n m (pos+1)) = some (cfg 0 n m (pos+2)) := by
  simp [step, machine, cfg, Configuration.scanned, hn, hm]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, action, HeadMove.apply]
  · rfl

theorem accept_step (n m : ℕ) :
    step machine (cfg 0 n m (n+1)) = some (cfg 1 n m (n+1)) := by
  simp [step, machine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, action, HeadMove.apply]
  · rfl

theorem reject_step (n m : ℕ) (h : m < n) :
    step machine (cfg 0 n m (m+1)) = some (cfg 3 n m (m+1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, action, HeadMove.apply]
  · rfl

theorem scan_prefix (k n m pos : ℕ) (hn : pos+k ≤ n) (hm : pos+k ≤ m) :
    Prefix machine (n+m+2) k (cfg 0 n m (pos+1)) (cfg 0 n m (pos+k+1)) := by
  induction k generalizing pos with
  | zero => simp; exact Prefix.refl _ (by simp)
  | succ k ih =>
    have hj := Prefix.step (by simp) (by rfl) (scan_step n m pos (by omega) (by omega))
      (ih (pos+1) (by omega) (by omega))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj

def rewindState (accept : Bool) : Fin 7 := if accept then 2 else 4
def finalState (accept : Bool) : Fin 7 := if accept then 5 else 6

theorem rewind_start (accept : Bool) (n m k : ℕ) :
    step machine (cfg (if accept then 1 else 3) n m (k+1)) =
      some (cfg (rewindState accept) n m k) := by
  cases accept <;> simp [step, machine, cfg]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction, action, HeadMove.apply]
    · rfl

theorem rewind_step (accept : Bool) (n m k : ℕ) (hk : k < n) :
    step machine (cfg (rewindState accept) n m (k+1)) =
      some (cfg (rewindState accept) n m k) := by
  cases accept <;> simp [step, machine, cfg, rewindState, Configuration.scanned, hk]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction, action, HeadMove.apply]
    · rfl

theorem rewind_stop (accept : Bool) (n m : ℕ) :
    step machine (cfg (rewindState accept) n m 0) = some (cfg (finalState accept) n m 1) := by
  cases accept <;> simp [step, machine, cfg, rewindState, Configuration.scanned]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction, action, HeadMove.apply]
    · rfl

theorem rewind_prefix (accept : Bool) (n m k : ℕ) (hk : k ≤ n) :
    Prefix machine (n+m+2) (k+1) (cfg (rewindState accept) n m k) (cfg (finalState accept) n m 1) := by
  induction k with
  | zero =>
    exact Prefix.step (by simp) (by cases accept <;> rfl) (rewind_stop accept n m) (Prefix.refl _ (by simp))
  | succ k ih =>
    exact Prefix.step (by simp) (by cases accept <;> rfl) (rewind_step accept n m k (by omega)) (ih (by omega))

theorem compare_run (n m : ℕ) :
    ∃ receipt : ExecutionReceipt 2 7,
      runFrom machine (2*min n m+3) (cfg 0 n m 1) = some receipt ∧
      receipt.final = cfg (if n ≤ m then 5 else 6) n m 1 ∧
      receipt.steps = 2*min n m+3 ∧ receipt.peakTapeCells ≤ n+m+2 := by
  have hp := scan_prefix (min n m) n m 0 (by omega) (by omega)
  simp only [Nat.zero_add] at hp
  by_cases h : n ≤ m
  · rw [min_eq_left h] at hp
    have hs := Prefix.step (by simp) (by rfl) (rewind_start true n m n) (rewind_prefix true n m n (Nat.le_refl _))
    have ht := Prefix.step (by simp) (by rfl) (accept_step n m) hs
    obtain ⟨r,hr,hf,hsteps,hpeak⟩ := (hp.trans ht).run (by rfl) (by simp)
    refine ⟨r, ?_, by simpa [h, finalState] using hf, ?_, hpeak⟩
    · have he : n+(n+1+1+1) = 2*n+3 := by omega
      simpa only [min_eq_left h, he] using hr
    · rw [min_eq_left h]; omega
  · rw [min_eq_right (by omega : m ≤ n)] at hp
    have hs := Prefix.step (by simp) (by rfl) (rewind_start false n m m) (rewind_prefix false n m m (by omega))
    have ht := Prefix.step (by simp) (by rfl) (reject_step n m (by omega)) hs
    obtain ⟨r,hr,hf,hsteps,hpeak⟩ := (hp.trans ht).run (by rfl) (by simp)
    refine ⟨r, ?_, by simpa [h, finalState] using hf, ?_, hpeak⟩
    · have he : m+(m+1+1+1) = 2*m+3 := by omega
      simpa only [min_eq_right (by omega : m ≤ n), he] using hr
    · rw [min_eq_right (by omega : m ≤ n)]; omega

end NearCubicWires.RepairSource.VerifierDecoding.CompareMachine
