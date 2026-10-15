import Proof.CaseAnalysis.FinalSupplierTotality
import Proof.CaseAnalysis.FinalOneSidedness
import Proof.Amplification.RecoveryTimedExecution
import Proof.MachineModel.OrdinaryMemoryEffect
import Proof.MachineModel.Runs

namespace NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate

open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness
open RepairOrdinary.RecoveryExecution RepairRepresentation CompetitorRationalGap
open ExtDecompositionBatch

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## The frame's even cells are its unary length track -/

theorem readTapeBit_nil (p : ℕ) : readTapeBit ([] : List Bool) p = false := by
  simp [readTapeBit]

theorem readTapeBit_cons_zero (a : Bool) (l : List Bool) :
    readTapeBit (a :: l) 0 = a := by simp [readTapeBit]

theorem readTapeBit_cons_succ (a : Bool) (l : List Bool) (p : ℕ) :
    readTapeBit (a :: l) (p+1) = readTapeBit l p := by simp [readTapeBit]

theorem frame_nil : frame ([] : List Bool) = [false] := rfl

theorem frame_cons (b : Bool) (bs : List Bool) :
    frame (b :: bs) = true :: b :: frame bs := rfl

theorem frame_even (bs : List Bool) (i : ℕ) :
    readTapeBit (frame bs) (2*i) = decide (i < bs.length) := by
  induction bs generalizing i with
  | nil =>
    cases i with
    | zero =>
      have h0 : (2:ℕ)*0 = 0 := by omega
      rw [h0, frame_nil, readTapeBit_cons_zero]
      simp
    | succ j =>
      have hj : (2:ℕ)*(j+1) = 2*j+1+1 := by omega
      rw [hj, frame_nil, readTapeBit_cons_succ, readTapeBit_nil]
      simp
  | cons b bs ih =>
    cases i with
    | zero =>
      have h0 : (2:ℕ)*0 = 0 := by omega
      rw [h0, frame_cons, readTapeBit_cons_zero]
      simp
    | succ j =>
      have hj : (2:ℕ)*(j+1) = 2*j+1+1 := by omega
      rw [hj, frame_cons, readTapeBit_cons_succ, readTapeBit_cons_succ]
      simpa using ih j

/-- The framed input of a length-`n` word is `true` at every even position below
`2*n` and `false` at position `2*n`: that is the whole length test. -/
theorem frame_short (bs : List Bool) (j : ℕ) (hj : j < 2*bs.length) (he : j % 2 = 0) :
    readTapeBit (frame bs) j = true := by
  have hsplit : j = 2*(j/2) := by omega
  rw [hsplit, frame_even]
  simp only [decide_eq_true_eq]
  omega

theorem frame_stop (bs : List Bool) :
    readTapeBit (frame bs) (2*bs.length) = false := by
  rw [frame_even]
  simp

/-! ## The counter's finite control -/

/-- The gate's transition table.  States `[0,2*C)` scan the framed input two at a
time; states `[2*C,4*C)` rewind the input head; state `4*C` commits a `true`
verdict; state `4*C+1` is the single halted state. -/
def gateAction (C : ℕ) {t : ℕ} (input flag : Fin t) (q : Fin (4*C+2))
    (scanned : Fin t → Bool) : Option (Action t (4*C+2)) :=
  if h : q.val < 2*C then
    if q.val % 2 = 0 ∧ scanned input = false then
      some ⟨⟨4*C+1, by omega⟩, fun i => if i = flag then some false else none, fun _ => .stay⟩
    else
      some ⟨⟨q.val+1, by omega⟩, fun _ => none, fun i => if i = input then .right else .stay⟩
  else if h2 : q.val < 4*C then
    some ⟨⟨q.val+1, by omega⟩, fun _ => none, fun i => if i = input then .left else .stay⟩
  else if q.val = 4*C then
    some ⟨⟨4*C+1, by omega⟩, fun i => if i = flag then some true else none, fun _ => .stay⟩
  else none

theorem gateAction_scan (C : ℕ) {t : ℕ} (input flag : Fin t) (q : Fin (4*C+2))
    (sc : Fin t → Bool) (hq : q.val < 2*C) (hne : ¬(q.val % 2 = 0 ∧ sc input = false))
    (h2 : q.val+1 < 4*C+2) :
    gateAction C input flag q sc
      = some ⟨⟨q.val+1, h2⟩, fun _ => none, fun i => if i = input then .right else .stay⟩ := by
  simp only [gateAction]
  rw [dif_pos hq, if_neg hne]

theorem gateAction_reject (C : ℕ) {t : ℕ} (input flag : Fin t) (q : Fin (4*C+2))
    (sc : Fin t → Bool) (hq : q.val < 2*C) (heq : q.val % 2 = 0 ∧ sc input = false)
    (h2 : 4*C+1 < 4*C+2) :
    gateAction C input flag q sc
      = some ⟨⟨4*C+1, h2⟩, fun i => if i = flag then some false else none, fun _ => .stay⟩ := by
  simp only [gateAction]
  rw [dif_pos hq, if_pos heq]

theorem gateAction_rewind (C : ℕ) {t : ℕ} (input flag : Fin t) (q : Fin (4*C+2))
    (sc : Fin t → Bool) (hq : ¬ q.val < 2*C) (hq2 : q.val < 4*C) (h2 : q.val+1 < 4*C+2) :
    gateAction C input flag q sc
      = some ⟨⟨q.val+1, h2⟩, fun _ => none, fun i => if i = input then .left else .stay⟩ := by
  simp only [gateAction]
  rw [dif_neg hq, dif_pos hq2]

theorem gateAction_commit (C : ℕ) {t : ℕ} (input flag : Fin t) (q : Fin (4*C+2))
    (sc : Fin t → Bool) (hq : q.val = 4*C) (h2 : 4*C+1 < 4*C+2) :
    gateAction C input flag q sc
      = some ⟨⟨4*C+1, h2⟩, fun i => if i = flag then some true else none, fun _ => .stay⟩ := by
  simp only [gateAction]
  rw [dif_neg (by omega : ¬ q.val < 2*C), dif_neg (by omega : ¬ q.val < 4*C), if_pos hq]

/-- The length gate as a machine: it never inspects anything but the framed
input, and its only output is one verdict bit on `flag`. -/
def counter (C : ℕ) {t : ℕ} (input flag : Fin t) : Machine t (4*C+2) where
  descriptionBits := 0
  start := ⟨0, by omega⟩
  halted := fun q => decide (q.val = 4*C+1)
  rule := gateAction C input flag

@[simp] theorem counter_rule (C : ℕ) {t : ℕ} (input flag : Fin t) (q : Fin (4*C+2))
    (scanned : Fin t → Bool) :
    (counter C input flag).rule q scanned = gateAction C input flag q scanned := rfl

@[simp] theorem counter_halted (C : ℕ) {t : ℕ} (input flag : Fin t) (q : Fin (4*C+2)) :
    (counter C input flag).halted q = decide (q.val = 4*C+1) := rfl

/-! ## Configurations along the walk -/

/-- Head positions during the walk: only the input head moves. -/
def exitHeads {t : ℕ} (input : Fin t) (H : Fin t → ℕ) (pos : ℕ) : Fin t → ℕ :=
  fun i => if i = input then pos else H i

/-- Tapes after the verdict bit is written. -/
def exitTapes {t : ℕ} (flag : Fin t) (T : Fin t → List Bool) (h : ℕ) (b : Bool) :
    Fin t → List Bool :=
  fun i => if i = flag then writeTapeBit (T flag) h b else T i

def cfg (C : ℕ) {t : ℕ} (input : Fin t) (H : Fin t → ℕ) (T : Fin t → List Bool)
    (j : ℕ) (hj : j < 4*C+2) (pos : ℕ) : Configuration t (4*C+2) :=
  ⟨⟨j, hj⟩, exitHeads input H pos, T⟩

/-- The halted configuration reached by either exit of the gate. -/
def stopCfg (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ) (T : Fin t → List Bool)
    (pos : ℕ) (b : Bool) : Configuration t (4*C+2) :=
  ⟨⟨4*C+1, by omega⟩, exitHeads input H pos,
    exitTapes flag T (exitHeads input H pos flag) b⟩

theorem cfg_congr (C : ℕ) {t : ℕ} (input : Fin t) (H : Fin t → ℕ) (T : Fin t → List Bool)
    (j j' : ℕ) (hj : j < 4*C+2) (hj' : j' < 4*C+2) (pos pos' : ℕ)
    (hjj : j = j') (hp : pos = pos') :
    cfg C input H T j hj pos = cfg C input H T j' hj' pos' := by
  subst hjj; subst hp; rfl

theorem cfg_scanned (C : ℕ) {t : ℕ} (input : Fin t) (H : Fin t → ℕ) (T : Fin t → List Bool)
    (j : ℕ) (hj : j < 4*C+2) (pos : ℕ) :
    (cfg C input H T j hj pos).scanned input = readTapeBit (T input) pos := by
  simp [cfg, Configuration.scanned, exitHeads]

theorem stopCfg_scanned (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ)
    (T : Fin t → List Bool) (pos : ℕ) (b : Bool) :
    (stopCfg C input flag H T pos b).scanned flag = b := by
  simp [stopCfg, exitTapes, Configuration.scanned, MemoryTransition.read_write]

theorem exitTapes_other {t : ℕ} (flag : Fin t) (T : Fin t → List Bool) (h : ℕ) (b : Bool)
    (i : Fin t) (hi : i ≠ flag) : exitTapes flag T h b i = T i := by
  simp [exitTapes, hi]

theorem exitHeads_other {t : ℕ} (input : Fin t) (H : Fin t → ℕ) (pos : ℕ)
    (i : Fin t) (hi : i ≠ input) : exitHeads input H pos i = H i := by
  simp [exitHeads, hi]

/-! ## The three transitions -/

theorem scan_step (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ)
    (T : Fin t → List Bool) (j : ℕ) (hj : j < 2*C) (pos : ℕ)
    (hread : j % 2 = 0 → readTapeBit (T input) pos = true)
    (h1 : j < 4*C+2) (h2 : j+1 < 4*C+2) :
    step (counter C input flag) (cfg C input H T j h1 pos)
      = some (cfg C input H T (j+1) h2 (pos+1)) := by
  have hcond : ¬ (j % 2 = 0 ∧ (cfg C input H T j h1 pos).scanned input = false) := by
    rintro ⟨he, hf⟩
    rw [cfg_scanned, hread he] at hf
    exact Bool.noConfusion hf
  have hrule : (counter C input flag).rule (cfg C input H T j h1 pos).control
      (cfg C input H T j h1 pos).scanned
      = some ⟨⟨j+1, h2⟩, fun _ => none, fun i => if i = input then .right else .stay⟩ :=
    gateAction_scan C input flag ⟨j, h1⟩ (cfg C input H T j h1 pos).scanned hj hcond h2
  simp only [step, hrule, Option.map_some]
  apply congrArg
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i = input <;>
      simp [applyAction, cfg, exitHeads, hi, HeadMove.apply]
  · funext i
    simp [applyAction, cfg]

theorem rewind_step (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ)
    (T : Fin t → List Bool) (j : ℕ) (hj : 2*C ≤ j) (hj2 : j < 4*C) (pos : ℕ)
    (h1 : j < 4*C+2) (h2 : j+1 < 4*C+2) :
    step (counter C input flag) (cfg C input H T j h1 pos)
      = some (cfg C input H T (j+1) h2 (pos-1)) := by
  have hrule : (counter C input flag).rule (cfg C input H T j h1 pos).control
      (cfg C input H T j h1 pos).scanned
      = some ⟨⟨j+1, h2⟩, fun _ => none, fun i => if i = input then .left else .stay⟩ :=
    gateAction_rewind C input flag ⟨j, h1⟩ (cfg C input H T j h1 pos).scanned
      (by simpa using (by omega : ¬ j < 2*C)) hj2 h2
  simp only [step, hrule, Option.map_some]
  apply congrArg
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i = input <;>
      simp [applyAction, cfg, exitHeads, hi, HeadMove.apply]
  · funext i
    simp [applyAction, cfg]

theorem reject_step (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ)
    (T : Fin t → List Bool) (j : ℕ) (hj : j < 2*C) (heven : j % 2 = 0) (pos : ℕ)
    (hread : readTapeBit (T input) pos = false) (h1 : j < 4*C+2) :
    step (counter C input flag) (cfg C input H T j h1 pos)
      = some (stopCfg C input flag H T pos false) := by
  have hcond : j % 2 = 0 ∧ (cfg C input H T j h1 pos).scanned input = false := by
    refine ⟨heven, ?_⟩
    rw [cfg_scanned]
    exact hread
  have hrule : (counter C input flag).rule (cfg C input H T j h1 pos).control
      (cfg C input H T j h1 pos).scanned
      = some ⟨⟨4*C+1, by omega⟩, fun i => if i = flag then some false else none,
          fun _ => .stay⟩ :=
    gateAction_reject C input flag ⟨j, h1⟩ (cfg C input H T j h1 pos).scanned hj hcond (by omega)
  simp only [step, hrule, Option.map_some]
  apply congrArg
  apply configuration_ext
  · rfl
  · funext i
    simp [applyAction, cfg, stopCfg, exitHeads, HeadMove.apply]
  · funext i
    by_cases hi : i = flag <;>
      simp [applyAction, cfg, stopCfg, exitTapes, exitHeads, hi]

theorem commit_step (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ)
    (T : Fin t → List Bool) (j : ℕ) (hj : j = 4*C) (pos : ℕ) (h1 : j < 4*C+2) :
    step (counter C input flag) (cfg C input H T j h1 pos)
      = some (stopCfg C input flag H T pos true) := by
  have hrule : (counter C input flag).rule (cfg C input H T j h1 pos).control
      (cfg C input H T j h1 pos).scanned
      = some ⟨⟨4*C+1, by omega⟩, fun i => if i = flag then some true else none,
          fun _ => .stay⟩ :=
    gateAction_commit C input flag ⟨j, h1⟩ (cfg C input H T j h1 pos).scanned hj (by omega)
  simp only [step, hrule, Option.map_some]
  apply congrArg
  apply configuration_ext
  · rfl
  · funext i
    simp [applyAction, cfg, stopCfg, exitHeads, HeadMove.apply]
  · funext i
    by_cases hi : i = flag <;>
      simp [applyAction, cfg, stopCfg, exitTapes, exitHeads, hi]

/-! ## The two walks -/

theorem scan_walk (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ)
    (T : Fin t → List Bool) (m : ℕ) (hm : m ≤ 2*C)
    (hread : ∀ j, j < m → j % 2 = 0 → readTapeBit (T input) (H input + j) = true)
    (h0 : 0 < 4*C+2) (hmm : m < 4*C+2) :
    Timed (counter C input flag) m (cfg C input H T 0 h0 (H input))
      (cfg C input H T m hmm (H input + m)) := by
  induction m with
  | zero => exact Timed.refl _ _
  | succ m ih =>
    have hlt : m < 4*C+2 := by omega
    have h1 := ih (by omega) (fun j hj => hread j (by omega)) hlt
    have hnot : (counter C input flag).halted (cfg C input H T m hlt (H input + m)).control
        = false := by
      simp only [counter_halted, cfg, decide_eq_false_iff_not]
      omega
    have h2 := scan_step C input flag H T m (by omega) (H input + m)
      (fun he => hread m (by omega) he) hlt hmm
    exact h1.trans (Timed.single hnot h2)

theorem rewind_walk (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ)
    (T : Fin t → List Bool) (k : ℕ) (hk : k ≤ 2*C)
    (h0 : 2*C < 4*C+2) (hkk : 2*C+k < 4*C+2) :
    Timed (counter C input flag) k (cfg C input H T (2*C) h0 (H input + 2*C))
      (cfg C input H T (2*C+k) hkk (H input + 2*C - k)) := by
  induction k with
  | zero => exact Timed.refl _ _
  | succ k ih =>
    have hlt : 2*C+k < 4*C+2 := by omega
    have h1 := ih (by omega) hlt
    have hnot : (counter C input flag).halted
        (cfg C input H T (2*C+k) hlt (H input + 2*C - k)).control = false := by
      simp only [counter_halted, cfg, decide_eq_false_iff_not]
      omega
    have h2 := rewind_step C input flag H T (2*C+k) (by omega) (by omega)
      (H input + 2*C - k) hlt (by omega : 2*C+k+1 < 4*C+2)
    have h3 : cfg C input H T (2*C+k+1) (by omega : 2*C+k+1 < 4*C+2)
        (H input + 2*C - k - 1)
        = cfg C input H T (2*C+(k+1)) hkk (H input + 2*C - (k+1)) :=
      cfg_congr C input H T _ _ _ _ _ _ (by omega) (by omega)
    rw [h3] at h2
    exact h1.trans (Timed.single hnot h2)

/-! ## The gate's two exits -/

theorem counter_entry (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ)
    (T : Fin t → List Bool) (h0 : 0 < 4*C+2) :
    cfg C input H T 0 h0 (H input)
      = (⟨(counter C input flag).start, H, T⟩ : Configuration t (4*C+2)) := by
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i = input <;> simp [cfg, exitHeads, hi]
  · rfl

theorem counter_reject (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ)
    (T : Fin t → List Bool) (m : ℕ) (hm : 2*m < 2*C)
    (hread : ∀ j, j < 2*m → j % 2 = 0 → readTapeBit (T input) (H input + j) = true)
    (hstop : readTapeBit (T input) (H input + 2*m) = false) :
    Step (counter C input flag) (2*m+1) H T (exitHeads input H (H input + 2*m))
      (exitTapes flag T (exitHeads input H (H input + 2*m) flag) false) := by
  have hlt : 2*m < 4*C+2 := by omega
  have hwalk := scan_walk C input flag H T (2*m) (by omega) hread (by omega) hlt
  have hnot : (counter C input flag).halted
      (cfg C input H T (2*m) hlt (H input + 2*m)).control = false := by
    simp only [counter_halted, cfg, decide_eq_false_iff_not]
    omega
  have hstep := reject_step C input flag H T (2*m) (by omega) (by omega)
    (H input + 2*m) hstop hlt
  obtain ⟨r, hr, hf, hs⟩ := (hwalk.trans (Timed.single hnot hstep)).run (by simp [stopCfg])
  rw [counter_entry] at hr
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

theorem counter_pass (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ)
    (T : Fin t → List Bool)
    (hread : ∀ j, j < 2*C → j % 2 = 0 → readTapeBit (T input) (H input + j) = true) :
    Step (counter C input flag) (4*C+1) H T (exitHeads input H (H input))
      (exitTapes flag T (exitHeads input H (H input) flag) true) := by
  have h2C : 2*C < 4*C+2 := by omega
  have h4C : 2*C+2*C < 4*C+2 := by omega
  have hscan := scan_walk C input flag H T (2*C) (by omega) hread (by omega) h2C
  have hrew := rewind_walk C input flag H T (2*C) (by omega) h2C h4C
  have hzero : cfg C input H T (2*C+2*C) h4C (H input + 2*C - 2*C)
      = cfg C input H T (2*C+2*C) h4C (H input) :=
    cfg_congr C input H T _ _ _ _ _ _ rfl (by omega)
  rw [hzero] at hrew
  have hnot : (counter C input flag).halted
      (cfg C input H T (2*C+2*C) h4C (H input)).control = false := by
    simp only [counter_halted, cfg, decide_eq_false_iff_not]
    omega
  have hstep := commit_step C input flag H T (2*C+2*C) (by omega) (H input) h4C
  have hall := (hscan.trans hrew).trans (Timed.single hnot hstep)
  have harith : 2*C+2*C+1 = 4*C+1 := by omega
  rw [harith] at hall
  obtain ⟨r, hr, hf, hs⟩ := hall.run (by simp [stopCfg])
  rw [counter_entry] at hr
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

/-- The gate's pass exit, with the head map already normalised: the rewind
phase puts every head back exactly where it entered, so a docked worker sees
its own entry heads. -/
theorem exitHeads_self {t : ℕ} (input : Fin t) (H : Fin t → ℕ) :
    exitHeads input H (H input) = H := by
  funext i
  by_cases hi : i = input <;> simp [exitHeads, hi]

theorem counter_pass_clean (C : ℕ) {t : ℕ} (input flag : Fin t) (H : Fin t → ℕ)
    (T : Fin t → List Bool)
    (hread : ∀ j, j < 2*C → j % 2 = 0 → readTapeBit (T input) (H input + j) = true) :
    Step (counter C input flag) (4*C+1) H T H (exitTapes flag T (H flag) true) :=
  (counter_pass C input flag H T hread).congr (exitHeads_self input H)
    (by rw [exitHeads_self])

def branch {t b : ℕ} (flag result : Fin t) (q : Machine t b) : Machine t (2 + b) where
  descriptionBits := 0
  start := (⟨0, by omega⟩ : Fin 2).castAdd b
  halted := Fin.addCases (fun j : Fin 2 => decide (j.val = 1)) q.halted
  rule := Fin.addCases
    (fun _ (sc : Fin t → Bool) =>
      if sc flag then
        some (⟨q.start.natAdd 2, fun _ => none, fun _ => .stay⟩ : Action t (2+b))
      else
        some ⟨(⟨1, by omega⟩ : Fin 2).castAdd b,
          fun i => if i = result then some false else none, fun _ => .stay⟩)
    (fun j sc => (q.rule j sc).map (Composition.rightAction 2))

@[simp] theorem branch_halted_left {t b : ℕ} (flag result : Fin t) (q : Machine t b)
    (j : Fin 2) : (branch flag result q).halted (j.castAdd b) = decide (j.val = 1) := by
  simp [branch]

@[simp] theorem branch_halted_right {t b : ℕ} (flag result : Fin t) (q : Machine t b)
    (j : Fin b) : (branch flag result q).halted (j.natAdd 2) = q.halted j := by
  simp [branch]

theorem branch_right_step {t b : ℕ} (flag result : Fin t) (q : Machine t b)
    (c : Configuration t b) :
    step (branch flag result q) (Composition.rightConfig 2 c)
      = (step q c).map (Composition.rightConfig 2) := by
  simp [step, branch, Composition.rightConfig, Option.map_map, Function.comp_def,
    Composition.rightAction, applyAction]
  rfl

theorem branch_right_run {t b : ℕ} (flag result : Fin t) (q : Machine t b) (fuel : ℕ)
    (c : Configuration t b) (r : ExecutionReceipt t b) (hrun : runFrom q fuel c = some r) :
    runFrom (branch flag result q) fuel (Composition.rightConfig 2 c)
      = some (Composition.rightReceipt 2 r) := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hrun
    split at hrun
    · next h =>
        cases hrun
        simp [runFrom, Composition.rightConfig, h, Composition.rightReceipt,
          Configuration.tapeCells]
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hrun
    split at hrun
    · next h =>
        cases hrun
        simp [runFrom, Composition.rightConfig, h, Composition.rightReceipt,
          Configuration.tapeCells]
    · next h =>
        split at hrun
        · contradiction
        · next nxt hs =>
            split at hrun
            · contradiction
            · next suffix htail =>
                cases hrun
                have hm := ih nxt suffix htail
                have hstep : step (branch flag result q) (Composition.rightConfig 2 c)
                    = some (Composition.rightConfig 2 nxt) := by
                  rw [branch_right_step, hs]
                  rfl
                simpa [Composition.rightReceipt] using
                  runFrom_step (branch flag result q) (Composition.rightConfig 2 c)
                    (Composition.rightConfig 2 nxt) (Composition.rightReceipt 2 suffix)
                    (by simpa [Composition.rightConfig] using h) hstep hm

theorem branch_reject_step {t b : ℕ} (flag result : Fin t) (q : Machine t b)
    (H : Fin t → ℕ) (T : Fin t → List Bool)
    (hflag : readTapeBit (T flag) (H flag) = false) :
    step (branch flag result q) ⟨(branch flag result q).start, H, T⟩
      = some ⟨(⟨1, by omega⟩ : Fin 2).castAdd b, H, exitTapes result T (H result) false⟩ := by
  have key : ∀ sc : Fin t → Bool, sc flag = false →
      (branch flag result q).rule ((⟨0, by omega⟩ : Fin 2).castAdd b) sc
        = some ⟨(⟨1, by omega⟩ : Fin 2).castAdd b,
            fun i => if i = result then some false else none, fun _ => .stay⟩ := by
    intro sc hsc
    simp [branch, hsc]
  have hrule : (branch flag result q).rule (branch flag result q).start
      (⟨(branch flag result q).start, H, T⟩ : Configuration t (2+b)).scanned
      = some ⟨(⟨1, by omega⟩ : Fin 2).castAdd b,
          fun i => if i = result then some false else none, fun _ => .stay⟩ :=
    key _ hflag
  simp only [step, hrule, Option.map_some]
  apply congrArg
  apply configuration_ext
  · rfl
  · funext i
    simp [applyAction, HeadMove.apply]
  · funext i
    by_cases hi : i = result <;> simp [applyAction, exitTapes, hi]

theorem branch_reject {t b : ℕ} (flag result : Fin t) (q : Machine t b)
    (H : Fin t → ℕ) (T : Fin t → List Bool)
    (hflag : readTapeBit (T flag) (H flag) = false) :
    Step (branch flag result q) 1 H T H (exitTapes result T (H result) false) := by
  have hnot : (branch flag result q).halted
      (⟨(branch flag result q).start, H, T⟩ : Configuration t (2+b)).control = false := by
    simp [branch]
  obtain ⟨r, hr, hf, hs⟩ :=
    (Timed.single hnot (branch_reject_step flag result q H T hflag)).run (by simp)
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

theorem branch_pass_step {t b : ℕ} (flag result : Fin t) (q : Machine t b)
    (H : Fin t → ℕ) (T : Fin t → List Bool)
    (hflag : readTapeBit (T flag) (H flag) = true) :
    step (branch flag result q) ⟨(branch flag result q).start, H, T⟩
      = some (Composition.rightConfig 2 (⟨q.start, H, T⟩ : Configuration t b)) := by
  have key : ∀ sc : Fin t → Bool, sc flag = true →
      (branch flag result q).rule ((⟨0, by omega⟩ : Fin 2).castAdd b) sc
        = some (⟨q.start.natAdd 2, fun _ => none, fun _ => .stay⟩ : Action t (2+b)) := by
    intro sc hsc
    simp [branch, hsc]
  have hrule : (branch flag result q).rule (branch flag result q).start
      (⟨(branch flag result q).start, H, T⟩ : Configuration t (2+b)).scanned
      = some (⟨q.start.natAdd 2, fun _ => none, fun _ => .stay⟩ : Action t (2+b)) :=
    key _ hflag
  simp only [step, hrule, Option.map_some]
  apply congrArg
  apply configuration_ext
  · rfl
  · funext i
    simp [applyAction, Composition.rightConfig, HeadMove.apply]
  · funext i
    simp [applyAction, Composition.rightConfig]

theorem branch_pass {t b : ℕ} (flag result : Fin t) (q : Machine t b)
    (H : Fin t → ℕ) (T : Fin t → List Bool)
    (hflag : readTapeBit (T flag) (H flag) = true)
    (fuel : ℕ) (hout : Fin t → ℕ) (tout : Fin t → List Bool)
    (hq : Step q fuel H T hout tout) :
    Step (branch flag result q) (fuel+1) H T hout tout := by
  obtain ⟨r, hr, hh, ht, hs⟩ := hq
  have hright := branch_right_run flag result q fuel ⟨q.start, H, T⟩ r hr
  have hnot : (branch flag result q).halted
      (⟨(branch flag result q).start, H, T⟩ : Configuration t (2+b)).control = false := by
    simp [branch]
  have hjoin := runFrom_step (branch flag result q)
    ⟨(branch flag result q).start, H, T⟩
    (Composition.rightConfig 2 (⟨q.start, H, T⟩ : Configuration t b))
    (Composition.rightReceipt 2 r) hnot (branch_pass_step flag result q H T hflag) hright
  exact ⟨_, hjoin, by simpa [Composition.rightReceipt, Composition.rightConfig] using hh,
    by simpa [Composition.rightReceipt, Composition.rightConfig] using ht, by
      simp only [Composition.rightReceipt]
      omega⟩

/-! ## The gated machine -/

/-- The weak machine's finite front: count the frozen onset out of the framed
input, rewind, then either reject outright or hand the tapes to the worker. -/
def gated (C : ℕ) {t b : ℕ} (input flag result : Fin t) (q : Machine t b) :
    Machine t ((4*C+2) + (2+b)) :=
  Composition.machine (counter C input flag) (branch flag result q)

theorem gated_def (C : ℕ) {t b : ℕ} (input flag result : Fin t) (q : Machine t b) :
    gated C input flag result q
      = Composition.machine (counter C input flag) (branch flag result q) := rfl

theorem gated_reject (C : ℕ) {t b : ℕ} (input flag result : Fin t) (q : Machine t b)
    (hfi : flag ≠ input) (H : Fin t → ℕ) (T : Fin t → List Bool) (m : ℕ) (hm : 2*m < 2*C)
    (hread : ∀ j, j < 2*m → j % 2 = 0 → readTapeBit (T input) (H input + j) = true)
    (hstop : readTapeBit (T input) (H input + 2*m) = false) :
    ∃ r, runFrom (gated C input flag result q) ((2*m+1)+1+1)
        ⟨(gated C input flag result q).start, H, T⟩ = some r ∧
      r.final.scanned result = false := by
  have hp := counter_reject C input flag H T m hm hread hstop
  have hhf : exitHeads input H (H input + 2*m) flag = H flag :=
    exitHeads_other input H _ flag hfi
  have hflag : readTapeBit
      (exitTapes flag T (exitHeads input H (H input + 2*m) flag) false flag)
      (exitHeads input H (H input + 2*m) flag) = false := by
    simp [exitTapes, MemoryTransition.read_write]
  have hb := branch_reject flag result q (exitHeads input H (H input + 2*m))
    (exitTapes flag T (exitHeads input H (H input + 2*m) flag) false) hflag
  obtain ⟨r, hr, hh, ht, _⟩ := hp.seq hb
  refine ⟨r, hr, ?_⟩
  have hscan : r.final.scanned result
      = readTapeBit (r.final.tapes result) (r.final.heads result) := rfl
  rw [hscan, ht, hh]
  simp [exitTapes, MemoryTransition.read_write, hhf]

theorem gated_pass (C : ℕ) {t b : ℕ} (input flag result : Fin t) (q : Machine t b)
    (H : Fin t → ℕ) (T : Fin t → List Bool)
    (hread : ∀ j, j < 2*C → j % 2 = 0 → readTapeBit (T input) (H input + j) = true)
    (fuel : ℕ) (hout : Fin t → ℕ) (tout : Fin t → List Bool)
    (hq : Step q fuel H (exitTapes flag T (H flag) true) hout tout) :
    Step (gated C input flag result q) ((4*C+1)+1+(fuel+1)) H T hout tout := by
  have hp := counter_pass_clean C input flag H T hread
  have hflag : readTapeBit (exitTapes flag T (H flag) true flag) (H flag) = true := by
    simp [exitTapes, MemoryTransition.read_write]
  exact hp.seq (branch_pass flag result q H (exitTapes flag T (H flag) true) hflag
    fuel hout tout hq)

/-! ## The deliverable -/

/-- **P4.** `Exposes` demands `Soundness.cutoff constants ≤ n` as a conjunct of
its conclusion, so the weak machine must reject every length below the onset.
`hstates` is the realizability constraint -- the onset is spent as finite
control -- and `rejects` is the obligation. -/
structure LengthGate {t s : ℕ} {source : PointwisePCPPAlgorithm}
    (constants : Constants source) (p : Machine t s) (ht : 2 ≤ t)
    (result : Fin t) (budget : ℕ → ℕ) where
  hstates : Soundness.cutoff constants ≤ s
  rejects : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    n < Soundness.cutoff constants →
    ∀ r, run p (budget n)
        ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits) = some r →
      r.final.scanned result = false

theorem runFrom_unique {t s : ℕ} (p : Machine t s) (c : Configuration t s) (f g : ℕ)
    (r u : ExecutionReceipt t s) (hr : runFrom p f c = some r)
    (hu : runFrom p g c = some u) : r = u := by
  have h1 := runFrom_moreFuel p f g c r hr
  have h2 := runFrom_moreFuel p g f c u hu
  rw [Nat.add_comm g f] at h2
  exact Option.some.inj (h1.symm.trans h2)

/-- The realizer.  `states = (4*C+2)+(2+b)` with `C = Soundness.cutoff
constants`; every summand is forced by the construction (see the header), and
no numeral is chosen. -/
theorem lengthGate_of_stateCounter {t b : ℕ} {source : PointwisePCPPAlgorithm}
    (constants : Constants source) (input flag result : Fin t) (q : Machine t b)
    (ht : 2 ≤ t) (hzero : input.val = 0) (hfi : flag ≠ input) (budget : ℕ → ℕ) :
    LengthGate constants (gated (Soundness.cutoff constants) input flag result q) ht
      result budget := by
  refine ⟨by omega, ?_⟩
  intro n x bits hn r hr
  have hT0 : (UAcceptanceCarrier.verifier
      (gated (Soundness.cutoff constants) input flag result q) ht result).inputTapes
      (List.ofFn x) bits input = frame (List.ofFn x) := by
    rw [UAcceptanceCarrier.inputTapes_eq]
    simp [hzero]
  have hread : ∀ j, j < 2*n → j % 2 = 0 →
      readTapeBit ((UAcceptanceCarrier.verifier
        (gated (Soundness.cutoff constants) input flag result q) ht result).inputTapes
        (List.ofFn x) bits input) ((fun _ : Fin t => 0) input + j) = true := by
    intro j hj he
    rw [hT0]
    simpa using frame_short (List.ofFn x) j (by simpa using hj) he
  have hstop : readTapeBit ((UAcceptanceCarrier.verifier
      (gated (Soundness.cutoff constants) input flag result q) ht result).inputTapes
      (List.ofFn x) bits input) ((fun _ : Fin t => 0) input + 2*n) = false := by
    rw [hT0]
    simpa using frame_stop (List.ofFn x)
  obtain ⟨u, hu, hfalse⟩ := gated_reject (Soundness.cutoff constants) input flag result q hfi
    (fun _ => 0) _ n (by omega) hread hstop
  have hr' : runFrom (gated (Soundness.cutoff constants) input flag result q) (budget n)
      ⟨(gated (Soundness.cutoff constants) input flag result q).start, fun _ => 0,
        (UAcceptanceCarrier.verifier
          (gated (Soundness.cutoff constants) input flag result q) ht result).inputTapes
          (List.ofFn x) bits⟩ = some r := hr
  rw [runFrom_unique _ _ _ _ r u hr' hu]
  exact hfalse

/-! ## What the gate buys the consumer -/

/-- The gate makes `Weak.decides` carry the cutoff.  This is exactly the
conjunct that `Exposes` demands and that `Soundness.below` needs. -/
theorem cutoff_le_of_decides {t s : ℕ} {source : PointwisePCPPAlgorithm}
    {constants : Constants source} {p : Machine t s} {ht : 2 ≤ t} {result : Fin t}
    {budget : ℕ → ℕ} (G : LengthGate constants p ht result budget)
    {n : ℕ} (x : BitInput n) (bits : List Bool)
    (h : Weak.decides p ht result budget n x bits) :
    Soundness.cutoff constants ≤ n := by
  by_contra hlt
  obtain ⟨r, hr, hs⟩ := h
  have hfalse := G.rejects n x bits (by omega) r hr
  rw [hs] at hfalse
  exact Bool.noConfusion hfalse

theorem exposes_of_gate (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) {t s : ℕ}
    (constants : Constants (CloseoutLanguage.selectedPCPP sources))
    (p : Machine t s) (ht : 2 ≤ t) (result : Fin t) (budget : ℕ → ℕ)
    (G : LengthGate constants p ht result budget)
    (h : Exposes sources k clock constants
          (fun n x bits => Soundness.cutoff constants ≤ n ∧
            Weak.decides p ht result budget n x bits)) :
    Exposes sources k clock constants (Weak.decides p ht result budget) := by
  intro n x bits hm
  exact h n x bits ⟨cutoff_le_of_decides G x bits hm, hm⟩

/-! ## What a docked worker inherits

These two are the contract W1 builds against: the gate hands the worker the
verifier's own tapes with every head back at zero, one scratch slot carrying
`[true]`, and nothing else touched. -/

theorem exitTapes_blank {t : ℕ} (flag : Fin t) (T : Fin t → List Bool) (b : Bool)
    (hblank : T flag = []) (i : Fin t) :
    exitTapes flag T 0 b i = if i = flag then [b] else T i := by
  by_cases hi : i = flag
  · subst hi
    simp [exitTapes, hblank, writeTapeBit]
  · simp [exitTapes, hi]

/-- The pass path at the verifier's own input tapes.  `input` is tape `0`; the
worker starts with all heads at zero, exactly as `initialConfiguration` would
have left them, and sees `T` with the single scratch slot `flag` overwritten. -/
theorem gated_verifier_pass {t b : ℕ} (C : ℕ) (input flag result : Fin t)
    (q : Machine t b) (ht : 2 ≤ t) (hzero : input.val = 0)
    (n : ℕ) (x : BitInput n) (bits : List Bool) (hn : C ≤ n)
    (fuel : ℕ) (hout : Fin t → ℕ) (tout : Fin t → List Bool)
    (hq : Step q fuel (fun _ => 0)
        (exitTapes flag ((UAcceptanceCarrier.verifier (gated C input flag result q) ht
          result).inputTapes (List.ofFn x) bits) 0 true) hout tout) :
    Step (gated C input flag result q) ((4*C+1)+1+(fuel+1)) (fun _ => 0)
      ((UAcceptanceCarrier.verifier (gated C input flag result q) ht result).inputTapes
        (List.ofFn x) bits) hout tout := by
  have hT0 : (UAcceptanceCarrier.verifier (gated C input flag result q) ht result).inputTapes
      (List.ofFn x) bits input = frame (List.ofFn x) := by
    rw [UAcceptanceCarrier.inputTapes_eq]
    simp [hzero]
  have hread : ∀ j, j < 2*C → j % 2 = 0 →
      readTapeBit ((UAcceptanceCarrier.verifier (gated C input flag result q) ht
        result).inputTapes (List.ofFn x) bits input) ((fun _ : Fin t => 0) input + j) = true := by
    intro j hj he
    rw [hT0]
    simpa using frame_short (List.ofFn x) j (by simp; omega) he
  exact gated_pass C input flag result q (fun _ => 0) _ hread fuel hout tout hq

end NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
