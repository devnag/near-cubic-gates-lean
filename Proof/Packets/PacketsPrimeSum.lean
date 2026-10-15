import Proof.Packets.PacketsPrimeCount

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.PrimeSum
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.NatSum

def nw : Fin 4 → Option Bool := fun _ => none

/-- States: 0–2 init, 3 outer test, 4 scan (first cycle), 5 scan (later cycles), 6 rewind the divisor,
7–10 next divisor, 12 prime verdict (extend the candidate), 21 copy the candidate onto the output,
13–19 next candidate, 20 halt. -/
def machine : Machine 4 22 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 20
  rule := fun q b =>
    if q.val = 0 then some ⟨1, ![none, none, some false, some false], ![.right, .stay, .right, .right]⟩
    else if q.val = 1 then some ⟨2, ![none, none, some true, some true], ![.stay, .stay, .right, .right]⟩
    else if q.val = 2 then some ⟨3, ![none, none, some true, some true], ![.stay, .stay, .left, .left]⟩
    else if q.val = 3 then some (if b 0 then ⟨4, nw, fun _ => .stay⟩ else ⟨20, nw, fun _ => .stay⟩)
    else if q.val = 4 then some (if b 2 then
        (if b 3 then ⟨4, nw, ![.stay, .stay, .right, .right]⟩ else ⟨6, nw, ![.stay, .stay, .stay, .left]⟩)
      else (if b 3 then ⟨7, nw, fun _ => .stay⟩ else ⟨12, nw, fun _ => .stay⟩))
    else if q.val = 5 then some (if b 2 then
        (if b 3 then ⟨5, nw, ![.stay, .stay, .right, .right]⟩ else ⟨6, nw, ![.stay, .stay, .stay, .left]⟩)
      else (if b 3 then ⟨7, nw, fun _ => .stay⟩ else ⟨13, nw, fun _ => .stay⟩))
    else if q.val = 6 then some (if b 3 then ⟨6, nw, ![.stay, .stay, .stay, .left]⟩
      else ⟨5, nw, ![.stay, .stay, .stay, .right]⟩)
    else if q.val = 7 then some (if b 3 then ⟨7, nw, ![.stay, .stay, .stay, .right]⟩
      else ⟨8, ![none, none, none, some true], ![.stay, .stay, .stay, .left]⟩)
    else if q.val = 8 then some (if b 3 then ⟨8, nw, ![.stay, .stay, .stay, .left]⟩
      else ⟨9, nw, ![.stay, .stay, .stay, .right]⟩)
    else if q.val = 9 then some ⟨10, nw, ![.stay, .stay, .left, .stay]⟩
    else if q.val = 10 then some (if b 2 then ⟨10, nw, ![.stay, .stay, .left, .stay]⟩
      else ⟨4, nw, ![.stay, .stay, .right, .stay]⟩)
    else if q.val = 12 then some ⟨21, ![none, none, some true, none], ![.stay, .stay, .left, .stay]⟩
    else if q.val = 13 then some ⟨14, ![none, none, some true, none], ![.stay, .stay, .left, .stay]⟩
    else if q.val = 14 then some (if b 2 then ⟨14, nw, ![.stay, .stay, .left, .stay]⟩
      else ⟨15, nw, ![.stay, .stay, .right, .stay]⟩)
    else if q.val = 15 then some ⟨16, nw, ![.stay, .stay, .stay, .left]⟩
    else if q.val = 16 then some (if b 3 then ⟨16, ![none, none, none, some false], ![.stay, .stay, .stay, .left]⟩
      else ⟨17, nw, ![.stay, .stay, .stay, .right]⟩)
    else if q.val = 17 then some ⟨18, ![none, none, none, some true], ![.stay, .stay, .stay, .right]⟩
    else if q.val = 18 then some ⟨19, ![none, none, none, some true], ![.stay, .stay, .stay, .left]⟩
    else if q.val = 19 then some ⟨3, nw, ![.right, .stay, .stay, .stay]⟩
    else if q.val = 21 then some (if b 2 then ⟨21, ![none, some true, none, none], ![.stay, .right, .left, .stay]⟩
      else ⟨15, nw, ![.stay, .stay, .right, .stay]⟩)
    else none

/-- Tapes: bound `1^n` (head `h0`), output `1^m` (head at its end), candidate, divisor. -/
def cfg (q : Fin 22) (n h0 m : ℕ) (C : List Bool) (h2 : ℕ) (D : List Bool) (h3 : ℕ) : Configuration 4 22 :=
  ⟨q, ![h0, m, h2, h3], ![List.replicate n true, List.replicate m true, C, D]⟩

section Steps
variable (n h0 m : ℕ) (C : List Bool) (h2 : ℕ) (D : List Bool) (h3 : ℕ)

theorem s0 : step machine (cfg 0 n h0 m C h2 D h3) =
    some (cfg 1 n (h0+1) m (writeTapeBit C h2 false) (h2+1) (writeTapeBit D h3 false) (h3+1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s1 : step machine (cfg 1 n h0 m C h2 D h3) =
    some (cfg 2 n h0 m (writeTapeBit C h2 true) (h2+1) (writeTapeBit D h3 true) (h3+1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s2 : step machine (cfg 2 n h0 m C h2 D h3) =
    some (cfg 3 n h0 m (writeTapeBit C h2 true) (h2-1) (writeTapeBit D h3 true) (h3-1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s3t (h : readTapeBit (List.replicate n true) h0 = true) :
    step machine (cfg 3 n h0 m C h2 D h3) = some (cfg 4 n h0 m C h2 D h3) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s3f (h : readTapeBit (List.replicate n true) h0 = false) :
    step machine (cfg 3 n h0 m C h2 D h3) = some (cfg 20 n h0 m C h2 D h3) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s4tt (hc : readTapeBit C h2 = true) (hd : readTapeBit D h3 = true) :
    step machine (cfg 4 n h0 m C h2 D h3) = some (cfg 4 n h0 m C (h2+1) D (h3+1)) := by
  simp [step, machine, cfg, Configuration.scanned, hc, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s4tf (hc : readTapeBit C h2 = true) (hd : readTapeBit D h3 = false) :
    step machine (cfg 4 n h0 m C h2 D h3) = some (cfg 6 n h0 m C h2 D (h3-1)) := by
  simp [step, machine, cfg, Configuration.scanned, hc, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s4ff (hc : readTapeBit C h2 = false) (hd : readTapeBit D h3 = false) :
    step machine (cfg 4 n h0 m C h2 D h3) = some (cfg 12 n h0 m C h2 D h3) := by
  simp [step, machine, cfg, Configuration.scanned, hc, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s5tt (hc : readTapeBit C h2 = true) (hd : readTapeBit D h3 = true) :
    step machine (cfg 5 n h0 m C h2 D h3) = some (cfg 5 n h0 m C (h2+1) D (h3+1)) := by
  simp [step, machine, cfg, Configuration.scanned, hc, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s5tf (hc : readTapeBit C h2 = true) (hd : readTapeBit D h3 = false) :
    step machine (cfg 5 n h0 m C h2 D h3) = some (cfg 6 n h0 m C h2 D (h3-1)) := by
  simp [step, machine, cfg, Configuration.scanned, hc, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s5ft (hc : readTapeBit C h2 = false) (hd : readTapeBit D h3 = true) :
    step machine (cfg 5 n h0 m C h2 D h3) = some (cfg 7 n h0 m C h2 D h3) := by
  simp [step, machine, cfg, Configuration.scanned, hc, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s5ff (hc : readTapeBit C h2 = false) (hd : readTapeBit D h3 = false) :
    step machine (cfg 5 n h0 m C h2 D h3) = some (cfg 13 n h0 m C h2 D h3) := by
  simp [step, machine, cfg, Configuration.scanned, hc, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s6t (hd : readTapeBit D h3 = true) :
    step machine (cfg 6 n h0 m C h2 D h3) = some (cfg 6 n h0 m C h2 D (h3-1)) := by
  simp [step, machine, cfg, Configuration.scanned, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s6f (hd : readTapeBit D h3 = false) :
    step machine (cfg 6 n h0 m C h2 D h3) = some (cfg 5 n h0 m C h2 D (h3+1)) := by
  simp [step, machine, cfg, Configuration.scanned, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s7t (hd : readTapeBit D h3 = true) :
    step machine (cfg 7 n h0 m C h2 D h3) = some (cfg 7 n h0 m C h2 D (h3+1)) := by
  simp [step, machine, cfg, Configuration.scanned, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s7f (hd : readTapeBit D h3 = false) :
    step machine (cfg 7 n h0 m C h2 D h3) = some (cfg 8 n h0 m C h2 (writeTapeBit D h3 true) (h3-1)) := by
  simp [step, machine, cfg, Configuration.scanned, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s8t (hd : readTapeBit D h3 = true) :
    step machine (cfg 8 n h0 m C h2 D h3) = some (cfg 8 n h0 m C h2 D (h3-1)) := by
  simp [step, machine, cfg, Configuration.scanned, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s8f (hd : readTapeBit D h3 = false) :
    step machine (cfg 8 n h0 m C h2 D h3) = some (cfg 9 n h0 m C h2 D (h3+1)) := by
  simp [step, machine, cfg, Configuration.scanned, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s9 : step machine (cfg 9 n h0 m C h2 D h3) = some (cfg 10 n h0 m C (h2-1) D h3) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s10t (hc : readTapeBit C h2 = true) :
    step machine (cfg 10 n h0 m C h2 D h3) = some (cfg 10 n h0 m C (h2-1) D h3) := by
  simp [step, machine, cfg, Configuration.scanned, hc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s10f (hc : readTapeBit C h2 = false) :
    step machine (cfg 10 n h0 m C h2 D h3) = some (cfg 4 n h0 m C (h2+1) D h3) := by
  simp [step, machine, cfg, Configuration.scanned, hc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s12 : step machine (cfg 12 n h0 m C h2 D h3) =
    some (cfg 21 n h0 m (writeTapeBit C h2 true) (h2-1) D h3) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s21t (hc : readTapeBit C h2 = true) :
    step machine (cfg 21 n h0 m C h2 D h3) = some (cfg 21 n h0 (m+1) C (h2-1) D h3) := by
  simp [step, machine, cfg, Configuration.scanned, hc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end_replicate]

theorem s21f (hc : readTapeBit C h2 = false) :
    step machine (cfg 21 n h0 m C h2 D h3) = some (cfg 15 n h0 m C (h2+1) D h3) := by
  simp [step, machine, cfg, Configuration.scanned, hc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s13 : step machine (cfg 13 n h0 m C h2 D h3) =
    some (cfg 14 n h0 m (writeTapeBit C h2 true) (h2-1) D h3) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s14t (hc : readTapeBit C h2 = true) :
    step machine (cfg 14 n h0 m C h2 D h3) = some (cfg 14 n h0 m C (h2-1) D h3) := by
  simp [step, machine, cfg, Configuration.scanned, hc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s14f (hc : readTapeBit C h2 = false) :
    step machine (cfg 14 n h0 m C h2 D h3) = some (cfg 15 n h0 m C (h2+1) D h3) := by
  simp [step, machine, cfg, Configuration.scanned, hc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s15 : step machine (cfg 15 n h0 m C h2 D h3) = some (cfg 16 n h0 m C h2 D (h3-1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s16t (hd : readTapeBit D h3 = true) :
    step machine (cfg 16 n h0 m C h2 D h3) = some (cfg 16 n h0 m C h2 (writeTapeBit D h3 false) (h3-1)) := by
  simp [step, machine, cfg, Configuration.scanned, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s16f (hd : readTapeBit D h3 = false) :
    step machine (cfg 16 n h0 m C h2 D h3) = some (cfg 17 n h0 m C h2 D (h3+1)) := by
  simp [step, machine, cfg, Configuration.scanned, hd]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s17 : step machine (cfg 17 n h0 m C h2 D h3) =
    some (cfg 18 n h0 m C h2 (writeTapeBit D h3 true) (h3+1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s18 : step machine (cfg 18 n h0 m C h2 D h3) =
    some (cfg 19 n h0 m C h2 (writeTapeBit D h3 true) (h3-1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s19 : step machine (cfg 19 n h0 m C h2 D h3) = some (cfg 3 n (h0+1) m C h2 D h3) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

end Steps

/-! ## Walks -/

theorem timed_congr {t t' : ℕ} {c c' d d' : Configuration 4 22} (h : Timed machine t c d)
    (ht : t = t') (hc : c = c') (hd : d = d') : Timed machine t' c' d' := by
  subst ht hc hd
  exact h

theorem tr {t u : ℕ} {c d d' e : Configuration 4 22} (h1 : Timed machine t c d) (h2 : Timed machine u d' e)
    (h : d = d') : Timed machine (t + u) c e := by
  subst h
  exact h1.trans h2

theorem one {c d : Configuration 4 22} (hq : c.control.val ≠ 20) (h : step machine c = some d) :
    Timed machine 1 c d :=
  Timed.single (by simp [machine, hq]) h

/-- A family of configurations stepping into each other is a timed walk. -/
theorem walk (f : ℕ → Configuration 4 22) (a : ℕ) : ∀ s : ℕ,
    (∀ i, a ≤ i → i < a + s → (f i).control.val ≠ 20 ∧ step machine (f i) = some (f (i+1))) →
    Timed machine s (f a) (f (a + s)) := by
  intro s
  induction s generalizing a with
  | zero => intro _; simpa using Timed.refl machine (f a)
  | succ s ih =>
    intro h
    have ⟨h1, h2⟩ := h a (le_refl a) (by omega)
    have t1 := one h1 h2
    have t2 := ih (a + 1) (fun i hi hi' => h i (by omega) (by omega))
    exact timed_congr (t1.trans t2) (by omega) rfl (by congr 1; omega)

theorem read_rep (x i : ℕ) : readTapeBit (List.replicate x true) i = decide (i < x) := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < x
  · simp [h]
  · simp [h]

theorem rs (d k i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ d) : readTapeBit (sent d k) i = true := by
  rw [read_sent]; simp [h1, h2]

theorem rsf (d k i : ℕ) (h : d < i) : readTapeBit (sent d k) i = false := by
  rw [read_sent]; simp; omega

theorem rs0 (d k : ℕ) : readTapeBit (sent d k) 0 = false := by
  rw [read_sent]; simp

section Walks
variable (n h0 m : ℕ)

/-- The lockstep scan (states 4, 5). -/
theorem scan_tt (q : Fin 22) (hq : q = 4 ∨ q = 5) (c d k i i' s : ℕ) (hi : i + s ≤ c) (hi' : i' + s ≤ d) :
    Timed machine s (cfg q n h0 m (sent c 0) (1 + i) (sent d k) (1 + i'))
      (cfg q n h0 m (sent c 0) (1 + i + s) (sent d k) (1 + i' + s)) := by
  have w := walk (fun t => cfg q n h0 m (sent c 0) (1 + i + t) (sent d k) (1 + i' + t)) 0 s (by
    intro t _ ht
    refine ⟨by rcases hq with rfl | rfl <;> simp [cfg], ?_⟩
    have hc := rs c 0 (1 + i + t) (by omega) (by omega)
    have hd := rs d k (1 + i' + t) (by omega) (by omega)
    rcases hq with rfl | rfl
    · exact (s4tt n h0 m _ _ _ _ hc hd).trans (by rfl)
    · exact (s5tt n h0 m _ _ _ _ hc hd).trans (by rfl))
  simpa using w

/-- Rewind the divisor head from `i` to `1` (state 6, then 5). -/
theorem rew6 (C : List Bool) (h2 d k : ℕ) (i : ℕ) (hi : i ≤ d) :
    Timed machine (i + 1) (cfg 6 n h0 m C h2 (sent d k) i) (cfg 5 n h0 m C h2 (sent d k) 1) := by
  have w := walk (fun t => cfg 6 n h0 m C h2 (sent d k) (i - t)) 0 i (by
    intro t _ ht
    refine ⟨by simp [cfg], ?_⟩
    have hd := rs d k (i - t) (by omega) (by omega)
    exact (s6t n h0 m C h2 _ _ hd).trans (by rw [show i - t - 1 = i - (t + 1) by omega]))
  have t2 := one (c := cfg 6 n h0 m C h2 (sent d k) 0) (by simp [cfg]) (s6f n h0 m C h2 _ _ (rs0 d k))
  exact timed_congr (tr w t2 (by simp)) (by omega) (by simp) rfl

end Walks

/-! ## The divisibility scan -/

section Scan
variable (n h0 m : ℕ)

/-- Later cycles: from `C` position `1 + (c - r)` with the divisor head at `1`, the scan reaches the end
of `C` with the divisor head at `1 + e`, where `e ∈ [1, d]` and `e = d` iff `d ∣ r`. -/
theorem scanL (c d k : ℕ) (hd : 2 ≤ d) : ∀ r, 1 ≤ r → r ≤ c → ∃ e T, 1 ≤ e ∧ e ≤ d ∧ (d ∣ r ↔ e = d) ∧
    T ≤ 3 * r ∧ Timed machine T (cfg 5 n h0 m (sent c 0) (1 + (c - r)) (sent d k) 1)
      (cfg 5 n h0 m (sent c 0) (1 + c) (sent d k) (1 + e)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr1 hrc
    by_cases hrd : r ≤ d
    · refine ⟨r, r, hr1, hrd, ?_, by omega, ?_⟩
      · constructor
        · intro h
          have := Nat.le_of_dvd (by omega) h
          omega
        · intro h; rw [h]
      · have w := scan_tt n h0 m 5 (Or.inr rfl) c d k (c - r) 0 r (by omega) (by omega)
        exact timed_congr w rfl rfl (by congr 1 <;> omega)
    · have w1 := scan_tt n h0 m 5 (Or.inr rfl) c d k (c - r) 0 d (by omega) (by omega)
      have hc := rs c 0 (1 + (c - r) + d) (by omega) (by omega)
      have hdf := rsf d k (1 + 0 + d) (by omega)
      have w2 := one (c := cfg 5 n h0 m (sent c 0) (1 + (c - r) + d) (sent d k) (1 + 0 + d)) (by simp [cfg])
        (s5tf n h0 m _ _ _ _ hc hdf)
      have w3 := rew6 n h0 m (sent c 0) (1 + (c - r) + d) d k (1 + 0 + d - 1) (by omega)
      obtain ⟨e, T, he1, he2, hediv, hT, w4⟩ := ih (r - d) (by omega) (by omega) (by omega)
      have hmid : (cfg 5 n h0 m (sent c 0) (1 + (c - r) + d) (sent d k) 1) =
          (cfg 5 n h0 m (sent c 0) (1 + (c - (r - d))) (sent d k) 1) := by
        congr 1; omega
      refine ⟨e, d + 1 + (1 + 0 + d - 1 + 1) + T, he1, he2, ?_, by omega, ?_⟩
      · have hr : r = d + (r - d) := by omega
        rw [hr, Nat.dvd_add_right (dvd_refl d)]
        exact hediv
      · exact tr (tr (tr w1 w2 rfl) w3 rfl) w4 hmid

/-- The first cycle when `c ≤ d`: the scan reaches the end of `C` with the divisor head at `1 + c`. -/
theorem scanF_le (c d k : ℕ) (hcd : c ≤ d) :
    Timed machine c (cfg 4 n h0 m (sent c 0) 1 (sent d k) 1) (cfg 4 n h0 m (sent c 0) (1 + c) (sent d k) (1 + c)) := by
  have w := scan_tt n h0 m 4 (Or.inl rfl) c d k 0 0 c (by omega) (by omega)
  exact timed_congr w rfl rfl (by congr 1 <;> omega)

/-- The first cycle when `d < c`: one full cycle, the rewind, then the later cycles. -/
theorem scanF_gt (c d k : ℕ) (hd : 2 ≤ d) (hcd : d < c) : ∃ e T, 1 ≤ e ∧ e ≤ d ∧ (d ∣ c ↔ e = d) ∧
    T ≤ 3 * c + 2 ∧ Timed machine T (cfg 4 n h0 m (sent c 0) 1 (sent d k) 1)
      (cfg 5 n h0 m (sent c 0) (1 + c) (sent d k) (1 + e)) := by
  have w1 := scan_tt n h0 m 4 (Or.inl rfl) c d k 0 0 d (by omega) (by omega)
  have hc := rs c 0 (1 + 0 + d) (by omega) (by omega)
  have hdf := rsf d k (1 + 0 + d) (by omega)
  have w2 := one (c := cfg 4 n h0 m (sent c 0) (1 + 0 + d) (sent d k) (1 + 0 + d)) (by simp [cfg])
    (s4tf n h0 m _ _ _ _ hc hdf)
  have w3 := rew6 n h0 m (sent c 0) (1 + 0 + d) d k (1 + 0 + d - 1) (by omega)
  obtain ⟨e, T, he1, he2, hediv, hT, w4⟩ := scanL n h0 m c d k hd (c - d) (by omega) (by omega)
  have hmid : (cfg 5 n h0 m (sent c 0) (1 + 0 + d) (sent d k) 1) =
      (cfg 5 n h0 m (sent c 0) (1 + (c - (c - d))) (sent d k) 1) := by
    congr 1; omega
  refine ⟨e, d + 1 + (1 + 0 + d - 1 + 1) + T, he1, he2, ?_, by omega, ?_⟩
  · have hr : c = d + (c - d) := by omega
    rw [hr, Nat.dvd_add_right (dvd_refl d)]
    exact hediv
  · exact timed_congr (tr (tr (tr w1 w2 rfl) w3 rfl) w4 hmid) rfl (by congr 1) rfl

/-- Not divisible: extend the divisor by one and return both heads to `1` (states 7–10). -/
theorem nondiv (c d k e : ℕ) (hd : 1 ≤ d) (hdc : d ≤ c) (he1 : 1 ≤ e) (hed : e < d) : ∃ T, T ≤ 3 * c + 4 ∧
    Timed machine T (cfg 5 n h0 m (sent c 0) (1 + c) (sent d k) (1 + e))
      (cfg 4 n h0 m (sent c 0) 1 (sent (d + 1) (k - 1)) 1) := by
  have hcf := rsf c 0 (1 + c) (by omega)
  have hdt := rs d k (1 + e) (by omega) (by omega)
  have w1 := one (c := cfg 5 n h0 m (sent c 0) (1 + c) (sent d k) (1 + e)) (by simp [cfg])
    (s5ft n h0 m _ _ _ _ hcf hdt)
  have w2 := walk (fun t => cfg 7 n h0 m (sent c 0) (1 + c) (sent d k) (1 + e + t)) 0 (d - e) (by
    intro t _ ht
    refine ⟨by simp [cfg], ?_⟩
    exact (s7t n h0 m _ _ _ _ (rs d k (1 + e + t) (by omega) (by omega))).trans (by rfl))
  have w3 := one (c := cfg 7 n h0 m (sent c 0) (1 + c) (sent d k) (1 + e + (d - e))) (by simp [cfg])
    (s7f n h0 m _ _ _ _ (rsf d k (1 + e + (d - e)) (by omega)))
  have ha : writeTapeBit (sent d k) (1 + e + (d - e)) true = sent (d + 1) (k - 1) := by
    rw [show 1 + e + (d - e) = d + 1 by omega]
    exact sent_add d k
  have w4 := walk (fun t => cfg 8 n h0 m (sent c 0) (1 + c) (sent (d + 1) (k - 1)) (d - t)) 0 d (by
    intro t _ ht
    refine ⟨by simp [cfg], ?_⟩
    exact (s8t n h0 m _ _ _ _ (rs (d + 1) (k - 1) (d - t) (by omega) (by omega))).trans
      (by rw [show d - t - 1 = d - (t + 1) by omega]))
  have w5 := one (c := cfg 8 n h0 m (sent c 0) (1 + c) (sent (d + 1) (k - 1)) 0) (by simp [cfg])
    (s8f n h0 m _ _ _ _ (rs0 (d + 1) (k - 1)))
  have w6 := one (c := cfg 9 n h0 m (sent c 0) (1 + c) (sent (d + 1) (k - 1)) (0 + 1)) (by simp [cfg])
    (s9 n h0 m _ _ _ _)
  have w7 := walk (fun t => cfg 10 n h0 m (sent c 0) (c - t) (sent (d + 1) (k - 1)) (0 + 1)) 0 c (by
    intro t _ ht
    refine ⟨by simp [cfg], ?_⟩
    exact (s10t n h0 m _ _ _ _ (rs c 0 (c - t) (by omega) (by omega))).trans
      (by rw [show c - t - 1 = c - (t + 1) by omega]))
  have w8 := one (c := cfg 10 n h0 m (sent c 0) 0 (sent (d + 1) (k - 1)) (0 + 1)) (by simp [cfg])
    (s10f n h0 m _ _ _ _ (rs0 c 0))
  refine ⟨_, ?_, tr (tr (tr (tr (tr (tr (tr w1 w2 (by simp)) w3 (by simp)) w4 (by rw [ha]; congr 1; omega)) w5
    (by simp)) w6 rfl) w7 (by simp)) w8 (by simp)⟩
  omega

end Scan

/-! ## The smallest-divisor search -/

section Inner
variable (n h0 m : ℕ)

/-- From divisor `d ≤ minFac c` (both heads at `1`), the machine reaches the verdict: state 12 when `c` is
prime, 13 otherwise, with the candidate head at its end and the divisor at `minFac c`. -/
theorem inner (c : ℕ) (hc : 2 ≤ c) : ∀ t d k, 2 ≤ d → d + t = Nat.minFac c → ∃ T k', T ≤ (t + 1) * (6 * c + 10) ∧
    ((c.Prime ∧ Timed machine T (cfg 4 n h0 m (sent c 0) 1 (sent d k) 1)
        (cfg 12 n h0 m (sent c 0) (1 + c) (sent (Nat.minFac c) k') (1 + Nat.minFac c))) ∨
     (¬ c.Prime ∧ Timed machine T (cfg 4 n h0 m (sent c 0) 1 (sent d k) 1)
        (cfg 13 n h0 m (sent c 0) (1 + c) (sent (Nat.minFac c) k') (1 + Nat.minFac c)))) := by
  have hmin := Nat.minFac_le (show 0 < c by omega)
  intro t
  induction t with
  | zero =>
    intro d k hd hdt
    have hdm : d = Nat.minFac c := by omega
    subst hdm
    by_cases hcd : c ≤ Nat.minFac c
    · have heq : Nat.minFac c = c := by omega
      have hp : c.Prime := Nat.prime_def_minFac.mpr ⟨hc, heq⟩
      have w1 := scanF_le n h0 m c (Nat.minFac c) k hcd
      have w2 := one (c := cfg 4 n h0 m (sent c 0) (1 + c) (sent (Nat.minFac c) k) (1 + c)) (by simp [cfg])
        (s4ff n h0 m _ _ _ _ (rsf c 0 (1 + c) (by omega)) (rsf (Nat.minFac c) k (1 + c) (by omega)))
      refine ⟨c + 1, k, by nlinarith, Or.inl ⟨hp, ?_⟩⟩
      exact timed_congr (w1.trans w2) rfl rfl (by rw [heq])
    · have hp : ¬ c.Prime := by
        intro hp
        exact hcd (le_of_eq hp.minFac_eq.symm)
      obtain ⟨e, T, he1, he2, hediv, hT, w1⟩ := scanF_gt n h0 m c (Nat.minFac c) k hd (by omega)
      have he : e = Nat.minFac c := hediv.mp (Nat.minFac_dvd c)
      subst he
      have w2 := one (c := cfg 5 n h0 m (sent c 0) (1 + c) (sent (Nat.minFac c) k) (1 + Nat.minFac c))
        (by simp [cfg])
        (s5ff n h0 m _ _ _ _ (rsf c 0 (1 + c) (by omega)) (rsf (Nat.minFac c) k (1 + Nat.minFac c) (by omega)))
      refine ⟨T + 1, k, by nlinarith, Or.inr ⟨hp, w1.trans w2⟩⟩
  | succ t ih =>
    intro d k hd hdt
    have hlt : d < Nat.minFac c := by omega
    have hndiv : ¬ d ∣ c := fun h => by
      have := Nat.minFac_le_of_dvd hd h
      omega
    obtain ⟨e, T, he1, he2, hediv, hT, w1⟩ := scanF_gt n h0 m c d k hd (by omega)
    have hed : e < d := by
      rcases Nat.lt_or_ge e d with h | h
      · exact h
      · exact absurd (hediv.mpr (by omega)) hndiv
    obtain ⟨T2, hT2, w2⟩ := nondiv n h0 m c d k e (by omega) (by omega) he1 hed
    obtain ⟨T3, k', hT3, h3⟩ := ih (d + 1) (k - 1) (by omega) (by omega)
    refine ⟨T + T2 + T3, k', ?_, ?_⟩
    · have : (t + 1 + 1) * (6 * c + 10) = (t + 1) * (6 * c + 10) + (6 * c + 10) := by ring
      omega
    · rcases h3 with ⟨hp, w3⟩ | ⟨hp, w3⟩
      · exact Or.inl ⟨hp, (w1.trans w2).trans w3⟩
      · exact Or.inr ⟨hp, (w1.trans w2).trans w3⟩

/-- After the verdict: extend the candidate, reset the divisor to `2`, advance the counter head. -/
theorem post (c d k : ℕ) :
    Timed machine (c + d + 7) (cfg 13 n h0 m (sent c 0) (1 + c) (sent d k) (1 + d))
      (cfg 3 n (h0 + 1) m (sent (c + 1) 0) 1 (sent 2 (k + d - 2)) 1) := by
  have w1 := one (c := cfg 13 n h0 m (sent c 0) (1 + c) (sent d k) (1 + d)) (by simp [cfg]) (s13 n h0 m _ _ _ _)
  have hC : writeTapeBit (sent c 0) (1 + c) true = sent (c + 1) 0 := by
    rw [show 1 + c = c + 1 by omega]; exact sent_add c 0
  have w2 := walk (fun t => cfg 14 n h0 m (sent (c + 1) 0) (c - t) (sent d k) (1 + d)) 0 c (by
    intro t _ ht
    refine ⟨by simp [cfg], ?_⟩
    exact (s14t n h0 m _ _ _ _ (rs (c + 1) 0 (c - t) (by omega) (by omega))).trans
      (by rw [show c - t - 1 = c - (t + 1) by omega]))
  have w3 := one (c := cfg 14 n h0 m (sent (c + 1) 0) 0 (sent d k) (1 + d)) (by simp [cfg])
    (s14f n h0 m _ _ _ _ (rs0 (c + 1) 0))
  have w4 := one (c := cfg 15 n h0 m (sent (c + 1) 0) (0 + 1) (sent d k) (1 + d)) (by simp [cfg])
    (s15 n h0 m _ _ _ _)
  have w5 := walk (fun t => cfg 16 n h0 m (sent (c + 1) 0) (0 + 1) (sent (d - t) (k + t)) (d - t)) 0 d (by
    intro t _ ht
    refine ⟨by simp [cfg], ?_⟩
    have he : writeTapeBit (sent (d - t) (k + t)) (d - t) false = sent (d - (t + 1)) (k + (t + 1)) := by
      have := sent_erase (d - t - 1) (k + t)
      rw [show d - t - 1 + 1 = d - t by omega] at this
      rw [this]; congr 1 <;> omega
    exact (s16t n h0 m _ _ _ _ (rs (d - t) (k + t) (d - t) (by omega) (by omega))).trans
      (by rw [he, show d - t - 1 = d - (t + 1) by omega]))
  have w6 := one (c := cfg 16 n h0 m (sent (c + 1) 0) (0 + 1) (sent 0 (k + d)) 0) (by simp [cfg])
    (s16f n h0 m _ _ _ _ (rs0 0 (k + d)))
  have w7 := one (c := cfg 17 n h0 m (sent (c + 1) 0) (0 + 1) (sent 0 (k + d)) (0 + 1)) (by simp [cfg])
    (s17 n h0 m _ _ _ _)
  have h17 : writeTapeBit (sent 0 (k + d)) (0 + 1) true = sent 1 (k + d - 1) := sent_add 0 (k + d)
  have w8 := one (c := cfg 18 n h0 m (sent (c + 1) 0) (0 + 1) (sent 1 (k + d - 1)) (0 + 1 + 1)) (by simp [cfg])
    (s18 n h0 m _ _ _ _)
  have h18 : writeTapeBit (sent 1 (k + d - 1)) (0 + 1 + 1) true = sent 2 (k + d - 2) := by
    have := sent_add 1 (k + d - 1)
    rw [show k + d - 1 - 1 = k + d - 2 by omega] at this
    exact this
  have w9 := one (c := cfg 19 n h0 m (sent (c + 1) 0) (0 + 1) (sent 2 (k + d - 2)) (0 + 1 + 1 - 1))
    (by simp [cfg]) (s19 n h0 m _ _ _ _)
  have t := tr (tr (tr (tr (tr (tr (tr (tr w1 w2 (by simp [hC])) w3 (by simp)) w4 rfl) w5
    (by simp)) w6 (by simp)) w7 rfl) w8 (by rw [h17])) w9 (by rw [h18])
  exact timed_congr t (by omega) rfl rfl

/-- After the PRIME verdict: extend the candidate, copy it onto the output (`c` trues), reset the divisor to
`2`, advance the counter head. -/
theorem postP (c d k : ℕ) :
    Timed machine (c + d + 7) (cfg 12 n h0 m (sent c 0) (1 + c) (sent d k) (1 + d))
      (cfg 3 n (h0 + 1) (m + c) (sent (c + 1) 0) 1 (sent 2 (k + d - 2)) 1) := by
  have w1 := one (c := cfg 12 n h0 m (sent c 0) (1 + c) (sent d k) (1 + d)) (by simp [cfg]) (s12 n h0 m _ _ _ _)
  have hC : writeTapeBit (sent c 0) (1 + c) true = sent (c + 1) 0 := by
    rw [show 1 + c = c + 1 by omega]; exact sent_add c 0
  have w2 := walk (fun t => cfg 21 n h0 (m + t) (sent (c + 1) 0) (c - t) (sent d k) (1 + d)) 0 c (by
    intro t _ ht
    refine ⟨by simp [cfg], ?_⟩
    exact (s21t n h0 (m + t) _ _ _ _ (rs (c + 1) 0 (c - t) (by omega) (by omega))).trans
      (by rw [show c - t - 1 = c - (t + 1) by omega, show m + t + 1 = m + (t + 1) by omega]))
  have w3 := one (c := cfg 21 n h0 (m + c) (sent (c + 1) 0) 0 (sent d k) (1 + d)) (by simp [cfg])
    (s21f n h0 (m + c) _ _ _ _ (rs0 (c + 1) 0))
  have w4 := one (c := cfg 15 n h0 (m + c) (sent (c + 1) 0) (0 + 1) (sent d k) (1 + d)) (by simp [cfg])
    (s15 n h0 (m + c) _ _ _ _)
  have w5 := walk (fun t => cfg 16 n h0 (m + c) (sent (c + 1) 0) (0 + 1) (sent (d - t) (k + t)) (d - t)) 0 d (by
    intro t _ ht
    refine ⟨by simp [cfg], ?_⟩
    have he : writeTapeBit (sent (d - t) (k + t)) (d - t) false = sent (d - (t + 1)) (k + (t + 1)) := by
      have := sent_erase (d - t - 1) (k + t)
      rw [show d - t - 1 + 1 = d - t by omega] at this
      rw [this]; congr 1 <;> omega
    exact (s16t n h0 (m + c) _ _ _ _ (rs (d - t) (k + t) (d - t) (by omega) (by omega))).trans
      (by rw [he, show d - t - 1 = d - (t + 1) by omega]))
  have w6 := one (c := cfg 16 n h0 (m + c) (sent (c + 1) 0) (0 + 1) (sent 0 (k + d)) 0) (by simp [cfg])
    (s16f n h0 (m + c) _ _ _ _ (rs0 0 (k + d)))
  have w7 := one (c := cfg 17 n h0 (m + c) (sent (c + 1) 0) (0 + 1) (sent 0 (k + d)) (0 + 1)) (by simp [cfg])
    (s17 n h0 (m + c) _ _ _ _)
  have h17 : writeTapeBit (sent 0 (k + d)) (0 + 1) true = sent 1 (k + d - 1) := sent_add 0 (k + d)
  have w8 := one (c := cfg 18 n h0 (m + c) (sent (c + 1) 0) (0 + 1) (sent 1 (k + d - 1)) (0 + 1 + 1)) (by simp [cfg])
    (s18 n h0 (m + c) _ _ _ _)
  have h18 : writeTapeBit (sent 1 (k + d - 1)) (0 + 1 + 1) true = sent 2 (k + d - 2) := by
    have := sent_add 1 (k + d - 1)
    rw [show k + d - 1 - 1 = k + d - 2 by omega] at this
    exact this
  have w9 := one (c := cfg 19 n h0 (m + c) (sent (c + 1) 0) (0 + 1) (sent 2 (k + d - 2)) (0 + 1 + 1 - 1))
    (by simp [cfg]) (s19 n h0 (m + c) _ _ _ _)
  have t := tr (tr (tr (tr (tr (tr (tr (tr w1 w2 (by simp [hC])) w3 (by simp)) w4 rfl) w5
    (by simp)) w6 (by simp)) w7 rfl) w8 (by rw [h17])) w9 (by rw [h18])
  exact timed_congr t (by omega) rfl rfl

end Inner

/-! ## The count -/

/-- The sum of the primes `≤ n`. -/
def ps : ℕ → ℕ
  | 0 => 0
  | c + 1 => ps c + if (c + 1).Prime then c + 1 else 0

theorem ps_eq (x : ℕ) : ps x = ∑ p ∈ SupplierPrime.primesUpTo x, p := by
  induction x with
  | zero => simp [ps, SupplierPrime.primesUpTo, Finset.range_one, Finset.filter_singleton, Nat.not_prime_zero]
  | succ c ih =>
    unfold SupplierPrime.primesUpTo at *
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hp : (c + 1).Prime
    · rw [if_pos hp, Finset.sum_insert (by simp)]
      simp only [ps, if_pos hp, ih]
      omega
    · rw [if_neg hp]
      simp only [ps, if_neg hp, ih, Nat.add_zero]

section Outer
variable (n : ℕ)

/-- The outer configuration: candidate `c = j + 1`, counter head `j`. -/
def outerCfg (j m k : ℕ) : Configuration 4 22 := cfg 3 n j m (sent (j + 1) 0) 1 (sent 2 k) 1

theorem outer_one (j k : ℕ) (hj : 1 ≤ j) (hjn : j < n) : ∃ T k', T ≤ 6 * (n + 3) ^ 2 ∧
    Timed machine T (outerCfg n j (ps j) k) (outerCfg n (j + 1) (ps (j + 1)) k') := by
  have hr := read_rep n j
  have w0 := one (c := outerCfg n j (ps j) k) (by simp [outerCfg, cfg])
    (s3t n j (ps j) _ _ _ _ (by rw [hr]; simp [hjn]))
  have hc2 : 2 ≤ j + 1 := by omega
  have hmin2 : 2 ≤ Nat.minFac (j + 1) := (Nat.minFac_prime (by omega)).two_le
  have hminle := Nat.minFac_le (show 0 < j + 1 by omega)
  obtain ⟨T, k', hT, h⟩ := inner n j (ps j) (j + 1) hc2 (Nat.minFac (j + 1) - 2) 2 k (le_refl 2) (by omega)
  have hT' : T ≤ (j + 1) * (6 * (j + 1) + 10) := by
    have : Nat.minFac (j + 1) - 2 + 1 ≤ j + 1 := by omega
    calc T ≤ (Nat.minFac (j + 1) - 2 + 1) * (6 * (j + 1) + 10) := hT
      _ ≤ (j + 1) * (6 * (j + 1) + 10) := Nat.mul_le_mul_right _ this
  have hb : (j + 1) * (6 * (j + 1) + 10) + 2 * (j + 1) + 10 ≤ 6 * (n + 3) ^ 2 := by
    have h1 : j + 1 ≤ n := by omega
    nlinarith [h1, Nat.mul_le_mul h1 h1]
  rcases h with ⟨hp, w1⟩ | ⟨hp, w1⟩
  · have w3 := postP n j (ps j) (j + 1) (Nat.minFac (j + 1)) k'
    refine ⟨1 + T + (j + 1 + Nat.minFac (j + 1) + 7), k' + Nat.minFac (j + 1) - 2, by omega, ?_⟩
    have t := tr (w0.trans w1) w3 rfl
    refine timed_congr t rfl rfl ?_
    simp only [outerCfg, ps, if_pos hp]
  · have w3 := post n j (ps j) (j + 1) (Nat.minFac (j + 1)) k'
    refine ⟨1 + T + (j + 1 + Nat.minFac (j + 1) + 7), k' + Nat.minFac (j + 1) - 2, by omega, ?_⟩
    have t := tr (w0.trans w1) w3 rfl
    refine timed_congr t rfl rfl ?_
    simp only [outerCfg, ps, if_neg hp, Nat.add_zero]

theorem outer_loop : ∀ s j k, 1 ≤ j → j + s = n → ∃ T k', T ≤ s * (6 * (n + 3) ^ 2) ∧
    Timed machine T (outerCfg n j (ps j) k) (outerCfg n n (ps n) k') := by
  intro s
  induction s with
  | zero =>
    intro j k _ hjs
    refine ⟨0, k, by simp, ?_⟩
    rw [show j = n by omega]
    exact Timed.refl _ _
  | succ s ih =>
    intro j k hj hjs
    obtain ⟨T1, k1, hT1, w1⟩ := outer_one n j k hj (by omega)
    obtain ⟨T2, k2, hT2, w2⟩ := ih (j + 1) k1 (by omega) (by omega)
    refine ⟨T1 + T2, k2, ?_, w1.trans w2⟩
    have : (s + 1) * (6 * (n + 3) ^ 2) = s * (6 * (n + 3) ^ 2) + 6 * (n + 3) ^ 2 := by ring
    omega

end Outer

theorem init (n : ℕ) : Timed machine 3 (cfg 0 n 0 0 [] 0 [] 0) (outerCfg n 1 0 0) := by
  have w1 := one (c := cfg 0 n 0 0 [] 0 [] 0) (by simp [cfg]) (s0 n 0 0 [] 0 [] 0)
  have w2 := one (c := cfg 1 n 1 0 (sent 0 0) 1 (sent 0 0) 1) (by simp [cfg]) (s1 n 1 0 _ _ _ _)
  have w3 := one (c := cfg 2 n 1 0 (sent 1 0) 2 (sent 1 0) 2) (by simp [cfg]) (s2 n 1 0 _ _ _ _)
  have e1 : writeTapeBit (sent 0 0) 1 true = sent 1 0 := sent_add 0 0
  have e2 : writeTapeBit (sent 1 0) 2 true = sent 2 0 := sent_add 1 0
  have t := tr (tr w1 w2 (by simp [writeTapeBit, sent])) w3 (by rw [e1])
  exact timed_congr t rfl rfl (by simp [outerCfg, e2])

theorem ps_one : ps 1 = 0 := by simp [ps, Nat.not_prime_one]

/-- **The prime sum**: from `1^n` it writes `1^(Σ_{p ≤ n prime} p)` on tape 1 and halts. -/
theorem run (n : ℕ) : ∃ T H A, Step machine T (fun _ => 0) ![List.replicate n true, [], [], []] H A ∧
    A 1 = List.replicate (ps n) true ∧ T ≤ 6 * (n + 3) ^ 3 + 4 := by
  have w0 := init n
  obtain ⟨j, T1, k, hj, hT1, hpc, w1⟩ : ∃ j T1 k, n ≤ j ∧ T1 ≤ n * (6 * (n + 3) ^ 2) ∧ ps j = ps n ∧
      Timed machine T1 (outerCfg n 1 0 0) (outerCfg n j (ps j) k) := by
    by_cases hn : 1 ≤ n
    · obtain ⟨T, k', hT, w⟩ := outer_loop n (n - 1) 1 0 (le_refl 1) (by omega)
      refine ⟨n, T, k', le_refl n, ?_, rfl, ?_⟩
      · have := Nat.mul_le_mul_right (6 * (n + 3) ^ 2) (show n - 1 ≤ n by omega)
        omega
      · simpa [ps_one] using w
    · refine ⟨1, 0, 0, by omega, by simp, ?_, ?_⟩
      · have : n = 0 := by omega
        subst this; rfl
      · simpa [ps_one] using Timed.refl machine (outerCfg n 1 0 0)
  have hr := read_rep n j
  have w2 := one (c := outerCfg n j (ps j) k) (by simp [outerCfg, cfg])
    (s3f n j (ps j) _ _ _ _ (by rw [hr]; simp; omega))
  have t := (w0.trans w1).trans w2
  obtain ⟨r, hr', hf, hs⟩ := t.run (by simp [machine, cfg])
  refine ⟨3 + T1 + 1, _, _, ⟨r, ?_, rfl, rfl, by omega⟩, ?_, ?_⟩
  · have hc : (⟨machine.start, fun _ => 0, ![List.replicate n true, [], [], []]⟩ : Configuration 4 22) =
        cfg 0 n 0 0 [] 0 [] 0 := by
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
    rw [hc]
    exact hr'
  · rw [hf]; simp [cfg, hpc]
  · have h3 : n * (6 * (n + 3) ^ 2) ≤ 6 * (n + 3) ^ 3 :=
      calc n * (6 * (n + 3) ^ 2) ≤ (n + 3) * (6 * (n + 3) ^ 2) := Nat.mul_le_mul_right _ (by omega)
        _ = 6 * (n + 3) ^ 3 := by ring
    omega

end NearCubicWires.PacketsGlue.PrimeSum

