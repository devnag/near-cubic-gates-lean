import Proof.Packets.PacketsGate

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsGlue.CeilSqrt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.CanonicalFourfoldRowProgram

def nw : Fin 3 → Option Bool := fun _ => none

def act (q : Fin 7) (w : Fin 3 → Option Bool) (m : Fin 3 → HeadMove) : Option (Action 3 7) :=
  some ⟨q, w, m⟩

/-- Tapes: 0 the input `1^x` (head at `c²`), 1 the output `1^c` (head at its end), 2 the counter `false :: 1^c`.
States: 0 counter sentinel, 1 test `c² < x`, 2 enter counter, 3/4 walk `2c`, 5 rewind counter, 6 halt. -/
def machine : Machine 3 7 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 6
  rule := fun q b =>
    if q.val = 0 then act 1 ![none, none, some false] ![.stay, .stay, .stay]
    else if q.val = 1 then (if b 0 then act 2 ![none, some true, none] ![.stay, .right, .stay]
      else act 6 nw ![.stay, .stay, .stay])
    else if q.val = 2 then act 3 nw ![.stay, .stay, .right]
    else if q.val = 3 then (if b 2 then act 4 nw ![.right, .stay, .stay]
      else act 5 ![none, none, some true] ![.right, .stay, .stay])
    else if q.val = 4 then act 3 nw ![.right, .stay, .right]
    else if q.val = 5 then (if b 2 then act 5 nw ![.stay, .stay, .left]
      else act 1 nw ![.stay, .stay, .stay])
    else none

def cfg (q : Fin 7) (X : List Bool) (xh : ℕ) (O : List Bool) (oh : ℕ) (C : List Bool) (ch : ℕ) :
    Configuration 3 7 :=
  ⟨q, ![xh, oh, ch], ![X, O, C]⟩

/-- The counter: a sentinel, then `c` ones. -/
def sentC (c : ℕ) : List Bool := false :: List.replicate c true

section Steps
variable (X : List Bool) (xh : ℕ) (O : List Bool) (oh : ℕ) (C : List Bool) (ch : ℕ)

theorem s0 : step machine (cfg 0 X xh O oh C ch) = some (cfg 1 X xh O oh (writeTapeBit C ch false) ch) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s1t (h : readTapeBit X xh = true) :
    step machine (cfg 1 X xh O oh C ch) = some (cfg 2 X xh (writeTapeBit O oh true) (oh + 1) C ch) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s1f (h : readTapeBit X xh = false) :
    step machine (cfg 1 X xh O oh C ch) = some (cfg 6 X xh O oh C ch) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s2 : step machine (cfg 2 X xh O oh C ch) = some (cfg 3 X xh O oh C (ch + 1)) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s3t (h : readTapeBit C ch = true) :
    step machine (cfg 3 X xh O oh C ch) = some (cfg 4 X (xh + 1) O oh C ch) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s3f (h : readTapeBit C ch = false) :
    step machine (cfg 3 X xh O oh C ch) = some (cfg 5 X (xh + 1) O oh (writeTapeBit C ch true) ch) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s4 : step machine (cfg 4 X xh O oh C ch) = some (cfg 3 X (xh + 1) O oh C (ch + 1)) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s5t (h : readTapeBit C ch = true) :
    step machine (cfg 5 X xh O oh C ch) = some (cfg 5 X xh O oh C (ch - 1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s5f (h : readTapeBit C ch = false) :
    step machine (cfg 5 X xh O oh C ch) = some (cfg 1 X xh O oh C ch) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

end Steps

/-! ## Tape facts -/

theorem read_rep (x i : ℕ) : readTapeBit (List.replicate x true) i = decide (i < x) := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < x
  · simp [h]
  · simp [h]

theorem read_sent (c i : ℕ) : readTapeBit (sentC c) i = decide (1 ≤ i ∧ i ≤ c) := by
  cases i with
  | zero => rfl
  | succ i =>
    unfold sentC readTapeBit
    simp only [List.getD_cons_succ]
    have := read_rep c i
    unfold readTapeBit at this
    rw [this]
    simp

theorem write_rep (c : ℕ) : writeTapeBit (List.replicate c true) c true = List.replicate (c + 1) true := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [List.replicate_succ, List.replicate_succ]
    simp only [writeTapeBit, ih]

theorem write_sent (c : ℕ) : writeTapeBit (sentC c) (c + 1) true = sentC (c + 1) := by
  unfold sentC
  simp only [writeTapeBit, write_rep]

/-! ## Loops -/

theorem timed_congr {n n' : ℕ} {c c' d d' : Configuration 3 7} (h : Timed machine n c d)
    (hn : n = n') (hc : c = c') (hd : d = d') : Timed machine n' c' d' := by
  subst hn hc hd
  exact h

theorem tr {n m : ℕ} {c d d' e : Configuration 3 7} (h1 : Timed machine n c d) (h2 : Timed machine m d' e)
    (h : d = d') : Timed machine (n + m) c e := by
  subst h
  exact h1.trans h2

/-- The walk: two input cells per counter one. -/
theorem walk (X O : List Bool) (oh c : ℕ) : ∀ j p xh : ℕ, 1 ≤ p → p + j ≤ c + 1 →
    Timed machine (2 * j) (cfg 3 X xh O oh (sentC c) p) (cfg 3 X (xh + 2 * j) O oh (sentC c) (p + j)) := by
  intro j
  induction j with
  | zero => intro p xh _ _; simpa using Timed.refl machine (cfg 3 X xh O oh (sentC c) p)
  | succ j ih =>
    intro p xh hp hj
    have h : readTapeBit (sentC c) p = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s3t X xh O oh (sentC c) p h)
    have t2 := Timed.single (p := machine) (by rfl) (s4 X (xh + 1) O oh (sentC c) p)
    have t3 := ih (p + 1) (xh + 1 + 1) (by omega) (by omega)
    have tt := tr (tr t1 t2 rfl) t3 rfl
    exact timed_congr tt (by omega) rfl (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))

/-- The counter rewind, ending on its sentinel. -/
theorem rewind (X O : List Bool) (xh oh c : ℕ) : ∀ p : ℕ, p ≤ c →
    Timed machine (p + 1) (cfg 5 X xh O oh (sentC c) p) (cfg 1 X xh O oh (sentC c) 0) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sentC c) 0 = false := rfl
    simpa using Timed.single (p := machine) (by rfl) (s5f X xh O oh (sentC c) 0 h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sentC c) (p + 1) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s5t X xh O oh (sentC c) (p + 1) h)
    rw [show p + 1 - 1 = p by omega] at t1
    have tt := tr t1 (ih (by omega)) rfl
    exact timed_congr tt (by omega) rfl rfl

/-- **One round**: `c² < x` ⇒ the output grows to `1^(c+1)` and the input head reaches `(c+1)²`. -/
theorem round (x c : ℕ) (hc : c * c < x) :
    Timed machine (3 * c + 5)
      (cfg 1 (List.replicate x true) (c * c) (List.replicate c true) c (sentC c) 0)
      (cfg 1 (List.replicate x true) ((c + 1) * (c + 1)) (List.replicate (c + 1) true) (c + 1)
        (sentC (c + 1)) 0) := by
  have h1 : readTapeBit (List.replicate x true) (c * c) = true := by rw [read_rep]; simp; omega
  have t1 := Timed.single (p := machine) (by rfl)
    (s1t (List.replicate x true) (c * c) (List.replicate c true) c (sentC c) 0 h1)
  rw [write_rep] at t1
  have t2 := Timed.single (p := machine) (by rfl)
    (s2 (List.replicate x true) (c * c) (List.replicate (c + 1) true) (c + 1) (sentC c) 0)
  have t3 := walk (List.replicate x true) (List.replicate (c + 1) true) (c + 1) c c (0 + 1) (c * c)
    (by omega) (by omega)
  rw [show 0 + 1 + c = c + 1 by omega] at t3
  have hf : readTapeBit (sentC c) (c + 1) = false := by rw [read_sent]; simp
  have t4 := Timed.single (p := machine) (by rfl)
    (s3f (List.replicate x true) (c * c + 2 * c) (List.replicate (c + 1) true) (c + 1) (sentC c) (c + 1) hf)
  rw [write_sent] at t4
  have t5 := rewind (List.replicate x true) (List.replicate (c + 1) true) (c * c + 2 * c + 1) (c + 1) (c + 1)
    (c + 1) (le_refl _)
  have e1 := tr t1 t2 rfl
  have e2 := tr e1 t3 rfl
  have e3 := tr e2 t4 rfl
  have e4 := tr e3 t5 rfl
  exact timed_congr e4 (by omega) rfl (by congr 1; ring)

/-- **The rounds**, up to any `k ≤ natCeilSqrt x`. -/
theorem rounds (x : ℕ) : ∀ k : ℕ, k ≤ natCeilSqrt x → ∃ T : ℕ, T ≤ k * (3 * k + 5) ∧
    Timed machine T (cfg 1 (List.replicate x true) 0 [] 0 (sentC 0) 0)
      (cfg 1 (List.replicate x true) (k * k) (List.replicate k true) k (sentC k) 0) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨0, le_refl _, Timed.refl _ _⟩
  | succ k ih =>
    intro hk
    obtain ⟨T, hT, t⟩ := ih (by omega)
    have hc : k * k < x := sq_lt_of_lt_natCeilSqrt (by omega)
    refine ⟨T + (3 * k + 5), by nlinarith, t.trans (round x k hc)⟩

theorem ceil_le (x : ℕ) : natCeilSqrt x ≤ x + 1 := by
  have := Nat.sqrt_le_self x
  show (if Nat.sqrt x * Nat.sqrt x = x then Nat.sqrt x else Nat.sqrt x + 1) ≤ x + 1
  split_ifs <;> omega

/-- **The run.** From `1^x` (all else blank, heads `0`) to `1^(natCeilSqrt x)` on tape 1. -/
theorem run (x : ℕ) : ∃ (n : ℕ) (H1 : Fin 3 → ℕ) (A1 : Fin 3 → List Bool),
    Step machine n (fun _ => 0) ![List.replicate x true, [], []] H1 A1 ∧
    A1 1 = List.replicate (natCeilSqrt x) true ∧ n ≤ 2 + (x + 1) * (3 * x + 8) := by
  set m := natCeilSqrt x with hm
  have t0 := Timed.single (p := machine) (by rfl) (s0 (List.replicate x true) 0 [] 0 [] 0)
  have e0 : writeTapeBit ([] : List Bool) 0 false = sentC 0 := rfl
  rw [e0] at t0
  obtain ⟨T, hT, t1⟩ := rounds x m (le_refl _)
  have hsq : x ≤ m * m := le_natCeilSqrt_sq x
  have hf : readTapeBit (List.replicate x true) (m * m) = false := by rw [read_rep]; simp; omega
  have t2 := Timed.single (p := machine) (by rfl)
    (s1f (List.replicate x true) (m * m) (List.replicate m true) m (sentC m) 0 hf)
  have e := tr (tr t0 t1 rfl) t2 rfl
  have s := NatAt.Timed.toStep e rfl rfl
  have hin : (cfg 0 (List.replicate x true) 0 [] 0 [] 0).tapes = ![List.replicate x true, [], []] := rfl
  have hh : (cfg 0 (List.replicate x true) 0 [] 0 [] 0).heads = fun _ => 0 := by
    funext i; fin_cases i <;> rfl
  rw [hin, hh] at s
  refine ⟨_, _, _, s, rfl, ?_⟩
  have hml := ceil_le x
  have hmk : m * (3 * m + 5) ≤ (x + 1) * (3 * (x + 1) + 5) := Nat.mul_le_mul hml (by omega)
  nlinarith

end NearCubicWires.PacketsGlue.CeilSqrt

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent NearCubicWires.CanonicalFourfoldRowProgram
noncomputable section

/-- **`⌈√x⌉` in unary.** -/
def ceilSqrtMap : UnaryMap (fun x => natCeilSqrt x) where
  extra := 2
  states := 7 + 2
  machine := MaskedReset.machine PacketsGlue.CeilSqrt.machine (fun _ => true)
  cost := fun x => 2 * (2 + (x + 1) * (3 * x + 8)) + 2
  run := by
    intro x
    obtain ⟨n, H1, A1, hs, hv, hn⟩ := PacketsGlue.CeilSqrt.run x
    obtain ⟨k, hm⟩ := step_mask0 (hs.enlarge hn) (fun _ => true) (by intro i _; rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn]
    · have hc : (⟨1, by omega⟩ : Fin (2 + 2)) = Fin.castAdd 1 (1 : Fin 3) := rfl
      rw [hc, Fin.addCases_left, hv]
    · have hc : (⟨1, by omega⟩ : Fin (2 + 2)) = Fin.castAdd 1 (1 : Fin 3) := rfl
      rw [hc, Fin.addCases_left]
      rfl

theorem ceilSqrt_cost (x : ℕ) : ceilSqrtMap.cost x ≤ 8 * (x + 3) ^ 2 := by
  change 2 * (2 + (x + 1) * (3 * x + 8)) + 2 ≤ _
  nlinarith

def rootStage (a : DecompositionAlgorithm) : UnaryStage a (fun r => natCeilSqrt (64 ^ 2 * touch a r)) :=
  (((touchStage a).thenMapP (scaleMap 4096) (4 * 4096 + 12) 2 (scale_cost 4096)).thenMapP ceilSqrtMap 8 2
    ceilSqrt_cost).ofEq (by
      intro r
      show natCeilSqrt (touch a r * 4096) = natCeilSqrt (64 ^ 2 * touch a r)
      congr 1
      ring)

end
end NearCubicWires.PacketsGlue.RequestMeta

