import Proof.Packets.PacketsNatSum
import Proof.Packets.PacketsMetaMaps

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.Clog
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.NatSum

def nw : Fin 4 → Option Bool := fun _ => none

/-- States: 0 init, 1 set the first weight cell, 2 compare, 3 rewind, 5..8 double, 9 count, 10 halt. -/
def machine : Machine 4 11 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 10
  rule := fun q b =>
    if q.val = 0 then some ⟨1, nw, ![.stay, .stay, .right, .stay]⟩
    else if q.val = 1 then some ⟨2, ![none, none, some true, none], fun _ => .stay⟩
    else if q.val = 2 then some (if b 0 then (if b 2 then ⟨2, nw, ![.right, .stay, .right, .stay]⟩
        else ⟨3, nw, ![.left, .stay, .left, .stay]⟩) else ⟨10, nw, fun _ => .stay⟩)
    else if q.val = 3 then some (if b 2 then ⟨3, nw, ![.left, .stay, .left, .stay]⟩
        else ⟨5, nw, ![.stay, .stay, .right, .stay]⟩)
    else if q.val = 5 then some ⟨6, ![none, none, none, some false], ![.stay, .stay, .stay, .right]⟩
    else if q.val = 6 then some (if b 2 then ⟨6, ![none, none, none, some true], ![.stay, .stay, .right, .right]⟩
        else ⟨7, nw, ![.stay, .stay, .stay, .left]⟩)
    else if q.val = 7 then some (if b 3 then ⟨7, ![none, none, some true, some false], ![.stay, .stay, .right, .left]⟩
        else ⟨8, nw, ![.stay, .stay, .left, .stay]⟩)
    else if q.val = 8 then some (if b 2 then ⟨8, nw, ![.stay, .stay, .left, .stay]⟩
        else ⟨9, nw, ![.stay, .stay, .right, .stay]⟩)
    else if q.val = 9 then some ⟨2, ![none, some true, none, none], ![.stay, .right, .stay, .stay]⟩
    else none

/-- Tapes: input `1^x`, output `1^o` (head at its end), weight, copy. -/
def cfg (q : Fin 11) (x xh o : ℕ) (P : List Bool) (ph : ℕ) (P2 : List Bool) (p2h : ℕ) : Configuration 4 11 :=
  ⟨q, ![xh, o, ph, p2h], ![List.replicate x true, List.replicate o true, P, P2]⟩

section Steps
variable (x xh o : ℕ) (P : List Bool) (ph : ℕ) (P2 : List Bool) (p2h : ℕ)

theorem s0 : step machine (cfg 0 x xh o P ph P2 p2h) = some (cfg 1 x xh o P (ph+1) P2 p2h) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s1 : step machine (cfg 1 x xh o P ph P2 p2h) =
    some (cfg 2 x xh o (writeTapeBit P ph true) ph P2 p2h) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s2tt (hx : readTapeBit (List.replicate x true) xh = true) (hp : readTapeBit P ph = true) :
    step machine (cfg 2 x xh o P ph P2 p2h) = some (cfg 2 x (xh+1) o P (ph+1) P2 p2h) := by
  simp [step, machine, cfg, Configuration.scanned, hx, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s2tf (hx : readTapeBit (List.replicate x true) xh = true) (hp : readTapeBit P ph = false) :
    step machine (cfg 2 x xh o P ph P2 p2h) = some (cfg 3 x (xh-1) o P (ph-1) P2 p2h) := by
  simp [step, machine, cfg, Configuration.scanned, hx, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s2f (hx : readTapeBit (List.replicate x true) xh = false) :
    step machine (cfg 2 x xh o P ph P2 p2h) = some (cfg 10 x xh o P ph P2 p2h) := by
  simp [step, machine, cfg, Configuration.scanned, hx]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s3t (hp : readTapeBit P ph = true) :
    step machine (cfg 3 x xh o P ph P2 p2h) = some (cfg 3 x (xh-1) o P (ph-1) P2 p2h) := by
  simp [step, machine, cfg, Configuration.scanned, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s3f (hp : readTapeBit P ph = false) :
    step machine (cfg 3 x xh o P ph P2 p2h) = some (cfg 5 x xh o P (ph+1) P2 p2h) := by
  simp [step, machine, cfg, Configuration.scanned, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s5 : step machine (cfg 5 x xh o P ph P2 p2h) =
    some (cfg 6 x xh o P ph (writeTapeBit P2 p2h false) (p2h+1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s6t (hp : readTapeBit P ph = true) :
    step machine (cfg 6 x xh o P ph P2 p2h) = some (cfg 6 x xh o P (ph+1) (writeTapeBit P2 p2h true) (p2h+1)) := by
  simp [step, machine, cfg, Configuration.scanned, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s6f (hp : readTapeBit P ph = false) :
    step machine (cfg 6 x xh o P ph P2 p2h) = some (cfg 7 x xh o P ph P2 (p2h-1)) := by
  simp [step, machine, cfg, Configuration.scanned, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s7t (hp : readTapeBit P2 p2h = true) :
    step machine (cfg 7 x xh o P ph P2 p2h) =
      some (cfg 7 x xh o (writeTapeBit P ph true) (ph+1) (writeTapeBit P2 p2h false) (p2h-1)) := by
  simp [step, machine, cfg, Configuration.scanned, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s7f (hp : readTapeBit P2 p2h = false) :
    step machine (cfg 7 x xh o P ph P2 p2h) = some (cfg 8 x xh o P (ph-1) P2 p2h) := by
  simp [step, machine, cfg, Configuration.scanned, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s8t (hp : readTapeBit P ph = true) :
    step machine (cfg 8 x xh o P ph P2 p2h) = some (cfg 8 x xh o P (ph-1) P2 p2h) := by
  simp [step, machine, cfg, Configuration.scanned, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s8f (hp : readTapeBit P ph = false) :
    step machine (cfg 8 x xh o P ph P2 p2h) = some (cfg 9 x xh o P (ph+1) P2 p2h) := by
  simp [step, machine, cfg, Configuration.scanned, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s9 : step machine (cfg 9 x xh o P ph P2 p2h) = some (cfg 2 x xh (o+1) P ph P2 p2h) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end_replicate]

end Steps

/-! ## Loops -/

theorem timed_congr {n n' : ℕ} {c c' d d' : Configuration 4 11} (h : Timed machine n c d)
    (hn : n = n') (hc : c = c') (hd : d = d') : Timed machine n' c' d' := by
  subst hn hc hd
  exact h

theorem tr {n m : ℕ} {c d d' e : Configuration 4 11} (h1 : Timed machine n c d) (h2 : Timed machine m d' e)
    (h : d = d') : Timed machine (n + m) c e := by
  subst h
  exact h1.trans h2

macro "ccfg_eq" : tactic => `(tactic| (congr 1 <;> first | rfl | omega | (congr 1 <;> omega)))

section Loops
variable (x : ℕ)

theorem compare_loop (o w g : ℕ) (P2 : List Bool) (p2h : ℕ) : ∀ j i : ℕ, i + j ≤ x → i + j ≤ w →
    Timed machine j (cfg 2 x i o (sent w g) (1 + i) P2 p2h) (cfg 2 x (i + j) o (sent w g) (1 + i + j) P2 p2h) := by
  intro j
  induction j with
  | zero => intro i _ _; simpa using Timed.refl machine (cfg 2 x i o (sent w g) (1 + i) P2 p2h)
  | succ j ih =>
    intro i hx hw
    have h1 : readTapeBit (List.replicate x true) i = true := read_replicate_true x i (by omega)
    have h2 : readTapeBit (sent w g) (1 + i) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s2tt x i o (sent w g) (1 + i) P2 p2h h1 h2)
    have t2 := ih (i + 1) (by omega) (by omega)
    have e := tr t1 t2 (by ccfg_eq)
    exact timed_congr e (by omega) rfl (by ccfg_eq)

theorem rewind3 (o w g : ℕ) (P2 : List Bool) (p2h : ℕ) : ∀ p : ℕ, p ≤ w →
    Timed machine (p + 1) (cfg 3 x (p - 1) o (sent w g) p P2 p2h) (cfg 5 x 0 o (sent w g) 1 P2 p2h) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sent w g) 0 = false := rfl
    simpa using Timed.single (p := machine) (by rfl) (s3f x (0 - 1) o (sent w g) 0 P2 p2h h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sent w g) (p + 1) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s3t x (p + 1 - 1) o (sent w g) (p + 1) P2 p2h h)
    have e := tr t1 (ih (by omega)) (by ccfg_eq)
    exact timed_congr e (by omega) rfl rfl

theorem copy6 (o w gw : ℕ) : ∀ j t g2 : ℕ, t + j ≤ w →
    Timed machine j (cfg 6 x 0 o (sent w gw) (1 + t) (sent t g2) (1 + t))
      (cfg 6 x 0 o (sent w gw) (1 + t + j) (sent (t + j) (g2 - j)) (1 + t + j)) := by
  intro j
  induction j with
  | zero => intro t g2 _; simpa using Timed.refl machine (cfg 6 x 0 o (sent w gw) (1 + t) (sent t g2) (1 + t))
  | succ j ih =>
    intro t g2 hj
    have h : readTapeBit (sent w gw) (1 + t) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s6t x 0 o (sent w gw) (1 + t) (sent t g2) (1 + t) h)
    rw [show 1 + t = t + 1 by omega, sent_add] at t1
    have t2 := ih (t + 1) (g2 - 1) (by omega)
    have e := tr t1 t2 (by ccfg_eq)
    exact timed_congr e (by omega) (by ccfg_eq) (by ccfg_eq)

theorem append7 (o : ℕ) : ∀ b a gw g2 : ℕ,
    Timed machine b (cfg 7 x 0 o (sent a gw) (a + 1) (sent b g2) b)
      (cfg 7 x 0 o (sent (a + b) (gw - b)) (a + b + 1) (sent 0 (g2 + b)) 0) := by
  intro b
  induction b with
  | zero => intro a gw g2; simpa using Timed.refl machine (cfg 7 x 0 o (sent a gw) (a + 1) (sent 0 g2) 0)
  | succ b ih =>
    intro a gw g2
    have h : readTapeBit (sent (b + 1) g2) (b + 1) = true := by rw [read_sent]; simp
    have t1 := Timed.single (p := machine) (by rfl) (s7t x 0 o (sent a gw) (a + 1) (sent (b + 1) g2) (b + 1) h)
    rw [sent_add, sent_erase, show b + 1 - 1 = b by omega] at t1
    have t2 := ih (a + 1) (gw - 1) (g2 + 1)
    have e := tr t1 t2 (by ccfg_eq)
    exact timed_congr e (by omega) rfl (by ccfg_eq)

theorem rewind8 (o w g : ℕ) (P2 : List Bool) (p2h : ℕ) : ∀ p : ℕ, p ≤ w →
    Timed machine (p + 1) (cfg 8 x 0 o (sent w g) p P2 p2h) (cfg 9 x 0 o (sent w g) 1 P2 p2h) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sent w g) 0 = false := rfl
    simpa using Timed.single (p := machine) (by rfl) (s8f x 0 o (sent w g) 0 P2 p2h h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sent w g) (p + 1) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s8t x 0 o (sent w g) (p + 1) P2 p2h h)
    rw [show p + 1 - 1 = p by omega] at t1
    have e := tr t1 (ih (by omega)) rfl
    exact timed_congr e (by omega) rfl rfl

/-- **One round**: `P = 2^k < x`; compare, rewind, double, count. -/
theorem round (o w gw k2 : ℕ) (hw : 1 ≤ w) (hwx : w < x) :
    ∃ gw' k2' : ℕ, Timed machine (6 * w + 7)
      (cfg 2 x 0 o (sent w gw) 1 (List.replicate k2 false) 0)
      (cfg 2 x 0 (o + 1) (sent (2 * w) gw') 1 (List.replicate k2' false) 0) := by
  have t1 := compare_loop x o w gw (List.replicate k2 false) 0 w 0 (by omega) (by omega)
  have h1 : readTapeBit (List.replicate x true) (0 + w) = true := read_replicate_true x _ (by omega)
  have h2 : readTapeBit (sent w gw) (1 + 0 + w) = false := by rw [read_sent]; simp
  have t2 := Timed.single (p := machine) (by rfl)
    (s2tf x (0 + w) o (sent w gw) (1 + 0 + w) (List.replicate k2 false) 0 h1 h2)
  have t3 := rewind3 x o w gw (List.replicate k2 false) 0 w (le_refl _)
  have t4 := Timed.single (p := machine) (by rfl) (s5 x 0 o (sent w gw) 1 (List.replicate k2 false) 0)
  rw [blank_zero] at t4
  have t5 := copy6 x o w gw w 0 (k2 - 1) (by omega)
  have hf : readTapeBit (sent w gw) (1 + 0 + w) = false := by rw [read_sent]; simp
  have t6 := Timed.single (p := machine) (by rfl)
    (s6f x 0 o (sent w gw) (1 + 0 + w) (sent (0 + w) (k2 - 1 - w)) (1 + 0 + w) hf)
  have t7 := append7 x o w w gw (k2 - 1 - w)
  have hf2 : readTapeBit (sent 0 (k2 - 1 - w + w)) 0 = false := rfl
  have t8 := Timed.single (p := machine) (by rfl)
    (s7f x 0 o (sent (w + w) (gw - w)) (w + w + 1) (sent 0 (k2 - 1 - w + w)) 0 hf2)
  have t9 := rewind8 x o (w + w) (gw - w) (sent 0 (k2 - 1 - w + w)) 0 (w + w) (le_refl _)
  have t10 := Timed.single (p := machine) (by rfl)
    (s9 x 0 o (sent (w + w) (gw - w)) 1 (sent 0 (k2 - 1 - w + w)) 0)
  have e1 := tr t1 t2 (by ccfg_eq)
  have e2 := tr e1 t3 (by ccfg_eq)
  have e3 := tr e2 t4 (by ccfg_eq)
  have e4 := tr e3 t5 (by ccfg_eq)
  have e5 := tr e4 t6 (by ccfg_eq)
  have e6 := tr e5 t7 (by ccfg_eq)
  have e7 := tr e6 t8 (by ccfg_eq)
  have e8 := tr e7 t9 (by ccfg_eq)
  have e9 := tr e8 t10 rfl
  rw [sent_zero] at e9
  exact ⟨gw - w, k2 - 1 - w + w + 1, timed_congr e9 (by omega) rfl (by ccfg_eq)⟩

theorem finish (o w gw k2 : ℕ) (hxw : x ≤ w) :
    Timed machine (x + 1) (cfg 2 x 0 o (sent w gw) 1 (List.replicate k2 false) 0)
      (cfg 10 x x o (sent w gw) (1 + x) (List.replicate k2 false) 0) := by
  have t1 := compare_loop x o w gw (List.replicate k2 false) 0 x 0 (by omega) (by omega)
  have h1 : readTapeBit (List.replicate x true) (0 + x) = false := by
    rw [Nat.zero_add]; exact read_replicate_end x true
  have t2 := Timed.single (p := machine) (by rfl)
    (s2f x (0 + x) o (sent w gw) (1 + 0 + x) (List.replicate k2 false) 0 h1)
  have e := tr t1 t2 (by ccfg_eq)
  exact timed_congr e rfl (by ccfg_eq) (by ccfg_eq)

/-- **The rounds.** From weight `2^k` with `k ≤ clog x`, the machine halts with `clog x - k` more output
ones. -/
theorem rounds : ∀ (n k o gw k2 : ℕ), n = Nat.clog 2 x - k → k ≤ Nat.clog 2 x →
    ∃ T gw' k2' : ℕ, Timed machine T (cfg 2 x 0 o (sent (2 ^ k) gw) 1 (List.replicate k2 false) 0)
      (cfg 10 x x (o + n) (sent (2 ^ Nat.clog 2 x) gw') (1 + x) (List.replicate k2' false) 0) ∧
      T + 6 * 2 ^ k ≤ 6 * 2 ^ Nat.clog 2 x + 8 * n + x + 1 := by
  intro n
  induction n with
  | zero =>
    intro k o gw k2 hn hk
    have hkk : k = Nat.clog 2 x := by omega
    subst hkk
    have hxw : x ≤ 2 ^ Nat.clog 2 x := Nat.le_pow_clog (by norm_num) x
    exact ⟨_, gw, k2, finish x o _ gw k2 hxw, by omega⟩
  | succ n ih =>
    intro k o gw k2 hn hk
    have hlt : k < Nat.clog 2 x := by omega
    have hwx : 2 ^ k < x := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mp hlt
    obtain ⟨gw1, k21, t1⟩ := round x o (2 ^ k) gw k2 (Nat.one_le_two_pow) hwx
    obtain ⟨T, gw', k2', t2, hT⟩ := ih (k + 1) (o + 1) gw1 k21 (by omega) (by omega)
    rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring] at t1
    have e := tr t1 t2 rfl
    refine ⟨_, gw', k2', timed_congr e rfl rfl (by ccfg_eq), ?_⟩
    rw [pow_succ] at hT
    omega

end Loops

/-- **`⌈log₂ x⌉` in unary.** -/
theorem run (x : ℕ) : ∃ (n : ℕ) (H1 : Fin 4 → ℕ) (A1 : Fin 4 → List Bool),
    Step machine n (fun _ => 0) ![List.replicate x true, [], [], []] H1 A1 ∧
    A1 1 = List.replicate (Nat.clog 2 x) true ∧ n ≤ 30 * (x + 1) := by
  have t1 := Timed.single (p := machine) (by rfl) (s0 x 0 0 [] 0 [] 0)
  have t2 := Timed.single (p := machine) (by rfl) (s1 x 0 0 [] (0 + 1) [] 0)
  have hw : writeTapeBit ([] : List Bool) (0 + 1) true = sent (2 ^ 0) 0 := by rfl
  rw [hw] at t2
  obtain ⟨T, gw', k2', t3, hT⟩ := rounds x (Nat.clog 2 x) 0 0 0 0 (by omega) (by omega)
  have e := (tr t1 t2 rfl).trans (timed_congr t3 rfl (by ccfg_eq) rfl)
  obtain ⟨r, hr, hf, hs⟩ := e.run rfl
  have hc : (⟨machine.start, fun _ => 0, ![List.replicate x true, [], [], []]⟩ : Configuration 4 11) =
      cfg 0 x 0 0 [] 0 [] 0 := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [← hc] at hr
  refine ⟨_, r.final.heads, r.final.tapes, ⟨r, hr, rfl, rfl, le_of_eq hs⟩, ?_, ?_⟩
  · rw [hf]; simp [cfg]
  · have hK : 2 ^ Nat.clog 2 x ≤ 2 * x + 1 := by
      rcases Nat.lt_or_ge x 2 with hx | hx
      · interval_cases x <;> simp
      · have h := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < x)
        rw [Nat.pred_eq_sub_one] at h
        have hpos : 0 < Nat.clog 2 x := Nat.clog_pos (by norm_num) (by omega)
        have : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x - 1) := by
          rw [← pow_succ']; congr 1; omega
        omega
    have hk : Nat.clog 2 x ≤ 2 ^ Nat.clog 2 x := (Nat.lt_two_pow_self).le
    omega

end NearCubicWires.PacketsGlue.Clog

