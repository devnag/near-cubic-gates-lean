import SourceAdapters.Amplification.NetCount
import NineInputs
import Bindings.TuringBridge.Core

/-!
# A02 step (a): an STV randomized oracle machine, run for `T` steps on fixed coins, as a net

STV's proof of Theorem 24 turns the reconstruction's oracle machines into a circuit ("express `M_j^B` as a
circuit"); `app:sources`, "Full-range amplification interface": "yields an exact circuit … The polynomial reconstruction overhead includes fixing the
decoder's randomness and conversion to our fan-in-two basis". This module is that conversion, non-uniformly
(only the existence of the circuit and its size are needed), in the leaf's own model
`STV.OracleMachine` (multitape bit machine, oracle answers written on the answer tape, field-element output).

* `tstep`: one transition with the oracle, frozen on halting or on a missing rule; `oracleRun_tstep`: a run of
  the leaf that halts within `fuel` steps ends in `tstep^[N]` for every `N ≥ fuel`.
* `enc b P`: a configuration as bits — the control state in `b` binary digits, every head one-hot and every tape
  cell over the first `P` positions.
* `stepV`: the vector step (scan, control table, tape update, oracle answer); `stepV_enc`: it commutes with
  `tstep` under `enc` while every head is below `P`.
* `real_stepV`, `real_run`: nets for one step and for `T` steps from the initial configuration, with node count
  polynomial in `P`, the description `stateCount·2^tapeCount`, and the oracle net's size.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicGates.Published.STV

/-! ## Any of a list, as a net -/

theorem foldl_or {ι : Type} (F : ι → Bool) :
    ∀ (l : List ι) (s : Unit → Bool), l.foldl (fun s i => fun _ => s () || F i) s = fun _ => s () || l.any F
  | [], s => by funext u; simp
  | i :: l, s => by
      rw [List.foldl_cons, foldl_or F l]
      funext u
      simp [Bool.or_assoc]

/-- **Disjunction over a list** of local functions. -/
theorem Real.any {α ι : Type} (a : ℕ) (l : List ι) (g : ι → Fin a → α) (f : ι → (Fin a → Bool) → Bool) :
    Real (1 + l.length * (1 * ((a + 1) + 8 * 2 ^ (a + 1))))
      (fun x (_ : Unit) => l.any (fun i => f i (fun k => x (g i k)))) := by
  have h0 : Real 1 (fun (_ : α → Bool) (_ : Unit) => false) := by
    have := Real.leaves (α := α) (fun _ : Fin 1 => (Sum.inl false : Bool ⊕ α))
    exact (this.reindex (fun _ : Unit => (0 : Fin 1))).congr fun _ _ => rfl
  have h := Real.foldList (σ := Unit) (c := 1 * ((a + 1) + 8 * 2 ^ (a + 1)))
    (fun i s x => fun _ => s () || f i (fun k => x (g i k))) l (fun _ _ => false) h0 (fun i _ => by
      have hl := Real.local (α := α ⊕ Unit) (β := Unit) (a + 1)
        (fun _ => Fin.cons (Sum.inr ()) (fun k => Sum.inl (g i k)))
        (fun _ v => v 0 || f i (fun k => v k.succ))
      rw [Fintype.card_unit] at hl
      exact hl.congr fun z u => by simp)
  refine h.congr fun x u => ?_
  rw [foldl_or (fun i => f i (fun k => x (g i k))) l]
  simp

/-! ## Total steps -/

variable (M : OracleMachine)

/-- One transition with oracle `O`, frozen on a halting state or a missing rule. -/
def tstep (O : List Bool → List Bool) (c : Configuration M.tapeCount M.stateCount) :
    Configuration M.tapeCount M.stateCount :=
  if M.machine.halted c.control then c else (M.oracleStep O c).getD c

theorem oracleRun_tstep (O : List Bool → List Bool) :
    ∀ (fuel : ℕ) (c c' : Configuration M.tapeCount M.stateCount), M.oracleRun O fuel c = some c' →
      ∀ N, fuel ≤ N → (tstep M O)^[N] c = c'
  | 0, c, c', h, N, _ => by
      simp only [OracleMachine.oracleRun] at h
      split_ifs at h with hh
      cases h
      exact Function.iterate_fixed (by simp [tstep, hh]) N
  | fuel + 1, c, c', h, N, hN => by
      simp only [OracleMachine.oracleRun] at h
      split_ifs at h with hh
      · cases h
        exact Function.iterate_fixed (by simp [tstep, hh]) N
      · cases hs : M.oracleStep O c with
        | none => rw [hs] at h; cases h
        | some c'' =>
            rw [hs] at h
            obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
            rw [Function.iterate_succ_apply]
            have : tstep M O c = c'' := by simp [tstep, hh, hs]
            rw [this]
            exact oracleRun_tstep O fuel c'' c' h N' (by omega)

/-- A halting run and any later total iterate agree. -/
theorem oracleRun_eq_iterate (O : List Bool → List Bool) (fuel N : ℕ) (hN : fuel ≤ N)
    (c c' : Configuration M.tapeCount M.stateCount) (h : M.oracleRun O fuel c = some c') :
    (tstep M O)^[N] c = c' :=
  oracleRun_tstep M O fuel c c' h N hN

theorem heads_applyAction {τ Q : ℕ} (c : Configuration τ Q) (a : Action τ Q) (i : Fin τ) :
    (applyAction c a).heads i ≤ c.heads i + 1 := by
  simp only [applyAction]
  cases a.move i <;> (simp only [HeadMove.apply]; omega)

theorem heads_tstep (O : List Bool → List Bool) (c : Configuration M.tapeCount M.stateCount) (i : Fin M.tapeCount) :
    (tstep M O c).heads i ≤ c.heads i + 1 := by
  unfold tstep
  split_ifs with hh
  · omega
  · cases hs : M.oracleStep O c with
    | none => simp
    | some c'' =>
        simp only [Option.getD_some]
        simp only [OracleMachine.oracleStep, step] at hs
        cases hr : M.machine.rule c.control c.scanned with
        | none => rw [hr] at hs; simp at hs
        | some a =>
            rw [hr] at hs
            simp only [Option.map_some, Option.some.injEq] at hs
            rw [← hs]
            split_ifs
            · simp only [Function.update_apply]
              split_ifs
              · omega
              · exact heads_applyAction c a i
            · exact heads_applyAction c a i

theorem heads_iterate (O : List Bool → List Bool) (c : Configuration M.tapeCount M.stateCount)
    (hc : ∀ i, c.heads i = 0) : ∀ (s : ℕ) (i : Fin M.tapeCount), ((tstep M O)^[s] c).heads i ≤ s
  | 0, i => by simp [hc i]
  | s + 1, i => by
      rw [Function.iterate_succ_apply']
      have := heads_tstep M O ((tstep M O)^[s] c) i
      have := heads_iterate O c hc s i
      omega

/-! ## Configurations as bit vectors -/

/-- Bit positions: `b` control digits, then head bits and cell bits for every tape and position `< P`. -/
abbrev CIdx (τ b P : ℕ) : Type := Fin b ⊕ (Fin τ × Fin P) ⊕ (Fin τ × Fin P)

/-- The head bit of tape `i` at position `p`. -/
def hd {τ b P : ℕ} (i : Fin τ) (p : Fin P) : CIdx τ b P := Sum.inr (Sum.inl (i, p))

/-- The cell bit of tape `i` at position `p`. -/
def cl {τ b P : ℕ} (i : Fin τ) (p : Fin P) : CIdx τ b P := Sum.inr (Sum.inr (i, p))

/-- The binary digits of a state. -/
def code (b : ℕ) {Q : ℕ} (s : Fin Q) : Fin b → Bool := fun j => s.val.testBit j.val

theorem code_injective {b Q : ℕ} (hb : Q ≤ 2 ^ b) : Function.Injective (code b (Q := Q)) := by
  intro s s' h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < b
  · exact congrFun h ⟨j, hj⟩
  · have h1 : s.val < 2 ^ j := lt_of_lt_of_le s.isLt (hb.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h2 : s'.val < 2 ^ j := lt_of_lt_of_le s'.isLt (hb.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

/-- The configuration `c` as bits. -/
def enc (b P : ℕ) (c : Configuration M.tapeCount M.stateCount) : CIdx M.tapeCount b P → Bool :=
  Sum.elim (code b c.control)
    (Sum.elim (fun ip => decide (c.heads ip.1 = ip.2.val)) (fun ip => readTapeBit (c.tapes ip.1) ip.2.val))

/-- The scanned bit of every tape: some position holds both the head and a `1`. -/
def scan {τ b P : ℕ} (x : CIdx τ b P → Bool) (i : Fin τ) : Bool :=
  (List.finRange P).any (fun p => x (hd i p) && x (cl i p))

theorem scan_enc (b P : ℕ) (c : Configuration M.tapeCount M.stateCount) (hP : ∀ i, c.heads i < P) :
    scan (enc M b P c) = c.scanned := by
  funext i
  simp only [scan, Configuration.scanned]
  rw [Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨p, -, hp⟩
    simp only [enc, hd, cl, Sum.elim_inr, Sum.elim_inl, Bool.and_eq_true, decide_eq_true_eq] at hp
    rw [hp.1]; exact hp.2
  · intro h
    refine ⟨⟨c.heads i, hP i⟩, List.mem_finRange _, ?_⟩
    simp [enc, hd, cl, h]

/-! ## The control table -/

/-- The action of the control table on state digits `v` and scanned bits `sc` (`none`: frozen). -/
noncomputable def ctlAct (b : ℕ) (v : Fin b → Bool) (sc : Fin M.tapeCount → Bool) :
    Option (Action M.tapeCount M.stateCount) :=
  if h : ∃ s : Fin M.stateCount, code b s = v then
    (if M.machine.halted (Classical.choose h) then none else M.machine.rule (Classical.choose h) sc)
  else none

theorem ctlAct_code {b : ℕ} (hb : M.stateCount ≤ 2 ^ b) (s : Fin M.stateCount) (sc : Fin M.tapeCount → Bool) :
    ctlAct M b (code b s) sc = if M.machine.halted s then none else M.machine.rule s sc := by
  have h : ∃ s' : Fin M.stateCount, code b s' = code b s := ⟨s, rfl⟩
  have hs : Classical.choose h = s := code_injective hb (Classical.choose_spec h)
  simp only [ctlAct, dif_pos h, hs]

/-- Control outputs: next digits, per tape (writes?, written bit, left?, right?), active?, asks?. -/
abbrev KIdx (τ b : ℕ) : Type := Fin b ⊕ (Fin τ × Fin 4) ⊕ Fin 2

def kA {τ b : ℕ} : KIdx τ b := Sum.inr (Sum.inr 0)
def kAsk {τ b : ℕ} : KIdx τ b := Sum.inr (Sum.inr 1)
def kWr {τ b : ℕ} (i : Fin τ) : KIdx τ b := Sum.inr (Sum.inl (i, 0))
def kWv {τ b : ℕ} (i : Fin τ) : KIdx τ b := Sum.inr (Sum.inl (i, 1))
def kLf {τ b : ℕ} (i : Fin τ) : KIdx τ b := Sum.inr (Sum.inl (i, 2))
def kRt {τ b : ℕ} (i : Fin τ) : KIdx τ b := Sum.inr (Sum.inl (i, 3))

/-- The control outputs as bits. -/
noncomputable def ctlOut (b : ℕ) (v : Fin b → Bool) (sc : Fin M.tapeCount → Bool) : KIdx M.tapeCount b → Bool :=
  match ctlAct M b v sc with
  | none => Sum.elim v (fun _ => false)
  | some a => Sum.elim (code b a.nextControl) (Sum.elim
      (fun ik => ![(a.write ik.1).isSome, (a.write ik.1).getD false, decide (a.move ik.1 = HeadMove.left),
        decide (a.move ik.1 = HeadMove.right)] ik.2)
      (fun e => ![true, M.asks a.nextControl] e))

/-! ## The tape update and the oracle answer -/

/-- The new head bit at `(i, p)`. -/
def preHead {τ b P : ℕ} (x : CIdx τ b P → Bool) (y : KIdx τ b → Bool) (i : Fin τ) (p : Fin P) : Bool :=
  if y kA then
    (y (kLf i) && ((if h : p.val + 1 < P then x (hd i ⟨p.val + 1, h⟩) else false) ||
        (decide (p.val = 0) && x (hd i p)))) ||
      (y (kRt i) && (if h : 1 ≤ p.val then x (hd i ⟨p.val - 1, by omega⟩) else false)) ||
      (!y (kLf i) && !y (kRt i) && x (hd i p))
  else x (hd i p)

/-- The new cell bit at `(i, p)`. -/
def preCell {τ b P : ℕ} (x : CIdx τ b P → Bool) (y : KIdx τ b → Bool) (i : Fin τ) (p : Fin P) : Bool :=
  if y kA && y (kWr i) && x (hd i p) then y (kWv i) else x (cl i p)

/-- The configuration bits after the action (before the oracle answer). -/
def pre {τ b P : ℕ} (x : CIdx τ b P → Bool) (y : KIdx τ b → Bool) : CIdx τ b P → Bool :=
  Sum.elim (fun j => y (Sum.inl j)) (Sum.elim (fun ip => preHead x y ip.1 ip.2) (fun ip => preCell x y ip.1 ip.2))

/-- The oracle's answer bits read from the query tape cells `i·t + j` of `c1`. -/
def orc {τ b P m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) (hmt : m * t ≤ P) (qt : Fin τ)
    (c1 : CIdx τ b P → Bool) : Fin t → Bool :=
  f (fun i j => c1 (cl qt ⟨i.val * t + j.val, by
    have := i.isLt; have := j.isLt
    calc i.val * t + j.val < i.val * t + t := by omega
      _ = (i.val + 1) * t := by ring
      _ ≤ m * t := Nat.mul_le_mul_right _ (by omega)
      _ ≤ P := hmt⟩))

/-- The final bits: on a query, the answer tape holds the answer and its head is at `0`. -/
def fin {τ b P t : ℕ} (at3 : Fin τ) (c1 : CIdx τ b P → Bool) (ak : Bool) (o : Fin t → Bool) : CIdx τ b P → Bool :=
  Sum.elim (fun j => c1 (Sum.inl j)) (Sum.elim
    (fun ip => if ak && decide (ip.1 = at3) then decide (ip.2.val = 0) else c1 (Sum.inr (Sum.inl ip)))
    (fun ip => if ak && decide (ip.1 = at3) then (if h : ip.2.val < t then o ⟨ip.2.val, h⟩ else false)
      else c1 (Sum.inr (Sum.inr ip))))

/-- **The vector step.** -/
noncomputable def stepV {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) (b P : ℕ) (hmt : m * t ≤ P)
    (x : CIdx M.tapeCount b P → Bool) : CIdx M.tapeCount b P → Bool :=
  fin M.answerTape (pre x (ctlOut M b (fun j => x (Sum.inl j)) (scan x)))
    (ctlOut M b (fun j => x (Sum.inl j)) (scan x) kAsk)
    (orc f hmt M.queryTape (pre x (ctlOut M b (fun j => x (Sum.inl j)) (scan x))))

/-! ## The step commutes with the encoding -/

theorem pre_frozen {τ b P : ℕ} (x : CIdx τ b P → Bool) :
    pre x (Sum.elim (fun j => x (Sum.inl j)) (fun _ => false)) = x := by
  funext z
  rcases z with j | ⟨i, p⟩ | ⟨i, p⟩
  · rfl
  · simp [pre, preHead, kA, hd]
  · simp [pre, preCell, kA, cl]

theorem fin_false {τ b P t : ℕ} (at3 : Fin τ) (c1 : CIdx τ b P → Bool) (o : Fin t → Bool) :
    fin at3 c1 false o = c1 := by
  funext z
  rcases z with j | ⟨i, p⟩ | ⟨i, p⟩ <;> rfl

theorem ctlOut_none (b : ℕ) (v : Fin b → Bool) (sc : Fin M.tapeCount → Bool) (h : ctlAct M b v sc = none) :
    ctlOut M b v sc = Sum.elim v (fun _ => false) := by
  unfold ctlOut; rw [h]

theorem ctlOut_some (b : ℕ) (v : Fin b → Bool) (sc : Fin M.tapeCount → Bool) (a : Action M.tapeCount M.stateCount)
    (h : ctlAct M b v sc = some a) :
    ctlOut M b v sc = Sum.elim (code b a.nextControl) (Sum.elim
      (fun ik => ![(a.write ik.1).isSome, (a.write ik.1).getD false, decide (a.move ik.1 = HeadMove.left),
        decide (a.move ik.1 = HeadMove.right)] ik.2)
      (fun e => ![true, M.asks a.nextControl] e)) := by
  unfold ctlOut; rw [h]

theorem headBit (P h : ℕ) (hh : h < P) (mv : HeadMove) (p : Fin P) :
    ((decide (mv = HeadMove.left) &&
          ((if _h : p.val + 1 < P then decide (h = p.val + 1) else false) ||
            decide (p.val = 0) && decide (h = p.val)) ||
        decide (mv = HeadMove.right) && if _h : 1 ≤ p.val then decide (h = p.val - 1) else false) ||
      !decide (mv = HeadMove.left) && !decide (mv = HeadMove.right) && decide (h = p.val)) =
    decide (mv.apply h = p.val) := by
  have hp := p.isLt
  cases mv <;> simp only [HeadMove.apply] <;> split_ifs <;> rw [Bool.eq_iff_iff] <;> simp <;> omega

theorem pre_active (b P : ℕ) (c : Configuration M.tapeCount M.stateCount) (hP : ∀ i, c.heads i < P)
    (a : Action M.tapeCount M.stateCount) :
    pre (enc M b P c) (Sum.elim (code b a.nextControl) (Sum.elim
      (fun ik => ![(a.write ik.1).isSome, (a.write ik.1).getD false, decide (a.move ik.1 = HeadMove.left),
        decide (a.move ik.1 = HeadMove.right)] ik.2)
      (fun e => ![true, M.asks a.nextControl] e))) = enc M b P (applyAction c a) := by
  funext z
  rcases z with j | ⟨i, p⟩ | ⟨i, p⟩
  · rfl
  · simp only [pre, preHead, Sum.elim_inr, Sum.elim_inl, kA, kLf, kRt, enc, hd, applyAction]
    have hi := hP i
    have e0 : (![true, M.asks a.nextControl] : Fin 2 → Bool) 0 = true := rfl
    have e2 : (![(a.write i).isSome, (a.write i).getD false, decide (a.move i = HeadMove.left),
        decide (a.move i = HeadMove.right)] : Fin 4 → Bool) 2 = decide (a.move i = HeadMove.left) := rfl
    have e3 : (![(a.write i).isSome, (a.write i).getD false, decide (a.move i = HeadMove.left),
        decide (a.move i = HeadMove.right)] : Fin 4 → Bool) 3 = decide (a.move i = HeadMove.right) := rfl
    rw [e0, e2, e3, if_pos rfl]
    exact headBit P _ hi (a.move i) p
  · simp only [pre, preCell, Sum.elim_inr, Sum.elim_inl, kA, kWr, kWv, enc, hd, cl, applyAction]
    cases hw : a.write i with
    | none => simp
    | some v =>
        simp only [Option.isSome_some, Option.getD_some, NearCubicWires.Bindings.Sim.readTapeBit_writeTapeBit]
        by_cases hp : c.heads i = p.val
        · simp [hp]
        · simp [hp, Ne.symm hp]

theorem readTapeBit_ofFn {t : ℕ} (g : Fin t → Bool) (p : ℕ) :
    readTapeBit (List.ofFn g) p = if h : p < t then g ⟨p, h⟩ else false := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> simp

theorem fin_true_enc (b P : ℕ) {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) (hmt : m * t ≤ P)
    (c' : Configuration M.tapeCount M.stateCount) :
    fin M.answerTape (enc M b P c') true (orc f hmt M.queryTape (enc M b P c')) =
      enc M b P (Configuration.mk c'.control (Function.update c'.heads M.answerTape 0)
        (Function.update c'.tapes M.answerTape (fieldOracle f (c'.tapes M.queryTape)))) := by
  funext z
  rcases z with j | ⟨i, p⟩ | ⟨i, p⟩
  · rfl
  · by_cases hi : i = M.answerTape
    · subst hi; simp [fin, enc, eq_comm]
    · simp [fin, enc, hi]
  · by_cases hi : i = M.answerTape
    · subst hi
      simp only [fin, enc, Sum.elim_inr, decide_true, Bool.and_self, if_true, Function.update_self, fieldOracle,
        readTapeBit_ofFn]
      rfl
    · simp [fin, enc, hi]

theorem stepV_enc {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) (b P : ℕ) (hmt : m * t ≤ P)
    (hb : M.stateCount ≤ 2 ^ b) (c : Configuration M.tapeCount M.stateCount) (hP : ∀ i, c.heads i < P) :
    stepV M f b P hmt (enc M b P c) = enc M b P (tstep M (fieldOracle f) c) := by
  have hsc := scan_enc M b P c hP
  have hv : (fun j => enc M b P c (Sum.inl j)) = code b c.control := rfl
  unfold stepV
  rw [hv, hsc]
  by_cases hh : M.machine.halted c.control = true
  · have hact : ctlAct M b (code b c.control) c.scanned = none := by rw [ctlAct_code M hb, if_pos hh]
    rw [ctlOut_none M b _ _ hact, ← hv, pre_frozen]
    have ht : tstep M (fieldOracle f) c = c := by simp [tstep, hh]
    rw [ht]
    exact fin_false _ _ _
  · cases hr : M.machine.rule c.control c.scanned with
    | none =>
        have hact : ctlAct M b (code b c.control) c.scanned = none := by rw [ctlAct_code M hb, if_neg hh, hr]
        rw [ctlOut_none M b _ _ hact, ← hv, pre_frozen]
        have ht : tstep M (fieldOracle f) c = c := by
          simp [tstep, hh, OracleMachine.oracleStep, step, hr]
        rw [ht]
        exact fin_false _ _ _
    | some a =>
        have hact : ctlAct M b (code b c.control) c.scanned = some a := by rw [ctlAct_code M hb, if_neg hh, hr]
        rw [ctlOut_some M b _ _ a hact, pre_active M b P c hP a]
        have ht : tstep M (fieldOracle f) c = if M.asks a.nextControl then
            Configuration.mk (applyAction c a).control (Function.update (applyAction c a).heads M.answerTape 0)
              (Function.update (applyAction c a).tapes M.answerTape
                (fieldOracle f ((applyAction c a).tapes M.queryTape)))
            else applyAction c a := by
          simp only [tstep, hh, Bool.false_eq_true, if_false, OracleMachine.oracleStep, step, hr, Option.map_some,
            Option.getD_some]
          rfl
        rw [ht]
        have hk : (Sum.elim (code b a.nextControl) (Sum.elim
            (fun ik : Fin M.tapeCount × Fin 4 => ![(a.write ik.1).isSome, (a.write ik.1).getD false,
              decide (a.move ik.1 = HeadMove.left), decide (a.move ik.1 = HeadMove.right)] ik.2)
            (fun e => ![true, M.asks a.nextControl] e)) : KIdx M.tapeCount b → Bool) kAsk = M.asks a.nextControl :=
          rfl
        rw [hk]
        by_cases hq : M.asks a.nextControl = true
        · rw [if_pos hq, hq]
          exact fin_true_enc M b P f hmt (applyAction c a)
        · rw [if_neg hq, Bool.eq_false_iff.mpr hq]
          exact fin_false _ _ _

/-! ## Nets for the step -/

theorem card_CIdx (τ b P : ℕ) : Fintype.card (CIdx τ b P) = b + (τ * P + τ * P) := by simp

theorem card_KIdx (τ b : ℕ) : Fintype.card (KIdx τ b) = b + (τ * 4 + 2) := by simp

theorem real_scan (τ b P : ℕ) :
    Real (τ * (1 + P * (1 * ((2 + 1) + 8 * 2 ^ (2 + 1))))) (fun (x : CIdx τ b P → Bool) => scan x) := by
  have h := Real.pi (β := Fin τ) (s := 1 + P * (1 * ((2 + 1) + 8 * 2 ^ (2 + 1))))
    (fun (x : CIdx τ b P → Bool) i => scan x i) (fun i => by
      have := Real.any (α := CIdx τ b P) 2 (List.finRange P) (fun p => ![hd i p, cl i p]) (fun _ v => v 0 && v 1)
      rw [List.length_finRange] at this
      exact this.congr fun x _ => rfl)
  rwa [Fintype.card_fin] at h

theorem real_ctl (b : ℕ) (P : ℕ) :
    Real ((b + (M.tapeCount * 4 + 2)) * ((b + M.tapeCount) + 8 * 2 ^ (b + M.tapeCount)))
      (fun (z : CIdx M.tapeCount b P ⊕ Fin M.tapeCount → Bool) =>
        ctlOut M b (fun j => z (Sum.inl (Sum.inl j))) (fun i => z (Sum.inr i))) := by
  have h := Real.local (α := CIdx M.tapeCount b P ⊕ Fin M.tapeCount) (β := KIdx M.tapeCount b) (b + M.tapeCount)
    (fun _ k => Sum.elim (fun j => Sum.inl (Sum.inl j)) Sum.inr (finSumFinEquiv.symm k))
    (fun o v => ctlOut M b (fun j => v (Fin.castAdd M.tapeCount j)) (fun i => v (Fin.natAdd b i)) o)
  rw [card_KIdx] at h
  exact h.congr fun z o => by simp

/-- The leaves read by the update of each position (padded to nine). -/
def preLeaves {τ b P : ℕ} : CIdx τ b P ⊕ Unit → Fin 9 → CIdx τ b P ⊕ KIdx τ b
  | Sum.inl (Sum.inl j) => fun _ => Sum.inr (Sum.inl j)
  | Sum.inl (Sum.inr (Sum.inl (i, p))) =>
      ![Sum.inl (hd i (if h : p.val + 1 < P then ⟨p.val + 1, h⟩ else p)), Sum.inl (hd i p),
        Sum.inl (hd i (if h : 1 ≤ p.val then ⟨p.val - 1, by omega⟩ else p)), Sum.inr kA, Sum.inr (kLf i),
        Sum.inr (kRt i), Sum.inr kA, Sum.inr kA, Sum.inr kA]
  | Sum.inl (Sum.inr (Sum.inr (i, p))) =>
      ![Sum.inl (hd i p), Sum.inl (cl i p), Sum.inr kA, Sum.inr (kWr i), Sum.inr (kWv i), Sum.inr kA, Sum.inr kA,
        Sum.inr kA, Sum.inr kA]
  | Sum.inr _ => fun _ => Sum.inr kAsk

/-- The update function of each position on its nine leaves. -/
def preFun {τ b P : ℕ} : CIdx τ b P ⊕ Unit → (Fin 9 → Bool) → Bool
  | Sum.inl (Sum.inl _) => fun v => v 0
  | Sum.inl (Sum.inr (Sum.inl (_, p))) => fun v =>
      if v 3 then
        (v 4 && ((if p.val + 1 < P then v 0 else false) || (decide (p.val = 0) && v 1))) ||
          (v 5 && (if 1 ≤ p.val then v 2 else false)) || (!v 4 && !v 5 && v 1)
      else v 1
  | Sum.inl (Sum.inr (Sum.inr _)) => fun v => if v 2 && v 3 && v 0 then v 4 else v 1
  | Sum.inr _ => fun v => v 0

theorem real_pre (τ b P : ℕ) :
    Real ((b + (τ * P + τ * P) + 1) * (9 + 8 * 2 ^ 9))
      (fun (w : CIdx τ b P ⊕ KIdx τ b → Bool) =>
        Sum.elim (pre (fun z => w (Sum.inl z)) (fun k => w (Sum.inr k))) (fun (_ : Unit) => w (Sum.inr kAsk))) := by
  have h := Real.local (α := CIdx τ b P ⊕ KIdx τ b) (β := CIdx τ b P ⊕ Unit) 9 preLeaves preFun
  rw [Fintype.card_sum, card_CIdx, Fintype.card_unit] at h
  refine h.congr fun w o => ?_
  rcases o with (j | ⟨i, p⟩ | ⟨i, p⟩) | u
  · rfl
  · simp only [preFun, preLeaves, pre, preHead, Sum.elim_inl, Sum.elim_inr]
    by_cases h1 : p.val + 1 < P <;> by_cases h2 : 1 ≤ p.val <;> simp [h1, h2]
  · rfl
  · rfl

/-- The final positions on three leaves: the bit after the action, the query flag, the oracle bit. -/
def finLeaves {τ b P t : ℕ} : CIdx τ b P → Fin 3 → (CIdx τ b P ⊕ Unit) ⊕ Fin t
  | z@(Sum.inr (Sum.inr (_, p))) =>
      ![Sum.inl (Sum.inl z), Sum.inl (Sum.inr ()), if h : p.val < t then Sum.inr ⟨p.val, h⟩ else Sum.inl (Sum.inr ())]
  | z => ![Sum.inl (Sum.inl z), Sum.inl (Sum.inr ()), Sum.inl (Sum.inr ())]

def finFun {τ b P t : ℕ} (at3 : Fin τ) : CIdx τ b P → (Fin 3 → Bool) → Bool
  | Sum.inl _ => fun v => v 0
  | Sum.inr (Sum.inl (i, p)) => fun v => if v 1 && decide (i = at3) then decide (p.val = 0) else v 0
  | Sum.inr (Sum.inr (i, p)) => fun v => if v 1 && decide (i = at3) then (if p.val < t then v 2 else false) else v 0

theorem real_fin (τ b P t : ℕ) (at3 : Fin τ) :
    Real ((b + (τ * P + τ * P)) * (3 + 8 * 2 ^ 3))
      (fun (w : (CIdx τ b P ⊕ Unit) ⊕ Fin t → Bool) =>
        fin at3 (fun z => w (Sum.inl (Sum.inl z))) (w (Sum.inl (Sum.inr ()))) (fun s => w (Sum.inr s))) := by
  have h := Real.local (α := (CIdx τ b P ⊕ Unit) ⊕ Fin t) (β := CIdx τ b P) 3 finLeaves (finFun (t := t) at3)
  rw [card_CIdx] at h
  refine h.congr fun w o => ?_
  rcases o with j | ⟨i, p⟩ | ⟨i, p⟩
  · rfl
  · rfl
  · simp only [finFun, finLeaves, fin, Sum.elim_inr]
    by_cases h1 : p.val < t <;> simp [h1]

/-- Size of one step. -/
def stepSize (τ b P sO : ℕ) : ℕ :=
  τ * (1 + P * (1 * ((2 + 1) + 8 * 2 ^ (2 + 1)))) + (b + (τ * 4 + 2)) * ((b + τ) + 8 * 2 ^ (b + τ)) +
    (b + (τ * P + τ * P) + 1) * (9 + 8 * 2 ^ 9) + (sO + (b + (τ * P + τ * P)) * (3 + 8 * 2 ^ 3))

/-- **One step as a net.** -/
theorem real_stepV {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) (sO : ℕ)
    (hO : Real sO (fun (z : Fin m × Fin t → Bool) => f (fun i j => z (i, j)))) (b P : ℕ) (hmt : m * t ≤ P) :
    Real (stepSize M.tapeCount b P sO) (stepV M f b P hmt) := by
  have h12 := Real.bind (real_scan M.tapeCount b P) (real_ctl M b P)
  have h123 := Real.bind h12 (real_pre M.tapeCount b P)
  have hO' := hO.mapIn (fun ij : Fin m × Fin t => (Sum.inl (cl M.queryTape ⟨ij.1.val * t + ij.2.val, by
    have := ij.1.isLt; have := ij.2.isLt
    calc ij.1.val * t + ij.2.val < ij.1.val * t + t := by omega
      _ = (ij.1.val + 1) * t := by ring
      _ ≤ m * t := Nat.mul_le_mul_right _ (by omega)
      _ ≤ P := hmt⟩) : CIdx M.tapeCount b P ⊕ Unit))
  have hF := Real.bind hO' (real_fin M.tapeCount b P t M.answerTape)
  refine ((Real.comp h123 hF).mono (by unfold stepSize; omega)).congr fun x z => ?_
  rfl

/-! ## The run from the initial configuration -/

theorem Real.leavesFT {α β : Type} [Fintype β] (w : β → Bool ⊕ α) :
    Real (Fintype.card β) (fun x b => Real.leafEval x (w b)) := by
  classical
  have h := Real.leaves (fun j : Fin (Fintype.card β) => w ((Fintype.equivFin β).symm j))
  exact (h.reindex (Fintype.equivFin β)).congr fun x b => by simp

/-- The leaves of the initial configuration: the input word (as leaves) on tape `0`, the coins on tape `1`. -/
def initLeaf (b P : ℕ) {α : Type} (inw : List (Bool ⊕ α)) (coins : List Bool) :
    CIdx M.tapeCount b P → Bool ⊕ α
  | Sum.inl j => Sum.inl (code b M.machine.start j)
  | Sum.inr (Sum.inl (_, p)) => Sum.inl (decide (0 = p.val))
  | Sum.inr (Sum.inr (i, p)) =>
      if i.val = 0 then inw.getD p.val (Sum.inl false)
      else Sum.inl (if i.val = 1 then readTapeBit coins p.val else false)

theorem enc_initial (b P : ℕ) {α : Type} (inw : List (Bool ⊕ α)) (coins : List Bool) (x : α → Bool) :
    enc M b P (M.initial (inw.map (Real.leafEval x)) coins) = fun z => Real.leafEval x (initLeaf M b P inw coins z) := by
  funext z
  rcases z with j | ⟨i, p⟩ | ⟨i, p⟩
  · rfl
  · rfl
  · simp only [enc, initLeaf, Sum.elim_inr, OracleMachine.initial]
    by_cases h0 : i.val = 0
    · rw [if_pos h0, if_pos h0]
      unfold readTapeBit
      rw [show (false : Bool) = Real.leafEval x (Sum.inl false) from rfl, List.getD_map]
      rfl
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : i.val = 1
      · rw [if_pos h1, if_pos h1]; rfl
      · rw [if_neg h1, if_neg h1]; simp [readTapeBit, Real.leafEval]

theorem stepV_iterate {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) (b P : ℕ) (hmt : m * t ≤ P)
    (hb : M.stateCount ≤ 2 ^ b) (c0 : Configuration M.tapeCount M.stateCount) (hc0 : ∀ i, c0.heads i = 0) :
    ∀ s, s ≤ P → (stepV M f b P hmt)^[s] (enc M b P c0) = enc M b P ((tstep M (fieldOracle f))^[s] c0)
  | 0, _ => rfl
  | s + 1, hs => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', stepV_iterate f b P hmt hb c0 hc0 s (by omega)]
      exact stepV_enc M f b P hmt hb _ (fun i => lt_of_le_of_lt (heads_iterate M _ c0 hc0 s i) (by omega))

/-- **The run as a net**: `T` steps from the initial configuration (input word given by leaves, coins fixed), then
the first output cell. -/
theorem real_run {m t : ℕ} (f : (Fin m → Fin t → Bool) → Fin t → Bool) (sO : ℕ)
    (hO : Real sO (fun (z : Fin m × Fin t → Bool) => f (fun i j => z (i, j)))) (b P T : ℕ)
    (hb : M.stateCount ≤ 2 ^ b) (hmt : m * t ≤ P) (hTP : T < P) {α : Type} (inw : List (Bool ⊕ α))
    (coins : List Bool) :
    Real (Fintype.card (CIdx M.tapeCount b P) + T * stepSize M.tapeCount b P sO)
      (fun x (_ : Unit) => readTapeBit
        (((tstep M (fieldOracle f))^[T] (M.initial (inw.map (Real.leafEval x)) coins)).tapes M.outputTape) 0) := by
  have h0 := Real.leavesFT (α := α) (initLeaf M b P inw coins)
  have hit := Real.iterate h0 (real_stepV M f sO hO b P hmt) T
  refine (hit.reindex (fun _ : Unit => cl M.outputTape ⟨0, by omega⟩)).congr fun x _ => ?_
  simp only [Function.comp_apply]
  rw [← enc_initial M b P inw coins x, stepV_iterate M f b P hmt hb _ (fun _ => rfl) T hTP.le]
  rfl

end NearCubicGates.Adapters.Amplification
