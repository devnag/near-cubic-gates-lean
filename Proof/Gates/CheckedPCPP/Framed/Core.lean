import Proof.Foundations.OrdinaryMachine

/-! # Generic exact-step machinery for simulating stack machines on the repo's bit machine

Stage 1 of the bridge `Turing.TM2ComputableInTime → RepairSource.OrdinaryWordFunction`.

Everything here is about the repo's own model `LocalBitMultitape.Machine`
(`Proof/Foundations/LocalBitMultitapeCore.lean`) and does not mention Turing machines:

* `Runs M n c d`: `d` is reached from `c` in EXACTLY `n` executed steps, every intermediate
  control being non-halted; `Runs.runFrom` turns it into the repo's `runFrom` receipt.
* `Local M q i f`: at control `q` the machine reads only tape `i`, and the scanned bit `b`
  determines the next control, the (optional) write and the head move `f b` on tape `i` alone.
* `mk`: a machine from a finite control type (`Fintype.equivFin`, the repo's pattern) whose every
  rule is such a single-tape action; `mk_local` is its local behaviour.
* Three macros with exact step counts: writing a list to the right (`push_runs`), reading `B`
  bits to the left into an accumulator (`read_runs`), moving right `L` cells (`back_runs`).
* The stack-tape representation: `lay enc cs` (sentinel cell, then one block of `B` code bits
  plus a presence flag per stack cell, bottom first), and `Agrees T L` (the tape reads `L` on
  its first `L.length` cells; cells further right are unconstrained).
-/

namespace NearCubicGates.Close.FramedSim
open NearCubicWires
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Exact step counts -/

/-- `Runs M n c d`: starting from `c`, the machine executes exactly `n` steps and arrives at `d`;
no configuration before the last one is halted. -/
def Runs {t s : ℕ} (M : Machine t s) : ℕ → Configuration t s → Configuration t s → Prop
  | 0, c, d => c = d
  | n + 1, c, d => M.halted c.control = false ∧ ∃ c', step M c = some c' ∧ Runs M n c' d

theorem Runs.refl {t s : ℕ} (M : Machine t s) (c : Configuration t s) : Runs M 0 c c := rfl

theorem Runs.of_eq {t s : ℕ} {M : Machine t s} {n m : ℕ} {c d : Configuration t s}
    (h : Runs M n c d) (hnm : n = m) : Runs M m c d := hnm ▸ h

theorem Runs.single {t s : ℕ} {M : Machine t s} {c d : Configuration t s}
    (hh : M.halted c.control = false) (hs : step M c = some d) : Runs M 1 c d :=
  ⟨hh, d, hs, rfl⟩

theorem Runs.trans {t s : ℕ} {M : Machine t s} :
    ∀ {m n : ℕ} {c d e : Configuration t s}, Runs M m c d → Runs M n d e → Runs M (m + n) c e
  | 0, n, c, d, e, h1, h2 => by
      have hcd : c = d := h1
      subst hcd
      simpa using h2
  | m + 1, n, c, d, e, h1, h2 => by
      obtain ⟨hh, c', hs, hr⟩ := h1
      have := Runs.trans hr h2
      have hmn : m + 1 + n = (m + n) + 1 := by omega
      rw [hmn]
      exact ⟨hh, c', hs, this⟩

/-- An exact run that ends in a halted control is a `runFrom` receipt at any larger fuel. -/
theorem Runs.runFrom {t s : ℕ} {M : Machine t s} :
    ∀ {n : ℕ} {c d : Configuration t s}, Runs M n c d → M.halted d.control = true →
      ∀ extra, ∃ r, LocalBitMultitape.runFrom M (n + extra) c = some r ∧ r.final = d
  | 0, c, d, h, hd, extra => by
      have hcd : c = d := h
      subst hcd
      refine ⟨{ final := c, steps := 0, peakTapeCells := c.tapeCells }, ?_, rfl⟩
      cases extra with
      | zero => simp [LocalBitMultitape.runFrom, hd]
      | succ e => simp [LocalBitMultitape.runFrom, hd]
  | n + 1, c, d, h, hd, extra => by
      obtain ⟨hh, c', hs, hr⟩ := h
      obtain ⟨r, hr', hfin⟩ := Runs.runFrom hr hd extra
      have hmn : n + 1 + extra = (n + extra) + 1 := by omega
      rw [hmn]
      refine ⟨⟨r.final, r.steps + 1, max c.tapeCells r.peakTapeCells⟩, ?_, hfin⟩
      simp [LocalBitMultitape.runFrom, hh, hs, hr']

/-! ## Single-tape actions -/

/-- The configuration after acting on tape `i` only. -/
def act {t s : ℕ} (C : Configuration t s) (q : Fin s) (i : Fin t) (w : Option Bool)
    (m : HeadMove) : Configuration t s where
  control := q
  heads := Function.update C.heads i (m.apply (C.heads i))
  tapes := Function.update C.tapes i
    (match w with
     | none => C.tapes i
     | some b => writeTapeBit (C.tapes i) (C.heads i) b)

@[simp] theorem act_control {t s : ℕ} (C : Configuration t s) (q : Fin s) (i : Fin t)
    (w : Option Bool) (m : HeadMove) : (act C q i w m).control = q := rfl

@[simp] theorem act_heads_self {t s : ℕ} (C : Configuration t s) (q : Fin s) (i : Fin t)
    (w : Option Bool) (m : HeadMove) : (act C q i w m).heads i = m.apply (C.heads i) := by
  simp [act]

theorem act_heads_ne {t s : ℕ} (C : Configuration t s) (q : Fin s) (i j : Fin t)
    (w : Option Bool) (m : HeadMove) (h : j ≠ i) : (act C q i w m).heads j = C.heads j := by
  simp [act, Function.update_of_ne h]

theorem act_tapes_ne {t s : ℕ} (C : Configuration t s) (q : Fin s) (i j : Fin t)
    (w : Option Bool) (m : HeadMove) (h : j ≠ i) : (act C q i w m).tapes j = C.tapes j := by
  simp [act, Function.update_of_ne h]

@[simp] theorem act_tapes_none {t s : ℕ} (C : Configuration t s) (q : Fin s) (i : Fin t)
    (m : HeadMove) : (act C q i none m).tapes = C.tapes := by
  funext j
  by_cases h : j = i
  · subst h; simp [act]
  · exact act_tapes_ne C q i j none m h

@[simp] theorem act_tapes_some {t s : ℕ} (C : Configuration t s) (q : Fin s) (i : Fin t)
    (b : Bool) (m : HeadMove) :
    (act C q i (some b) m).tapes i = writeTapeBit (C.tapes i) (C.heads i) b := by
  simp [act]

/-- The repo action touching tape `i` only. -/
def singleAction {t s : ℕ} (q : Fin s) (i : Fin t) (w : Option Bool) (m : HeadMove) :
    Action t s where
  nextControl := q
  write := fun j => if j = i then w else none
  move := fun j => if j = i then m else .stay

theorem applyAction_single {t s : ℕ} (C : Configuration t s) (q : Fin s) (i : Fin t)
    (w : Option Bool) (m : HeadMove) : applyAction C (singleAction q i w m) = act C q i w m := by
  apply configuration_ext
  · rfl
  · funext j
    by_cases h : j = i
    · subst h; simp [applyAction, singleAction, act]
    · simp [applyAction, singleAction, act, h, HeadMove.apply]
  · funext j
    by_cases h : j = i
    · subst h
      cases w <;> simp [applyAction, singleAction, act]
    · simp [applyAction, singleAction, act, h]

/-- Local behaviour of a control state: it reads tape `i` only and acts on tape `i` only. -/
def Local {t s : ℕ} (M : Machine t s) (q : Fin s) (i : Fin t)
    (f : Bool → Fin s × Option Bool × HeadMove) : Prop :=
  M.halted q = false ∧ ∀ C : Configuration t s, C.control = q →
    step M C = some (act C (f (C.scanned i)).1 i (f (C.scanned i)).2.1 (f (C.scanned i)).2.2)

theorem Local.runs {t s : ℕ} {M : Machine t s} {q : Fin s} {i : Fin t}
    {f : Bool → Fin s × Option Bool × HeadMove} (h : Local M q i f) (C : Configuration t s)
    (hC : C.control = q) :
    Runs M 1 C (act C (f (C.scanned i)).1 i (f (C.scanned i)).2.1 (f (C.scanned i)).2.2) :=
  Runs.single (by rw [hC]; exact h.1) (h.2 C hC)

/-! ## A machine from a finite control type -/

section Mk
variable {t : ℕ} {Q : Type} [Fintype Q]

/-- The repo machine of a finite control type whose rule at each control reads one tape and acts
on that tape only. The control is numbered by `Fintype.equivFin` (the repo's pattern). -/
noncomputable def mk (start : Q) (halted : Q → Bool) (tapeOf : Q → Fin t)
    (g : Q → Bool → Q × Option Bool × HeadMove) : Machine t (Fintype.card Q) where
  descriptionBits := 0
  start := Fintype.equivFin Q start
  halted := fun x => halted ((Fintype.equivFin Q).symm x)
  rule := fun x bits =>
    some (singleAction (Fintype.equivFin Q (g ((Fintype.equivFin Q).symm x)
      (bits (tapeOf ((Fintype.equivFin Q).symm x)))).1) (tapeOf ((Fintype.equivFin Q).symm x))
      (g ((Fintype.equivFin Q).symm x) (bits (tapeOf ((Fintype.equivFin Q).symm x)))).2.1
      (g ((Fintype.equivFin Q).symm x) (bits (tapeOf ((Fintype.equivFin Q).symm x)))).2.2)

theorem mk_halted (start : Q) (halted : Q → Bool) (tapeOf : Q → Fin t)
    (g : Q → Bool → Q × Option Bool × HeadMove) (q : Q) :
    (mk start halted tapeOf g).halted (Fintype.equivFin Q q) = halted q := by
  simp [mk]

theorem mk_local (start : Q) (halted : Q → Bool) (tapeOf : Q → Fin t)
    (g : Q → Bool → Q × Option Bool × HeadMove) (q : Q) (hq : halted q = false) :
    Local (mk start halted tapeOf g) (Fintype.equivFin Q q) (tapeOf q)
      (fun b => (Fintype.equivFin Q (g q b).1, (g q b).2.1, (g q b).2.2)) := by
  refine ⟨by simp [mk, hq], ?_⟩
  intro C hC
  simp only [step, mk, hC, Equiv.symm_apply_apply, Option.map_some, applyAction_single]

end Mk

/-! ## Tape lemmas -/

theorem readTapeBit_writeTapeBit :
    ∀ (T : List Bool) (p q : ℕ) (b : Bool),
      readTapeBit (writeTapeBit T p b) q = if q = p then b else readTapeBit T q
  | [], 0, 0, b => by simp [writeTapeBit, readTapeBit]
  | [], 0, q + 1, b => by simp [writeTapeBit, readTapeBit]
  | [], p + 1, 0, b => by simp [writeTapeBit, readTapeBit]
  | [], p + 1, q + 1, b => by
      have := readTapeBit_writeTapeBit [] p q b
      simp only [readTapeBit] at this ⊢
      simpa [writeTapeBit] using this
  | x :: T, 0, 0, b => by simp [writeTapeBit, readTapeBit]
  | x :: T, 0, q + 1, b => by simp [writeTapeBit, readTapeBit]
  | x :: T, p + 1, 0, b => by simp [writeTapeBit, readTapeBit]
  | x :: T, p + 1, q + 1, b => by
      have := readTapeBit_writeTapeBit T p q b
      simp only [readTapeBit] at this ⊢
      simpa [writeTapeBit] using this

theorem writeTapeBit_length_eq_append :
    ∀ (L : List Bool) (b : Bool), writeTapeBit L L.length b = L ++ [b]
  | [], b => by simp [writeTapeBit]
  | x :: L, b => by
      simp [writeTapeBit, writeTapeBit_length_eq_append L b]

theorem HeadMove.apply_right (h : ℕ) : HeadMove.right.apply h = h + 1 := rfl
theorem HeadMove.apply_left (h : ℕ) : HeadMove.left.apply h = h - 1 := rfl
theorem HeadMove.apply_stay (h : ℕ) : HeadMove.stay.apply h = h := rfl

/-! ## Macro 1: write a list rightwards -/

section Macros
variable {t s : ℕ} {M : Machine t s} (i : Fin t)

theorem push_mid (X : List Bool) (P : ℕ → Fin s)
    (hmid : ∀ j, j + 1 < X.length →
      Local M (P (j + 1)) i (fun _ => (P (j + 2), some (X.getD j false), .right))) :
    ∀ m, m + 1 ≤ X.length → ∀ C : Configuration t s, C.control = P 1 →
      ∃ C', Runs M m C C' ∧ C'.control = P (m + 1) ∧ C'.heads i = C.heads i + m ∧
        (∀ q, readTapeBit (C'.tapes i) q =
          if C.heads i ≤ q ∧ q < C.heads i + m then X.getD (q - C.heads i) false
          else readTapeBit (C.tapes i) q) ∧
        (∀ j, j ≠ i → C'.heads j = C.heads j ∧ C'.tapes j = C.tapes j)
  | 0, _, C, hC => ⟨C, Runs.refl M C, hC, by simp, by intro q; simp, by simp⟩
  | m + 1, hm, C, hC => by
      obtain ⟨C', hr, hc, hh, hread, hoth⟩ := push_mid X P hmid m (by omega) C hC
      have hl := hmid m (by omega)
      refine ⟨_, Runs.trans hr (hl.runs C' hc), rfl, ?_, ?_, ?_⟩
      · simp [HeadMove.apply_right, hh]; omega
      · intro q
        simp only [act_tapes_some, readTapeBit_writeTapeBit, hread, hh]
        by_cases hq : q = C.heads i + m
        · subst hq; simp
        · simp only [hq, if_false]
          split_ifs <;> first | rfl | omega
      · intro j hj
        obtain ⟨h1, h2⟩ := hoth j hj
        exact ⟨by rw [act_heads_ne _ _ _ _ _ _ hj, h1], by rw [act_tapes_ne _ _ _ _ _ _ hj, h2]⟩

/-- Writing a nonempty list `X` to the cells right of the head: one move, then one write per
cell; exactly `X.length + 1` steps. The head ends on the last written cell. -/
theorem push_runs (X : List Bool) (hX : 0 < X.length) (P : ℕ → Fin s) (after : Fin s)
    (h0 : Local M (P 0) i (fun _ => (P 1, none, .right)))
    (hmid : ∀ j, j + 1 < X.length →
      Local M (P (j + 1)) i (fun _ => (P (j + 2), some (X.getD j false), .right)))
    (hlast : Local M (P X.length) i (fun _ => (after, some (X.getD (X.length - 1) false), .stay)))
    (C : Configuration t s) (hC : C.control = P 0) :
    ∃ C', Runs M (X.length + 1) C C' ∧ C'.control = after ∧ C'.heads i = C.heads i + X.length ∧
      (∀ q, readTapeBit (C'.tapes i) q =
        if C.heads i < q ∧ q ≤ C.heads i + X.length then X.getD (q - C.heads i - 1) false
        else readTapeBit (C.tapes i) q) ∧
      (∀ j, j ≠ i → C'.heads j = C.heads j ∧ C'.tapes j = C.tapes j) := by
  have r0 := h0.runs C hC
  set C1 := act C (P 1) i none HeadMove.right with hC1
  obtain ⟨C2, hr2, hc2, hh2, hread2, hoth2⟩ :=
    push_mid i X P hmid (X.length - 1) (by omega) C1 rfl
  have hl := hlast.runs C2 (by rw [hc2]; congr 1; omega)
  have hlen : 1 + (X.length - 1) + 1 = X.length + 1 := by omega
  refine ⟨_, (Runs.trans (Runs.trans r0 hr2) hl).of_eq hlen, rfl, ?_, ?_, ?_⟩
  · simp [HeadMove.apply_stay, hh2, hC1, HeadMove.apply_right]; omega
  · intro q
    have hC1h : C1.heads i = C.heads i + 1 := by simp [hC1, HeadMove.apply_right]
    have hC1t : C1.tapes = C.tapes := by simp [hC1]
    simp only [act_tapes_some, readTapeBit_writeTapeBit, hread2, hh2, hC1h, hC1t]
    by_cases hq : q = C.heads i + 1 + (X.length - 1)
    · subst hq
      simp only [if_true]
      rw [if_pos (by omega)]
      congr 1; omega
    · simp only [hq, if_false]
      split_ifs <;> first | omega | congr 1
  · intro j hj
    obtain ⟨h1, h2⟩ := hoth2 j hj
    refine ⟨?_, ?_⟩
    · rw [act_heads_ne _ _ _ _ _ _ hj, h1, hC1, act_heads_ne _ _ _ _ _ _ hj]
    · rw [act_tapes_ne _ _ _ _ _ _ hj, h2, hC1, act_tapes_ne _ _ _ _ _ _ hj]

/-! ## Macro 2: read `B` bits leftwards -/

/-- Set bit number `k` of an accumulator (no-op when `k ≥ B`). -/
def setBit {B : ℕ} (acc : Fin B → Bool) (k : ℕ) (b : Bool) : Fin B → Bool :=
  fun r => if r.val = k then b else acc r

/-- Accumulator after reading the top `m` code bits of a block whose code bit `r` sits at
`base + 1 + r`. -/
def accOf (B : ℕ) (T : List Bool) (base m : ℕ) : Fin B → Bool :=
  fun r => if B ≤ r.val + m then readTapeBit T (base + 1 + r.val) else false

theorem read_mid (B : ℕ) (G : ℕ → (Fin B → Bool) → Fin s) (fin : (Fin B → Bool) → Fin s)
    (hG : ∀ j acc, j < B → Local M (G j acc) i (fun b =>
      (if j + 1 < B then G (j + 1) (setBit acc (B - 1 - j) b) else fin (setBit acc (B - 1 - j) b),
        none, .left)))
    (base : ℕ) (C : Configuration t s) (hC : C.control = G 0 (fun _ => false))
    (hh : C.heads i = base + B) :
    ∀ m, m < B → ∃ C', Runs M m C C' ∧ C'.control = G m (accOf B (C.tapes i) base m) ∧
      C'.heads i = base + B - m ∧ C'.tapes = C.tapes ∧ (∀ j, j ≠ i → C'.heads j = C.heads j)
  | 0, _ => by
      refine ⟨C, Runs.refl M C, ?_, by omega, rfl, fun _ _ => rfl⟩
      rw [hC]; congr 1; funext r; simp [accOf]
  | m + 1, hm => by
      obtain ⟨C', hr, hc, hh', ht, hoth⟩ := read_mid B G fin hG base C hC hh m (by omega)
      have hl := (hG m _ (by omega)).runs C' hc
      refine ⟨_, Runs.trans hr hl, ?_, ?_, ?_, ?_⟩
      · simp only [act_control, if_pos (show m + 1 < B by omega)]
        congr 1
        funext r
        simp only [setBit, accOf, Configuration.scanned, hh', ht]
        by_cases hr' : r.val = B - 1 - m
        · rw [if_pos hr', if_pos (by omega)]; congr 1; omega
        · rw [if_neg hr']
          by_cases hb : B ≤ r.val + m
          · rw [if_pos hb, if_pos (by omega)]
          · rw [if_neg hb, if_neg (by omega)]
      · simp [HeadMove.apply_left, hh']; omega
      · simp [ht]
      · intro j hj
        rw [act_heads_ne _ _ _ _ _ _ hj, hoth j hj]

/-- Reading the `B` code bits of the block below the head, leftwards: exactly `B` steps; the head
ends on `base`, the accumulator is the block's code, and no tape changes. -/
theorem read_runs (B : ℕ) (hB : 0 < B) (G : ℕ → (Fin B → Bool) → Fin s)
    (fin : (Fin B → Bool) → Fin s)
    (hG : ∀ j acc, j < B → Local M (G j acc) i (fun b =>
      (if j + 1 < B then G (j + 1) (setBit acc (B - 1 - j) b) else fin (setBit acc (B - 1 - j) b),
        none, .left)))
    (base : ℕ) (C : Configuration t s) (hC : C.control = G 0 (fun _ => false))
    (hh : C.heads i = base + B) :
    ∃ C', Runs M B C C' ∧ C'.control = fin (fun r => readTapeBit (C.tapes i) (base + 1 + r.val)) ∧
      C'.heads i = base ∧ C'.tapes = C.tapes ∧ (∀ j, j ≠ i → C'.heads j = C.heads j) := by
  obtain ⟨C', hr, hc, hh', ht, hoth⟩ := read_mid i B G fin hG base C hC hh (B - 1) (by omega)
  have hl := (hG (B - 1) _ (by omega)).runs C' hc
  have hlen : B - 1 + 1 = B := by omega
  refine ⟨_, (Runs.trans hr hl).of_eq hlen, ?_, ?_, ?_, ?_⟩
  · simp only [act_control, if_neg (show ¬ (B - 1 + 1 < B) by omega)]
    congr 1
    funext r
    simp only [setBit, accOf, Configuration.scanned, hh', ht]
    by_cases hr' : r.val = B - 1 - (B - 1)
    · rw [if_pos hr']; congr 1; omega
    · rw [if_neg hr', if_pos (by omega)]
  · simp [HeadMove.apply_left, hh']; omega
  · simp [ht]
  · intro j hj
    rw [act_heads_ne _ _ _ _ _ _ hj, hoth j hj]

/-! ## Macro 3: move right `L` cells -/

theorem back_mid (L : ℕ) (Bk : ℕ → Fin s) (after : Fin s)
    (hBk : ∀ j, j < L → Local M (Bk j) i (fun _ =>
      (if j + 1 < L then Bk (j + 1) else after, none, .right)))
    (C : Configuration t s) (hC : C.control = Bk 0) :
    ∀ m, m < L → ∃ C', Runs M m C C' ∧ C'.control = Bk m ∧ C'.heads i = C.heads i + m ∧
      C'.tapes = C.tapes ∧ (∀ j, j ≠ i → C'.heads j = C.heads j)
  | 0, _ => ⟨C, Runs.refl M C, hC, rfl, rfl, fun _ _ => rfl⟩
  | m + 1, hm => by
      obtain ⟨C', hr, hc, hh', ht, hoth⟩ := back_mid L Bk after hBk C hC m (by omega)
      have hl := (hBk m (by omega)).runs C' hc
      refine ⟨_, Runs.trans hr hl, ?_, ?_, ?_, ?_⟩
      · simp [if_pos (show m + 1 < L by omega)]
      · simp [HeadMove.apply_right, hh']; omega
      · simp [ht]
      · intro j hj
        rw [act_heads_ne _ _ _ _ _ _ hj, hoth j hj]

/-- Moving right `L > 0` cells without writing: exactly `L` steps. -/
theorem back_runs (L : ℕ) (hL : 0 < L) (Bk : ℕ → Fin s) (after : Fin s)
    (hBk : ∀ j, j < L → Local M (Bk j) i (fun _ =>
      (if j + 1 < L then Bk (j + 1) else after, none, .right)))
    (C : Configuration t s) (hC : C.control = Bk 0) :
    ∃ C', Runs M L C C' ∧ C'.control = after ∧ C'.heads i = C.heads i + L ∧
      C'.tapes = C.tapes ∧ (∀ j, j ≠ i → C'.heads j = C.heads j) := by
  obtain ⟨C', hr, hc, hh', ht, hoth⟩ := back_mid i L Bk after hBk C hC (L - 1) (by omega)
  have hl := (hBk (L - 1) (by omega)).runs C' hc
  have hlen : L - 1 + 1 = L := by omega
  refine ⟨_, (Runs.trans hr hl).of_eq hlen, ?_, ?_, ?_, ?_⟩
  · simp [if_neg (show ¬ (L - 1 + 1 < L) by omega)]
  · simp [HeadMove.apply_right, hh']; omega
  · simp [ht]
  · intro j hj
    rw [act_heads_ne _ _ _ _ _ _ hj, hoth j hj]

end Macros

/-! ## The stack-tape layout -/

section Layout
variable {Src : Type} {B : ℕ} (enc : Src → Fin B → Bool)

/-- One stack cell: its `B` code bits, then the presence flag `true`. -/
def blk (c : Src) : List Bool := List.ofFn (enc c) ++ [true]

/-- A stack (top first) on a tape: a `false` sentinel cell, then the blocks from the bottom up.
The head rests on the last cell (the top's flag, or the sentinel for the empty stack). -/
def lay : List Src → List Bool
  | [] => [false]
  | c :: cs => lay cs ++ blk enc c

@[simp] theorem blk_length (c : Src) : (blk enc c).length = B + 1 := by simp [blk]

@[simp] theorem lay_length (cs : List Src) : (lay enc cs).length = cs.length * (B + 1) + 1 := by
  induction cs with
  | nil => simp [lay]
  | cons c cs ih => simp [lay, ih]; ring

/-- The tape `T` reads `L` on the first `L.length` cells. -/
def Agrees (T L : List Bool) : Prop := ∀ p, p < L.length → readTapeBit T p = L.getD p false

theorem agrees_nil_lay : Agrees ([] : List Bool) (lay enc ([] : List Src)) := by
  intro p hp
  simp [lay] at hp
  subst hp
  simp [lay, readTapeBit]

theorem Agrees.of_append {T L L' : List Bool} (h : Agrees T (L ++ L')) : Agrees T L := by
  intro p hp
  rw [h p (by simp; omega), List.getD_append _ _ _ _ hp]

theorem Agrees.tail {T : List Bool} {c : Src} {cs : List Src} (h : Agrees T (lay enc (c :: cs))) :
    Agrees T (lay enc cs) := Agrees.of_append (L' := blk enc c) h

theorem Agrees.flag_nil {T : List Bool} (h : Agrees T (lay enc ([] : List Src))) :
    readTapeBit T 0 = false := by
  rw [h 0 (by simp [lay])]; simp [lay]

theorem Agrees.flag_cons {T : List Bool} {c : Src} {cs : List Src}
    (h : Agrees T (lay enc (c :: cs))) : readTapeBit T ((cs.length + 1) * (B + 1)) = true := by
  have hP : (cs.length + 1) * (B + 1) = (cs.length * (B + 1) + 1) + B := by ring
  have hlen : (cs.length + 1) * (B + 1) < (lay enc (c :: cs)).length := by
    rw [lay_length, List.length_cons]; omega
  rw [h _ hlen]
  simp only [lay]
  rw [List.getD_append_right _ _ _ _ (by rw [lay_length]; omega), lay_length, hP,
    Nat.add_sub_cancel_left, blk, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem Agrees.code {T : List Bool} {c : Src} {cs : List Src}
    (h : Agrees T (lay enc (c :: cs))) (r : Fin B) :
    readTapeBit T (cs.length * (B + 1) + 1 + r.val) = enc c r := by
  have hlen : cs.length * (B + 1) + 1 + r.val < (lay enc (c :: cs)).length := by
    simp; have := r.isLt; ring_nf; omega
  rw [h _ hlen]
  simp only [lay]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [lay_length, blk]
  rw [List.getD_append _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- The tape after writing a block for `c` right of a stack layout agrees with the pushed layout. -/
theorem Agrees.push {T T' : List Bool} {cs : List Src} (h : Agrees T (lay enc cs)) (c : Src)
    (hT' : ∀ q, readTapeBit T' q =
      if cs.length * (B + 1) < q ∧ q ≤ cs.length * (B + 1) + (blk enc c).length then
        (blk enc c).getD (q - cs.length * (B + 1) - 1) false
      else readTapeBit T q) :
    Agrees T' (lay enc (c :: cs)) := by
  intro p hp
  have hP : (cs.length + 1) * (B + 1) = cs.length * (B + 1) + (B + 1) := by ring
  rw [lay_length, List.length_cons, hP] at hp
  rw [hT' p, blk_length]
  simp only [lay]
  by_cases hlo : p < (lay enc cs).length
  · rw [lay_length] at hlo
    rw [List.getD_append _ _ _ _ (by rw [lay_length]; exact hlo), if_neg (by omega)]
    exact h p (by rw [lay_length]; exact hlo)
  · rw [lay_length] at hlo
    rw [List.getD_append_right _ _ _ _ (by rw [lay_length]; omega), lay_length, if_pos (by omega)]
    congr 1

end Layout

end NearCubicGates.Close.FramedSim
