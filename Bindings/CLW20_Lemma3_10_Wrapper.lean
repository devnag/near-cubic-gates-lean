import Bindings.CLW20_Lemma3_10
import Proof.CaseAnalysis.FinalTapeLocality

/-!
# The reject-short-witness wrapper: CLW20 Lemma 3.10 as printed feeds the import

`Bindings.CLW20_Lemma3_10` proves `CLW20_Lemma3_10_onWitnessLengthT → ProjectionPCPSource`. There the
time hypothesis is needed only for witnesses `y ∈ {0,1}^{T(n)}`. The printed lemma (CLW20 PDF
p.18, "Let M be an algorithm running in time T = T(n) ≥ n on inputs of the form (x, y) where
|x| = n") asks for time `T(n)` on EVERY input `(x, y)`. This module closes that gap. A verifier
`M` that halts within `T(n)` steps on witnesses of length `T(n)` is wrapped as `guard M`, which:

* halts within `T(n)` steps on EVERY witness (`guard_runsInTime`), and
* accepts a witness of length `T(n)` exactly when `M` does (`guard_accepts_iff`).

So the printed lemma applied to `(guard M, T)` is the witness-length version for `(M, T)`
(`clw20_lemma3_10_to_onWitnessLengthT`). With the adapter of `Bindings.CLW20_Lemma3_10` this gives
`clw20_lemma3_10_to_import : CLW20_Lemma3_10 → ProjectionPCPSource`.

## The wrapper

`guard M` runs `M` step for step, with one extra tape and one extra bit of control.

* The extra tape is the MIRROR. Its head moves exactly as the witness head does, and every step
  writes `true` under it. So a scanned mirror cell reads `false` exactly when the witness cell
  under the head is being visited for the first time. On a first visit the witness cell still
  holds its original content, even though `M` may write on its witness tape.
* Heads move by at most one cell, so first visits happen in increasing order. The index of a
  first-visited cell is the number of first visits so far. One control bit (the frontier
  parity) tracks whether it is even.
* The witness is framed (`frame y = true, y₁, true, y₂, …, false`), so the end of the witness is
  the first even cell holding `false`. When the guard scans that cell on a first visit, it
  REPLACES `M`'s step by a step into a halted, rejecting state.

Why the time bound stays exactly `T(n)`: pad a short witness `y` to `y' = y ++ 0…0` of length
`T(n)`. The two frames agree below cell `2|y|`. Until the head first reaches cell `2|y|`, the
guard on `y` does what `M` does on `y'` (`guard_run`). When the guard rejects at step `s`, `M` on
`y'` is not yet halted at step `s`, so `s + 1 ≤ T(n)`. On a witness of length exactly `T(n)`, a
run of `T(n)` steps never reaches cell `2T(n)`, so the guard never rejects there, and it accepts
exactly when `M` does. A witness longer than `T(n)` agrees with its first `T(n)` bits on every
cell a `T(n)`-step run can see (locality: `CloseoutFinalC10TapeLocality.runFrom_agree`).

This is the Tier 1 machine model (`Proof/Foundations/OrdinaryMachine.lean`, `Proof/Foundations/LocalBitMultitapeCore.lean`).
-/

namespace NearCubicWires.Bindings.CLW20Lemma310Guard

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicWires.LocalBitMultitape NearCubicWires.Bindings.CLW20Lemma310

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-! ## Stage 1: the machine -/

section Machine

variable {t s : ℕ}

/-- An original tape of `M`, inside the guard's tape bank. -/
def lift (i : Fin t) : Fin (t + 1) := Fin.castAdd 1 i

/-- The mirror tape: the last tape of the guard. -/
def mirror (t : ℕ) : Fin (t + 1) := Fin.natAdd t (0 : Fin 1)

@[simp] theorem lift_val (i : Fin t) : (lift i).val = i.val := rfl

@[simp] theorem mirror_val : (mirror t).val = t := rfl

/-- The guard's control: `M`'s state with the frontier parity (two copies of `M`'s states), and
one rejecting state. -/
def enc (q : Fin s) (b : Bool) : Fin (s + s + 1) :=
  Fin.castAdd 1 (if b then Fin.natAdd s q else Fin.castAdd s q)

/-- The halted, rejecting state. -/
def rejectState : Fin (s + s + 1) := Fin.natAdd (s + s) (0 : Fin 1)

/-- Read a guard state back as `M`'s state and the parity bit, or `none` for the reject state. -/
def decodeState (st : Fin (s + s + 1)) : Option (Fin s × Bool) :=
  Fin.addCases
    (fun st' : Fin (s + s) =>
      some (Fin.addCases (fun q : Fin s => (q, false)) (fun q : Fin s => (q, true)) st'))
    (fun _ => none) st

@[simp] theorem decode_enc (q : Fin s) (b : Bool) : decodeState (enc q b) = some (q, b) := by
  cases b <;>
    simp only [enc, decodeState, Fin.addCases_left, Fin.addCases_right, ↓reduceIte,
      Bool.false_eq_true]

@[simp] theorem decode_reject : decodeState (rejectState (s := s)) = none := by
  simp [decodeState, rejectState]

/-- `M`'s action, with the mirror tape written `true` and moved like the witness head. -/
def liftAction (w : Fin t) (b : Bool) (a : Action t s) : Action (t + 1) (s + s + 1) where
  nextControl := enc a.nextControl b
  write := Fin.addCases a.write (fun _ => some true)
  move := Fin.addCases a.move (fun _ => a.move w)

/-- The step into the rejecting state. -/
def rejectAction : Action (t + 1) (s + s + 1) where
  nextControl := rejectState
  write := fun _ => none
  move := fun _ => .stay

/-- One guard step from `M`'s state `q` and parity `b`. A first visit (`mirror` reads `false`)
at even parity to a witness cell holding `false` is the end of the witness: reject. Otherwise
take `M`'s step, and flip the parity on a first visit. -/
def guardRule (p : Machine t s) (w : Fin t) (q : Fin s) (b : Bool)
    (scanned : Fin (t + 1) → Bool) : Option (Action (t + 1) (s + s + 1)) :=
  if (!(scanned (mirror t))) = true ∧ b = false ∧ scanned (lift w) = false then
    some rejectAction
  else
    (p.rule q (fun i => scanned (lift i))).map (liftAction w (xor b (!(scanned (mirror t)))))

/-- The guard machine of `p`, with witness tape `w`. -/
def guardMachine (p : Machine t s) (w : Fin t) : Machine (t + 1) (s + s + 1) where
  descriptionBits := 0
  start := enc p.start false
  halted := fun st =>
    match decodeState st with
    | some (q, _) => p.halted q
    | none => true
  rule := fun st scanned =>
    match decodeState st with
    | some (q, b) => guardRule p w q b scanned
    | none => none

@[simp] theorem guard_halted_enc (p : Machine t s) (w : Fin t) (q : Fin s) (b : Bool) :
    (guardMachine p w).halted (enc q b) = p.halted q := by
  simp [guardMachine]

@[simp] theorem guard_halted_reject (p : Machine t s) (w : Fin t) :
    (guardMachine p w).halted rejectState = true := by
  simp [guardMachine]

end Machine

/-! ## Stage 2: one step -/

section Step

variable {t s : ℕ}

@[simp] theorem liftAction_write_lift (w : Fin t) (b : Bool) (a : Action t s) (i : Fin t) :
    (liftAction w b a).write (lift i) = a.write i := by
  simp [liftAction, lift]

@[simp] theorem liftAction_write_mirror (w : Fin t) (b : Bool) (a : Action t s) :
    (liftAction w b a).write (mirror t) = some true := by
  simp [liftAction, mirror]

@[simp] theorem liftAction_move_lift (w : Fin t) (b : Bool) (a : Action t s) (i : Fin t) :
    (liftAction w b a).move (lift i) = a.move i := by
  simp [liftAction, lift]

@[simp] theorem liftAction_move_mirror (w : Fin t) (b : Bool) (a : Action t s) :
    (liftAction w b a).move (mirror t) = a.move w := by
  simp [liftAction, mirror]

/-- The simulation relation between `M` on the padded witness (`c`) and the guard on the actual
witness (`c'`). The first `V` cells of the witness tape have been visited. Below `D` the two
witness tapes read alike. From cell `V` on, the guard's witness tape still holds its original
word `orig`. The mirror marks exactly the visited cells. -/
structure Rel (w : Fin t) (V D : ℕ) (orig : ℕ → Bool) (c : Configuration t s)
    (c' : Configuration (t + 1) (s + s + 1)) : Prop where
  control : c'.control = enc c.control (decide (V % 2 = 1))
  heads : ∀ i, c'.heads (lift i) = c.heads i
  mirrorHead : c'.heads (mirror t) = c.heads w
  tapes : ∀ i, i ≠ w → c'.tapes (lift i) = c.tapes i
  agree : ∀ j, j < D → readTapeBit (c'.tapes (lift w)) j = readTapeBit (c.tapes w) j
  fresh : ∀ j, V ≤ j → readTapeBit (c'.tapes (lift w)) j = orig j
  mirrorTape : ∀ j, readTapeBit (c'.tapes (mirror t)) j = decide (j < V)
  headLe : c.heads w ≤ V
  visitedLe : V ≤ D

open NearCubicWires.RepairOrdinary.CloseoutFinalC10TapeLocality (read_write apply_le)

theorem scanned_lift {w : Fin t} {V D : ℕ} {orig : ℕ → Bool} {c : Configuration t s}
    {c' : Configuration (t + 1) (s + s + 1)} (hR : Rel w V D orig c c') (hlt : c.heads w < D) :
    (fun i => c'.scanned (lift i)) = c.scanned := by
  funext i
  show readTapeBit (c'.tapes (lift i)) (c'.heads (lift i)) = readTapeBit (c.tapes i) (c.heads i)
  rw [hR.heads]
  by_cases hi : i = w
  · subst hi
    exact hR.agree _ hlt
  · rw [hR.tapes i hi]

theorem scanned_mirror {w : Fin t} {V D : ℕ} {orig : ℕ → Bool} {c : Configuration t s}
    {c' : Configuration (t + 1) (s + s + 1)} (hR : Rel w V D orig c c') :
    c'.scanned (mirror t) = decide (c.heads w < V) := by
  show readTapeBit (c'.tapes (mirror t)) (c'.heads (mirror t)) = _
  rw [hR.mirrorHead, hR.mirrorTape]

theorem scanned_wit_fresh {w : Fin t} {V D : ℕ} {orig : ℕ → Bool} {c : Configuration t s}
    {c' : Configuration (t + 1) (s + s + 1)} (hR : Rel w V D orig c c') (hV : c.heads w = V) :
    c'.scanned (lift w) = orig V := by
  show readTapeBit (c'.tapes (lift w)) (c'.heads (lift w)) = _
  rw [hR.heads, hV]
  exact hR.fresh V le_rfl

theorem guard_rule_eq (p : Machine t s) (w : Fin t) {V D : ℕ} {orig : ℕ → Bool}
    {c : Configuration t s} {c' : Configuration (t + 1) (s + s + 1)} (hR : Rel w V D orig c c') :
    (guardMachine p w).rule c'.control c'.scanned =
      guardRule p w c.control (decide (V % 2 = 1)) c'.scanned := by
  show (match decodeState c'.control with
    | some (q, b) => guardRule p w q b c'.scanned
    | none => none) = _
  rw [hR.control, decode_enc]

/-- **One step below the horizon `D`.** The guard takes `M`'s step (no reject: an even cell
below `D` of the original word is a frame marker, `true`), and the relation is kept with one more
visited cell when the head was on the frontier. -/
theorem step_lift (p : Machine t s) {w : Fin t} {V D : ℕ} {orig : ℕ → Bool}
    {c d : Configuration t s} {c' : Configuration (t + 1) (s + s + 1)}
    (hR : Rel w V D orig c c') (hlt : c.heads w < D)
    (hmarks : ∀ j, j < D → j % 2 = 0 → orig j = true)
    (hs : step p c = some d) :
    ∃ d', step (guardMachine p w) c' = some d' ∧
      Rel w (if c.heads w = V then V + 1 else V) D orig d d' := by
  cases hr : p.rule c.control c.scanned with
  | none => simp [step, hr] at hs
  | some a =>
    have hd : applyAction c a = d := by simpa [step, hr] using hs
    subst hd
    have hsc := scanned_lift hR hlt
    have hmir := scanned_mirror hR
    have hle := hR.headLe
    have hVD := hR.visitedLe
    have hno : ¬ ((!(c'.scanned (mirror t))) = true ∧ decide (V % 2 = 1) = false ∧
        c'.scanned (lift w) = false) := by
      rintro ⟨hf, hb, hc⟩
      rw [hmir] at hf
      have hV : c.heads w = V := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt] at hf
        omega
      rw [scanned_wit_fresh hR hV] at hc
      have hev : V % 2 = 0 := by
        simp only [decide_eq_false_iff_not] at hb
        omega
      rw [hmarks V (hV ▸ hlt) hev] at hc
      exact Bool.noConfusion hc
    have hrule : (guardMachine p w).rule c'.control c'.scanned =
        some (liftAction w (xor (decide (V % 2 = 1)) (!(c'.scanned (mirror t)))) a) := by
      rw [guard_rule_eq p w hR]
      unfold guardRule
      rw [if_neg hno, hsc, hr]
      rfl
    refine ⟨applyAction c'
      (liftAction w (xor (decide (V % 2 = 1)) (!(c'.scanned (mirror t)))) a), ?_, ?_⟩
    · simp only [step, hrule, Option.map_some]
    · have hV' : c.heads w < (if c.heads w = V then V + 1 else V) ∧
          V ≤ (if c.heads w = V then V + 1 else V) ∧
          (if c.heads w = V then V + 1 else V) ≤ D := by
        split_ifs <;> omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show enc a.nextControl _ = enc a.nextControl _
        congr 1
        rw [hmir]
        by_cases hhV : c.heads w = V
        · have hlt' : ¬ c.heads w < V := by omega
          by_cases hv : V % 2 = 1
          · have hv' : ¬ (V + 1) % 2 = 1 := by omega
            simp [hhV, hv, hv']
          · have hv' : (V + 1) % 2 = 1 := by omega
            simp [hhV, hv, hv']
        · have hlt' : c.heads w < V := by omega
          simp [hhV, hlt']
      · intro i
        show ((liftAction w _ a).move (lift i)).apply (c'.heads (lift i)) =
          (a.move i).apply (c.heads i)
        rw [liftAction_move_lift, hR.heads]
      · show ((liftAction w _ a).move (mirror t)).apply (c'.heads (mirror t)) =
          (a.move w).apply (c.heads w)
        rw [liftAction_move_mirror, hR.mirrorHead]
      · intro i hi
        simp only [applyAction, liftAction_write_lift]
        rw [hR.heads, hR.tapes i hi]
      · intro j hj
        simp only [applyAction, liftAction_write_lift]
        rw [hR.heads]
        cases a.write w with
        | none => exact hR.agree j hj
        | some v =>
          simp only
          rw [read_write, read_write]
          split_ifs
          · rfl
          · exact hR.agree j hj
      · intro j hj
        simp only [applyAction, liftAction_write_lift]
        rw [hR.heads]
        cases a.write w with
        | none => exact hR.fresh j (by omega)
        | some v =>
          simp only
          rw [read_write, if_neg (by omega)]
          exact hR.fresh j (by omega)
      · intro j
        simp only [applyAction, liftAction_write_mirror]
        rw [read_write, hR.mirrorHead, hR.mirrorTape]
        by_cases hj : j = c.heads w
        · rw [if_pos hj]
          simp only [true_eq_decide_iff]
          omega
        · rw [if_neg hj]
          simp only [decide_eq_decide]
          split_ifs <;> omega
      · show (a.move w).apply (c.heads w) ≤ _
        have := apply_le (a.move w) (c.heads w)
        omega
      · exact hV'.2.2

/-- **The reject step.** On the frontier, at even parity, over an original `false`: the guard
steps into the halted rejecting state. -/
theorem step_reject (p : Machine t s) {w : Fin t} {V D : ℕ} {orig : ℕ → Bool}
    {c : Configuration t s} {c' : Configuration (t + 1) (s + s + 1)}
    (hR : Rel w V D orig c c') (hV : c.heads w = V) (hev : V % 2 = 0) (horig : orig V = false) :
    step (guardMachine p w) c' = some (applyAction c' rejectAction) := by
  have hmir := scanned_mirror hR
  have hyes : (!(c'.scanned (mirror t))) = true ∧ decide (V % 2 = 1) = false ∧
      c'.scanned (lift w) = false := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmir, hV]
      simp
    · simp only [decide_eq_false_iff_not]
      omega
    · rw [scanned_wit_fresh hR hV, horig]
  have hrule : (guardMachine p w).rule c'.control c'.scanned = some rejectAction := by
    rw [guard_rule_eq p w hR]
    unfold guardRule
    rw [if_pos hyes]
  simp only [step, hrule, Option.map_some]

end Step

/-! ## Stage 3: whole runs -/

section Run

variable {t s : ℕ}

open NearCubicWires.RepairOrdinary.CloseoutFinalC10TapeLocality
  (runFrom_of_halted runFrom_succ_inv apply_le)

theorem halted_of_runFrom_zero (p : Machine t s) (c : Configuration t s)
    (r : ExecutionReceipt t s) (hr : runFrom p 0 c = some r) : p.halted c.control = true := by
  by_contra hne
  simp only [Bool.not_eq_true] at hne
  simp [runFrom, hne] at hr

theorem step_head_le (p : Machine t s) (w : Fin t) (c d : Configuration t s)
    (hs : step p c = some d) : d.heads w ≤ c.heads w + 1 := by
  cases hr : p.rule c.control c.scanned with
  | none => simp [step, hr] at hs
  | some a =>
    have hd : applyAction c a = d := by simpa [step, hr] using hs
    subst hd
    exact apply_le _ _

/-- A halted `M` configuration: the guard is halted too, in the lifted state. -/
theorem guard_run_halted (p : Machine t s) (w : Fin t) {V D : ℕ} {orig : ℕ → Bool} (f : ℕ)
    {c : Configuration t s} {c' : Configuration (t + 1) (s + s + 1)}
    (hR : Rel w V D orig c c') (hh : p.halted c.control = true) :
    ∃ r', runFrom (guardMachine p w) f c' = some r' ∧
      r'.final.control = enc c.control (decide (V % 2 = 1)) := by
  have hh' : (guardMachine p w).halted c'.control = true := by
    rw [hR.control, guard_halted_enc]
    exact hh
  exact ⟨_, runFrom_of_halted _ f c' hh', hR.control⟩

/-- **The guard's run.** Let `M` run from `c` for `f` steps on the padded witness. Let `D` be
the end of the guard's own witness: an even cell whose original content is `false`, with every
even cell below it `true`. Then the guard's run from a related configuration also halts within `f`
steps. It either ends in `M`'s final state (with some parity), or it rejects, and it can reject
only if a head starting at `c.heads w` could reach cell `D` within the run. -/
theorem guard_run (p : Machine t s) (w : Fin t) {D : ℕ} {orig : ℕ → Bool}
    (hmarks : ∀ j, j < D → j % 2 = 0 → orig j = true) (hD : D % 2 = 0)
    (horig : orig D = false) :
    ∀ (f V : ℕ) (c : Configuration t s) (c' : Configuration (t + 1) (s + s + 1))
      (r : ExecutionReceipt t s), Rel w V D orig c c' → runFrom p f c = some r →
      ∃ r', runFrom (guardMachine p w) f c' = some r' ∧
        ((∃ b, r'.final.control = enc r.final.control b) ∨
          (r'.final.control = rejectState ∧ D + 1 ≤ c.heads w + f)) := by
  intro f
  induction f with
  | zero =>
    intro V c c' r hR hr
    have hh := halted_of_runFrom_zero p c r hr
    have hrc : r.final = c := by
      rw [runFrom_of_halted p 0 c hh] at hr
      rw [← Option.some_inj.mp hr]
    obtain ⟨r', hr', hctl⟩ := guard_run_halted p w 0 hR hh
    exact ⟨r', hr', Or.inl ⟨_, by rw [hrc]; exact hctl⟩⟩
  | succ f ih =>
    intro V c c' r hR hr
    by_cases hh : p.halted c.control = true
    · have hrc : r.final = c := by
        rw [runFrom_of_halted p (f + 1) c hh] at hr
        rw [← Option.some_inj.mp hr]
      obtain ⟨r', hr', hctl⟩ := guard_run_halted p w (f + 1) hR hh
      exact ⟨r', hr', Or.inl ⟨_, by rw [hrc]; exact hctl⟩⟩
    · have hnh : p.halted c.control = false := by simpa using hh
      have hnh' : (guardMachine p w).halted c'.control = false := by
        rw [hR.control, guard_halted_enc]
        exact hnh
      obtain ⟨d, sfx, hd, hsfx, hfin⟩ := runFrom_succ_inv p f c r hnh hr
      by_cases hlt : c.heads w < D
      · obtain ⟨d', hd', hR'⟩ := step_lift p hR hlt hmarks hd
        obtain ⟨r'', hr'', hcase⟩ := ih _ d d' sfx hR' hsfx
        refine ⟨_, runFrom_step _ c' d' r'' hnh' hd' hr'', ?_⟩
        rcases hcase with ⟨b, hb⟩ | ⟨hrej, hbound⟩
        · exact Or.inl ⟨b, by rw [hfin]; exact hb⟩
        · refine Or.inr ⟨hrej, ?_⟩
          have := step_head_le p w c d hd
          omega
      · have hVD := hR.visitedLe
        have hle := hR.headLe
        have hV : c.heads w = V := by omega
        have hDV : V = D := by omega
        have hstep := step_reject p hR hV (by rw [hDV]; exact hD) (by rw [hDV]; exact horig)
        have hrej : (guardMachine p w).halted (applyAction c' rejectAction).control = true :=
          guard_halted_reject p w
        exact ⟨_, runFrom_step _ c' _ _ hnh' hstep (runFrom_of_halted _ f _ hrej),
          Or.inr ⟨rfl, by omega⟩⟩

end Run

/-- The witness tape of a verifier: tape `1`. -/
def wit (M : OrdinaryVerifier) : Fin M.tapeCount := ⟨1, by have := M.twoTapes; omega⟩

/-- **The guard of `M`.** It accepts in `M`'s accepting states, whatever the parity, and never
in the rejecting state. -/
def guard (M : OrdinaryVerifier) : OrdinaryVerifier where
  tapeCount := M.tapeCount + 1
  stateCount := M.stateCount + M.stateCount + 1
  twoTapes := by have := M.twoTapes; omega
  machine := guardMachine M.machine (wit M)
  accepting := fun st =>
    match decodeState st with
    | some (q, _) => M.accepting q
    | none => false

@[simp] theorem guard_accepting_enc (M : OrdinaryVerifier) (q : Fin M.stateCount) (b : Bool) :
    (guard M).accepting (enc q b) = M.accepting q := by
  simp [guard]

/-! ## Stage 4: the guard's two properties -/

section Frames

open NearCubicWires.RepairOrdinary.Streaming (marks marks_length frame_append read_append)

theorem read_prefix (l1 l2 : List Bool) (j : ℕ) (hj : j < l1.length) :
    readTapeBit (l1 ++ l2) j = readTapeBit l1 j := by
  simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem frame_eq_marks (y : List Bool) : RepairOrdinary.frame y = marks y ++ [false] := by
  have h := frame_append y []
  rw [List.append_nil] at h
  exact h

/-- Below `2|y|`, the frame of `y` is its marks: every even cell is a marker `true`. -/
theorem frame_even (y : List Bool) :
    ∀ j, j < 2 * y.length → j % 2 = 0 → readTapeBit (RepairOrdinary.frame y) j = true := by
  induction y with
  | nil => intro j hj; simp at hj
  | cons b y ih =>
    intro j hj he
    match j with
    | 0 => rfl
    | 1 => omega
    | j + 2 =>
      show readTapeBit (RepairOrdinary.frame y) j = true
      exact ih j (by simp at hj; omega) (by omega)

/-- Cell `2|y|` of the frame of `y` is its end marker `false`. -/
theorem frame_end (y : List Bool) : readTapeBit (RepairOrdinary.frame y) (2 * y.length) = false := by
  rw [frame_eq_marks]
  have h := read_append (marks y) [] false
  rw [marks_length] at h
  exact h

/-- `y` and any extension of it have frames that agree below `2|y|`. -/
theorem frame_agree (y z : List Bool) (j : ℕ) (hj : j < 2 * y.length) :
    readTapeBit (RepairOrdinary.frame y) j = readTapeBit (RepairOrdinary.frame (y ++ z)) j := by
  have hm : j < (marks y).length := by rw [marks_length]; exact hj
  rw [frame_eq_marks, frame_append, read_prefix _ _ _ hm, read_prefix _ _ _ hm]

end Frames

/-- The guard's start, related to `M`'s start on the padded witness `y ++ z`. -/
theorem init_rel (M : OrdinaryVerifier) (a y z : List Bool) :
    Rel (wit M) 0 (2 * y.length) (readTapeBit (RepairOrdinary.frame y))
      (initialConfiguration M.machine (M.inputTapes a (y ++ z)))
      (initialConfiguration (guard M).machine ((guard M).inputTapes a y)) := by
  have ht := M.twoTapes
  have hw : (lift (wit M)).val = 1 := rfl
  refine ⟨rfl, fun _ => rfl, rfl, ?_, ?_, ?_, ?_, le_rfl, Nat.zero_le _⟩
  · intro i hi
    have hi1 : i.val ≠ 1 := fun h => hi (Fin.ext h)
    show (guard M).inputTapes a y (lift i) = M.inputTapes a (y ++ z) i
    simp only [RepairOrdinary.Verifier.inputTapes, lift_val, hi1, if_false]
  · intro j hj
    show readTapeBit ((guard M).inputTapes a y (lift (wit M))) j =
      readTapeBit (M.inputTapes a (y ++ z) (wit M)) j
    have hw' : (wit M).val = 1 := rfl
    simp only [RepairOrdinary.Verifier.inputTapes, hw, hw', one_ne_zero, if_false, if_true]
    exact frame_agree y z j hj
  · intro j _
    show readTapeBit ((guard M).inputTapes a y (lift (wit M))) j = _
    simp only [RepairOrdinary.Verifier.inputTapes, hw, one_ne_zero, if_false, if_true]
  · intro j
    show readTapeBit ((guard M).inputTapes a y (mirror M.tapeCount)) j = _
    have h0 : M.tapeCount ≠ 0 := by omega
    have h1 : M.tapeCount ≠ 1 := by omega
    simp [RepairOrdinary.Verifier.inputTapes, h0, h1,
      NearCubicWires.RepairOrdinary.CloseoutFinalC10TapeLocality.read_nil]

/-- The guard on a witness `y`, against `M` on any extension `y ++ z` of it. -/
theorem guard_run_padded (M : OrdinaryVerifier) (f : ℕ) (a y z : List Bool)
    (r : ExecutionReceipt M.tapeCount M.stateCount)
    (hr : run M.machine f (M.inputTapes a (y ++ z)) = some r) :
    ∃ r', run (guard M).machine f ((guard M).inputTapes a y) = some r' ∧
      ((∃ b, r'.final.control = enc r.final.control b) ∨
        (r'.final.control = rejectState ∧ 2 * y.length + 1 ≤ f)) := by
  obtain ⟨r', hr', hcase⟩ := guard_run M.machine (wit M) (frame_even y) (by omega) (frame_end y)
    f 0 _ _ r (init_rel M a y z) hr
  refine ⟨r', hr', ?_⟩
  rcases hcase with hb | ⟨hrej, hbound⟩
  · exact Or.inl hb
  · have h0 : (initialConfiguration M.machine (M.inputTapes a (y ++ z))).heads (wit M) = 0 := rfl
    exact Or.inr ⟨hrej, by omega⟩

theorem run_unique {t s : ℕ} (m : Machine t s) {f1 f2 : ℕ} {i : Fin t → List Bool}
    {r1 r2 : ExecutionReceipt t s} (h1 : run m f1 i = some r1) (h2 : run m f2 i = some r2) :
    r1 = r2 := by
  have a := RepairOrdinary.run_moreFuel m f1 f2 i r1 h1
  have b := RepairOrdinary.run_moreFuel m f2 f1 i r2 h2
  rw [Nat.add_comm] at b
  exact Option.some.inj (a.symm.trans b)

theorem ofFn_getD (L : List Bool) (k : ℕ) (hk : L.length = k) :
    List.ofFn (fun i : Fin k => L.getD i false) = L := by
  subst hk
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD]

/-- A witness no longer than `T(n)`: the guard halts within `T(n)` steps. -/
theorem guard_halts_short (M : OrdinaryVerifier) (T : ℕ → ℕ) (h : RunsInTimeOnWitnessLengthT M T)
    (n : ℕ) (x : BitInput n) (y : List Bool) (hy : y.length ≤ T n) :
    ∃ r', run (guard M).machine (T n) ((guard M).inputTapes (List.ofFn x) y) = some r' := by
  have hL : (y ++ List.replicate (T n - y.length) false).length = T n := by simp; omega
  obtain ⟨r, hr⟩ := h n x (fun i => (y ++ List.replicate (T n - y.length) false).getD i false)
  rw [ofFn_getD _ _ hL] at hr
  obtain ⟨r', hr', _⟩ := guard_run_padded M (T n) (List.ofFn x) y _ r hr
  exact ⟨r', hr'⟩

open NearCubicWires.RepairOrdinary.CloseoutFinalC10TapeLocality (Agree runFrom_agree runFrom_of_halted)

/-- **The guard runs in time `T(n)` on EVERY witness** (the printed hypothesis). -/
theorem guard_runsInTime (M : OrdinaryVerifier) (T : ℕ → ℕ) (h : RunsInTimeOnWitnessLengthT M T) :
    RunsInTime (guard M) T := by
  intro n x y
  by_cases hy : y.length ≤ T n
  · exact guard_halts_short M T h n x y hy
  · have htake : (y.take (T n)).length = T n := by simp; omega
    obtain ⟨r1, hr1⟩ := guard_halts_short M T h n x (y.take (T n)) (by omega)
    by_cases hT0 : T n = 0
    · have hst := halted_of_runFrom_zero _ _ r1 (by rw [← hT0]; exact hr1)
      exact ⟨_, runFrom_of_halted _ (T n) _ hst⟩
    · have hag : Agree (2 * T n) ((guard M).inputTapes (List.ofFn x) (y.take (T n)))
          ((guard M).inputTapes (List.ofFn x) y) := by
        intro i j hj
        simp only [RepairOrdinary.Verifier.inputTapes]
        split_ifs
        · rfl
        · have := frame_agree (y.take (T n)) (y.drop (T n)) j (by omega)
          rwa [List.take_append_drop] at this
        · rfl
      obtain ⟨r2, hr2, _⟩ := runFrom_agree (guard M).machine (T n) (guard M).machine.start
        (fun _ => 0) _ _ hag (fun _ => by omega) r1 hr1
      exact ⟨r2, hr2⟩

/-- **On a witness of length `T(n)`, the guard accepts exactly when `M` does.** -/
theorem guard_accepts_iff (M : OrdinaryVerifier) (T : ℕ → ℕ) (h : RunsInTimeOnWitnessLengthT M T)
    (n : ℕ) (x : BitInput n) (y : BitInput (T n)) :
    (guard M).accepts (List.ofFn x) (List.ofFn y) ↔ M.accepts (List.ofFn x) (List.ofFn y) := by
  obtain ⟨r, hr⟩ := h n x y
  have hr0 : run M.machine (T n) (M.inputTapes (List.ofFn x) (List.ofFn y ++ [])) = some r := by
    simpa using hr
  obtain ⟨r', hr', hcase⟩ := guard_run_padded M (T n) (List.ofFn x) (List.ofFn y) [] r hr0
  obtain ⟨b, hb⟩ : ∃ b, r'.final.control = enc r.final.control b := by
    rcases hcase with hb | ⟨_, hbad⟩
    · exact hb
    · simp only [List.length_ofFn] at hbad
      omega
  constructor
  · rintro ⟨fuel, r2, hr2, hacc⟩
    have he : r2 = r' := run_unique _ hr2 hr'
    refine ⟨T n, r, hr, ?_⟩
    rw [he, hb, guard_accepting_enc] at hacc
    exact hacc
  · rintro ⟨fuel, r3, hr3, hacc⟩
    have he : r3 = r := run_unique _ hr3 hr
    refine ⟨T n, r', hr', ?_⟩
    rw [hb, guard_accepting_enc, ← he]
    exact hacc

/-! ## Stage 5: the printed lemma feeds the import -/

/-- **CLW20 Lemma 3.10 as printed (time `T` on every input `(x, y)`) implies the witness-length
version.** Apply the printed lemma to `(guard M, T)`. The algorithm, `t = poly(r)` and proof
length clauses do not mention the verifier. Completeness and soundness transfer because the
guard accepts a witness of length `T(n)` exactly when `M` does. -/
theorem clw20_lemma3_10_to_onWitnessLengthT :
    CLW20_Lemma3_10 → CLW20_Lemma3_10_onWitnessLengthT := by
  intro L M T hT h
  obtain ⟨out, halg, ht, hp, hc, hs⟩ := L (guard M) T hT (guard_runsInTime M T h)
  refine ⟨out, halg, ht, hp, ?_, ?_⟩
  · rintro x hx ⟨y, hy⟩
    exact hc x hx ⟨y, (guard_accepts_iff M T h x.1 x.2 y).mpr hy⟩
  · intro x hx hno π
    exact hs x hx (fun ⟨y, hy⟩ => hno ⟨y, (guard_accepts_iff M T h x.1 x.2 y).mp hy⟩) π

/-- **CLW20 Lemma 3.10 as printed gives the imported projection PCP source.** -/
theorem clw20_lemma3_10_to_import : CLW20_Lemma3_10 → ProjectionPCPSource :=
  fun L => clw20_lemma3_10_onWitnessLengthT_to_import (clw20_lemma3_10_to_onWitnessLengthT L)

/-- The two versions are equivalent. -/
theorem clw20_lemma3_10_iff_onWitnessLengthT :
    CLW20_Lemma3_10 ↔ CLW20_Lemma3_10_onWitnessLengthT :=
  ⟨clw20_lemma3_10_to_onWitnessLengthT, clw20_lemma3_10_onWitnessLengthT_to_literal⟩

end NearCubicWires.Bindings.CLW20Lemma310Guard
