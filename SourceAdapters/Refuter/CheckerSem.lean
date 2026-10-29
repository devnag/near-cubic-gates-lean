import SourceAdapters.Refuter.TraceCheck

/-!
# The checker's passes, semantically (input 7, F01 machine layer, part 1)

Paper anchor: `lem:multitape-refuter`, (the universal simulation `U` with
`c_P(t+1)` accepting time) and the tape reduction it composes with, SFM78 l.222–233 (BGW70):
"guess on its second tape an alternating sequence of displays and legal actions … This can be
checked independently for each tape in turn … Clearly M' runs for time proportional to the length
of the sequence it guesses."

The fixed checking machine (built in `CheckerPass`/`Checker`) reads the code of `M` and a guessed
sequence of displays; the actions are looked up in the code's transition table. It makes one pass
per simulated tape `i`: each pass recomputes the control chain (and checks its legality) and replays
tape `i` on a work tape against the protected cutoff `r`.

This module is the exact semantic mirror of one pass, `passStep`: it follows the machine even after
a check has failed (the flag `ok` is then `false` and stays `false`), so the machine proof is a
simulation of a total function. `passes_iff` is the bridge: all passes succeed iff the decoded trace
passes `TraceChecks` (`TraceCheck.lean`) with the requested verdict. `traceOfD_of_legal` makes the
decoded trace of the displays of any legal trace equal to that trace (completeness).
-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.LocalBitMultitape

set_option autoImplicit false

variable {t s : ℕ}

/-! ## Decoded actions -/

/-- Control `0` (a machine has at least its start control). -/
def zeroCtl (m : Machine t s) : Fin s := ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) m.start.isLt⟩

/-- The action the checker decodes from an all-zero (`none`) table entry: control `0`, no write,
every head left (`writeCode none = [0,0]`, `moveCode left = [0,0]`). -/
def noAction (m : Machine t s) : Action t s := ⟨zeroCtl m, fun _ => none, fun _ => .left⟩

/-- The action decoded from the table at control `q` and display `d`. -/
def decodedAction (m : Machine t s) (q : Fin s) (d : Fin t → Bool) : Action t s :=
  (m.rule q d).getD (noAction m)

theorem decodedAction_of_rule {m : Machine t s} {q : Fin s} {d : Fin t → Bool} {a : Action t s}
    (h : m.rule q d = some a) : decodedAction m q d = a := by
  simp [decodedAction, h]

/-- The trace of a list of guessed displays from control `q`, actions decoded from the table. -/
def traceOfD (m : Machine t s) : Fin s → List (Fin t → Bool) → List (ClaimedStep t s)
  | _, [] => []
  | q, d :: ds => ⟨d, decodedAction m q d⟩ :: traceOfD m (decodedAction m q d).nextControl ds

@[simp] theorem traceOfD_length (m : Machine t s) :
    ∀ (q : Fin s) (ds : List (Fin t → Bool)), (traceOfD m q ds).length = ds.length
  | _, [] => rfl
  | q, d :: ds => by simp [traceOfD, traceOfD_length m _ ds]

/-- **Completeness of decoding**: a legal trace is the decoded trace of its displays. -/
theorem traceOfD_of_legal (m : Machine t s) :
    ∀ (q : Fin s) (trace : List (ClaimedStep t s)), ControlLegal m q trace →
      traceOfD m q (trace.map (·.scanned)) = trace
  | _, [], _ => rfl
  | q, e :: rest, h => by
    obtain ⟨_, hrule, hrest⟩ := h
    have ha := decodedAction_of_rule hrule
    simp only [List.map_cons, traceOfD, ha]
    rw [traceOfD_of_legal m _ rest hrest]

/-! ## One pass -/

/-- The state of a pass: the flag, the recomputed control, the work tape and its head. -/
structure PassSt (s : ℕ) where
  ok : Bool
  q : Fin s
  tape : List Bool
  head : ℕ

/-- **One step of pass `i`** on the guessed display `d`: the flag records that the control is not
halted, the table entry is an action, the head is before the cutoff, and the scanned cell agrees
with the display; the decoded write and move of tape `i` are applied in every case. -/
def passStep (m : Machine t s) (r : ℕ) (i : Fin t) (st : PassSt s) (d : Fin t → Bool) : PassSt s where
  ok := st.ok && !m.halted st.q && (m.rule st.q d).isSome && decide (st.head < r) &&
    (readTapeBit st.tape st.head == d i)
  q := (decodedAction m st.q d).nextControl
  tape := replayWrite i ⟨d, decodedAction m st.q d⟩ st.tape st.head
  head := ((decodedAction m st.q d).move i).apply st.head

/-- The pass over a list of displays. -/
def passRun (m : Machine t s) (r : ℕ) (i : Fin t) (st : PassSt s) (ds : List (Fin t → Bool)) :
    PassSt s :=
  ds.foldl (passStep m r i) st

theorem passRun_ok_false (m : Machine t s) (r : ℕ) (i : Fin t) :
    ∀ (ds : List (Fin t → Bool)) (st : PassSt s), st.ok = false → (passRun m r i st ds).ok = false
  | [], _, h => h
  | d :: ds, st, h => by
    unfold passRun
    rw [List.foldl_cons]
    apply passRun_ok_false m r i ds
    simp [passStep, h]

/-- The control of a pass is the recomputed control of the decoded trace. -/
theorem passRun_q (m : Machine t s) (r : ℕ) (i : Fin t) :
    ∀ (ds : List (Fin t → Bool)) (st : PassSt s),
      (passRun m r i st ds).q = controlAfter st.q (traceOfD m st.q ds)
  | [], _ => rfl
  | d :: ds, st => by
    unfold passRun
    rw [List.foldl_cons]
    exact passRun_q m r i ds _

/-- **The pass bridge.** Starting with the flag set, on a work tape that agrees below the cutoff
with the replayed tape `base`, the pass ends with the flag set iff the decoded trace is control-legal
and tape `i` replays (SFM78 l.227–230 with the protected cutoff, proof of `lem:multitape-refuter`). -/
theorem passRun_ok_iff (m : Machine t s) (r : ℕ) (i : Fin t) :
    ∀ (ds : List (Fin t → Bool)) (q : Fin s) (tape base : List Bool) (h : ℕ), AgreeBelow r tape base →
      ((passRun m r i ⟨true, q, tape, h⟩ ds).ok = true ↔
        ControlLegal m q (traceOfD m q ds) ∧ TapeReplay r i base h (traceOfD m q ds))
  | [], _, _, _, _, _ => by
    simp only [passRun, List.foldl_nil, traceOfD]
    exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  | d :: ds, q, tape, base, h, hag => by
    unfold passRun
    rw [List.foldl_cons]
    simp only [traceOfD, ControlLegal, TapeReplay]
    by_cases hstep : (passStep m r i ⟨true, q, tape, h⟩ d).ok = true
    · have hs := hstep
      simp only [passStep, Bool.true_and, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_true_eq, beq_iff_eq, Option.isSome_iff_exists] at hs
      obtain ⟨⟨⟨hnh, a, ha⟩, hhr⟩, hrd⟩ := hs
      have hda := decodedAction_of_rule ha
      have hread : readTapeBit base h = d i := by rw [← hag h hhr, hrd]
      have hag' : AgreeBelow r (replayWrite i ⟨d, decodedAction m q d⟩ tape h)
          (replayWrite i ⟨d, decodedAction m q d⟩ base h) := by
        unfold replayWrite
        split
        · exact hag
        · exact hag.write _ _
      have ih := passRun_ok_iff m r i ds (decodedAction m q d).nextControl _ _
        (((decodedAction m q d).move i).apply h) hag'
      have e : passStep m r i ⟨true, q, tape, h⟩ d =
          ⟨true, (decodedAction m q d).nextControl, replayWrite i ⟨d, decodedAction m q d⟩ tape h,
            ((decodedAction m q d).move i).apply h⟩ := by
        simp only [passStep, PassSt.mk.injEq, and_true]
        exact hstep
      unfold passRun at ih
      rw [e, ih, hda]
      simp only [hda] at hag' ⊢
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hnh, ha, h1⟩, hhr, hread, h2⟩
      · rintro ⟨⟨_, _, h1⟩, _, _, h2⟩
        exact ⟨h1, h2⟩
    · have hf : (passStep m r i ⟨true, q, tape, h⟩ d).ok = false := by simpa using hstep
      have := passRun_ok_false m r i ds _ hf
      unfold passRun at this
      rw [this]
      constructor
      · intro hc; exact absurd hc (by simp)
      rintro ⟨⟨hnh, hrule, _⟩, hhr, hrd, _⟩
      exfalso
      apply hstep
      simp only [passStep, Bool.true_and, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_true_eq, beq_iff_eq, Option.isSome_iff_exists]
      exact ⟨⟨⟨hnh, _, hrule⟩, hhr⟩, by rw [hag h hhr, hrd]⟩

/-- A pass's verdict: the flag, a halted final control, and the requested acceptance bit. -/
def passOk (v : RepairOrdinary.Verifier) (r : ℕ) (i : Fin v.tapeCount) (tape : List Bool)
    (ds : List (Fin v.tapeCount → Bool)) (verdict : Bool) : Bool :=
  let st := passRun v.machine r i ⟨true, v.machine.start, tape, 0⟩ ds
  st.ok && v.machine.halted st.q && (v.accepting st.q == verdict)

/-- **All passes ⟺ the trace checks with the verdict.** If each pass `i` starts on a work tape that
agrees below the cutoff with the copied prefix of tape `i`, then all passes succeed iff the decoded
trace passes `TraceChecks` and its recomputed final control has acceptance bit `verdict`. -/
theorem passes_iff (v : RepairOrdinary.Verifier) (r : ℕ) (tapes work : Fin v.tapeCount → List Bool)
    (hwork : ∀ i, AgreeBelow r (work i) (prefixTape r (tapes i)))
    (ds : List (Fin v.tapeCount → Bool)) (verdict : Bool) :
    (∀ i, passOk v r i (work i) ds verdict = true) ↔
      TraceChecks v.machine r tapes (traceOfD v.machine v.machine.start ds) ∧
        v.accepting (controlAfter v.machine.start (traceOfD v.machine v.machine.start ds)) =
          verdict := by
  have i0 : Fin v.tapeCount := ⟨0, by have := v.twoTapes; omega⟩
  unfold passOk TraceChecks ChecksFrom
  simp only [Bool.and_eq_true, beq_iff_eq]
  simp only [initialConfiguration, prefixTapes]
  constructor
  · intro h
    obtain ⟨⟨hok0, hh⟩, hacc⟩ := h i0
    rw [passRun_q] at hh hacc
    have hctl := ((passRun_ok_iff v.machine r i0 ds _ _ _ 0 (hwork i0)).mp hok0).1
    refine ⟨⟨hctl, fun i => ?_, hh⟩, hacc⟩
    exact ((passRun_ok_iff v.machine r i ds _ _ _ 0 (hwork i)).mp (h i).1.1).2
  · rintro ⟨⟨hctl, hrep, hh⟩, hacc⟩ i
    refine ⟨⟨(passRun_ok_iff v.machine r i ds _ _ _ 0 (hwork i)).mpr ⟨hctl, hrep i⟩, ?_⟩, ?_⟩
    · rw [passRun_q]; exact hh
    · rw [passRun_q]; exact hacc

end NearCubicGates.Adapters.Refuter
