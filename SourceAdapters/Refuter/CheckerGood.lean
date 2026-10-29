import SourceAdapters.Refuter.CheckerReadR

/-!
# Pass verdicts are tape-independent; transport of the reset state (input 7, F01, part 14)

`passGood` is a pass's verdict stated on the copied prefix itself; `passOk_iff_good` shows the
machine's pass verdict equals it for any work tape agreeing below the cutoff (so the stale contents
of the work tape beyond `r` never matter, proof of `lem:multitape-refuter`), and `goods_iff` assembles all tapes into
`TraceChecks` (the BGW check, SFM78 l.222–233). `RestEnc.congr`: the reset state survives changes of
the pass index and of loop counters.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- Pass `i`'s verdict on the copied prefix of tape `i`. -/
def passGood (v : RepairOrdinary.Verifier) (r : ℕ) (tapes : Fin v.tapeCount → List Bool)
    (ds : List (Fin v.tapeCount → Bool)) (verdict : Bool) (i : Fin v.tapeCount) : Prop :=
  ControlLegal v.machine v.machine.start (traceOfD v.machine v.machine.start ds) ∧
    TapeReplay r i (prefixTape r (tapes i)) 0 (traceOfD v.machine v.machine.start ds) ∧
    v.machine.halted (controlAfter v.machine.start (traceOfD v.machine v.machine.start ds)) = true ∧
    v.accepting (controlAfter v.machine.start (traceOfD v.machine v.machine.start ds)) = verdict

theorem passOk_iff_good (v : RepairOrdinary.Verifier) (r : ℕ) (tapes : Fin v.tapeCount → List Bool)
    (ds : List (Fin v.tapeCount → Bool)) (verdict : Bool) (i : Fin v.tapeCount) (tape : List Bool)
    (hag : AgreeBelow r tape (prefixTape r (tapes i))) :
    passOk v r i tape ds verdict = true ↔ passGood v r tapes ds verdict i := by
  unfold passOk passGood
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [passRun_q, passRun_ok_iff v.machine r i ds _ _ _ 0 hag]
  simp only [and_assoc]

theorem goods_iff (v : RepairOrdinary.Verifier) (r : ℕ) (tapes : Fin v.tapeCount → List Bool)
    (ds : List (Fin v.tapeCount → Bool)) (verdict : Bool) :
    (∀ i, passGood v r tapes ds verdict i) ↔
      TraceChecks v.machine r tapes (traceOfD v.machine v.machine.start ds) ∧
        v.accepting (controlAfter v.machine.start (traceOfD v.machine v.machine.start ds)) = verdict := by
  have i0 : Fin v.tapeCount := ⟨0, by have := v.twoTapes; omega⟩
  unfold passGood TraceChecks ChecksFrom
  simp only [initialConfiguration, prefixTapes]
  constructor
  · intro h
    exact ⟨⟨(h i0).1, fun i => (h i).2.1, (h i0).2.2.1⟩, (h i0).2.2.2⟩
  · rintro ⟨⟨hc, hr, hh⟩, ha⟩ i
    exact ⟨hc, hr i, hh, ha⟩

theorem srcOf_eq (v : RepairOrdinary.Verifier) (σ : St) (x w : List Bool) (hx : σ.st sXS = RepairOrdinary.frame x)
    (hy : σ.st sYS = RepairOrdinary.frame w) (hz : σ.st sZ = []) (i : Fin v.tapeCount) :
    srcOf σ i.val = v.inputTapes x w i := by
  unfold srcOf Verifier.inputTapes
  split_ifs <;> simp_all

/-- The registers a pass index change and the loop counters may touch. -/
abbrev idxR : List (Fin NR) := [rI, rTD, rTI]

theorem PassEnc.congr {v : RepairOrdinary.Verifier} {r : ℕ} {i : Fin v.tapeCount} {wD : List Bool}
    {σ τ : St} {st : PassSt v.stateCount} (h : PassEnc v r i wD σ st) (j : Fin v.tapeCount)
    (hs : SameExcept σ τ [] idxR) (hI : τ.val rI = j.val) : PassEnc v r j wD τ st := by
  have fs : ∀ x, τ.st x = σ.st x := fun x => (hs.1 x (by simp)).1
  have fsh : ∀ x, τ.sh x = σ.sh x := fun x => (hs.1 x (by simp)).2
  have fv : ∀ x, x ∉ idxR → τ.val x = σ.val x := fun x hx => hs.2.1 x hx
  exact {
    code := (by rw [fs]; exact h.code), codeh := (by rw [fsh]; exact h.codeh),
    t := (by rw [fv _ (by decide)]; exact h.t), wd := (by rw [fv _ (by decide)]; exact h.wd),
    ew := (by rw [fv _ (by decide)]; exact h.ew), hb := (by rw [fv _ (by decide)]; exact h.hb),
    tbl := (by rw [fv _ (by decide)]; exact h.tbl), bs := (by rw [fv _ (by decide)]; exact h.bs),
    ii := hI, ok := (by rw [fv _ (by decide)]; exact h.ok), q := (by rw [fv _ (by decide)]; exact h.q),
    h := (by rw [fv _ (by decide)]; exact h.h), sim := (by rw [fs]; exact h.sim),
    simh := (by rw [fsh]; exact h.simh), rs := (by rw [fs]; exact h.rs), rsh := (by rw [fsh]; exact h.rsh),
    wit := (by rw [fs]; exact h.wit), disph := (by rw [fsh]; exact h.disph),
    zQN := (by rw [fv _ (by decide)]; exact h.zQN), zMK := (by rw [fv _ (by decide)]; exact h.zMK),
    zP := (by rw [fv _ (by decide)]; exact h.zP), zOFF := (by rw [fv _ (by decide)]; exact h.zOFF),
    zBIT := (by rw [fv _ (by decide)]; exact h.zBIT), zTA := (by rw [fv _ (by decide)]; exact h.zTA),
    zTB := (by rw [fv _ (by decide)]; exact h.zTB), zTC := (by rw [fv _ (by decide)]; exact h.zTC),
    zPT := (by rw [fv _ (by decide)]; exact h.zPT), zW0 := (by rw [fv _ (by decide)]; exact h.zW0),
    zW1 := (by rw [fv _ (by decide)]; exact h.zW1), zM0 := (by rw [fv _ (by decide)]; exact h.zM0),
    zM1 := (by rw [fv _ (by decide)]; exact h.zM1), zDI := (by rw [fv _ (by decide)]; exact h.zDI),
    zA2 := (by rw [fv _ (by decide)]; exact h.zA2) }

theorem RestEnc.congr {v : RepairOrdinary.Verifier} {r : ℕ} {i : Fin v.tapeCount} {wD : List Bool} {p : ℕ}
    {σ τ : St} (h : RestEnc v r i wD p σ) (j : Fin v.tapeCount) (hs : SameExcept σ τ [] idxR)
    (hI : τ.val rI = j.val) : RestEnc v r j wD p τ := by
  have fs : ∀ x, τ.st x = σ.st x := fun x => (hs.1 x (by simp)).1
  have fsh : ∀ x, τ.sh x = σ.sh x := fun x => (hs.1 x (by simp)).2
  have fv : ∀ x, x ∉ idxR → τ.val x = σ.val x := fun x hx => hs.2.1 x hx
  have he := h.enc
  rw [← fs sSIM] at he
  exact {
    enc := he.congr j hs hI,
    cont := (by rw [fv _ (by decide)]; exact h.cont), wp := (by rw [fv _ (by decide)]; exact h.wp),
    wit := (by rw [fsh]; exact h.wit), start := (by rw [fv _ (by decide)]; exact h.start),
    vd := (by rw [fv _ (by decide)]; exact h.vd), r0 := (by rw [fv _ (by decide)]; exact h.r0),
    all := (by rw [fv _ (by decide)]; exact h.all), i1 := (by rw [fv _ (by decide)]; exact h.i1),
    tg := (by rw [fv _ (by decide)]; exact h.tg), ws := (by rw [fv _ (by decide)]; exact h.ws),
    xh := (by rw [fsh]; exact h.xh), yh := (by rw [fsh]; exact h.yh), zh := (by rw [fsh]; exact h.zh) }

end NearCubicGates.Adapters.Refuter.Mach
