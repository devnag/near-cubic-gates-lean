import SourceAdapters.Refuter.BodySetup

/-!
# The hierarchy verifier's body (input 7, the paper Step 1 and `cor:framed-refuter`)

proof of `lem:multitape-refuter`: "It then uses the shared prefix construction for two universal simulations: (a) the
rejecting-verdict acceptor `P_M^-`, for `M` on input `⟨M,N,0⟩` with witness `z`; (b) when `z≠1^{g}`, the
accepting-verdict acceptor `P_M^+`, for `M` on input `⟨M,N,z+1⟩` with a guessed witness … It accepts exactly
when the first simulation and, when required, the second simulation accept." In the framed convention
 the two simulations run on `fr(x_1), fr(w_i)` and on `fr(x_{i+1}), fr(v)`.

`body = setup ; check(VD=0) ; incr ; [unless last: XS := fr(x_{i+1}) ; YS := fr(v) ; VD := 1 ; check]`.
`body_spec`: on the record `x_i` of `M` and every witness word `w`, the body terminates, and its flag `ALL`
is set iff `BodyCond M N i w`: the first guessed trace passes `TraceChecks` on `fr(x_1), fr(w_i)` with a
rejecting verdict and, when `i+1 < 2^g`, the second guessed trace passes on `fr(x_{i+1}), fr(v)` with an
accepting verdict, `v` the `g` bits guessed after the first trace. The cost is `bodyCost`: `c_0N` with an
absolute `c_0`, plus `a_M`, plus the two checks' `a_M + b_M(n + r + 1)`.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.VerifierEncoding
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

def second : Pg := .seq incr (.ifr rLS WMX.skip (.seq copyX (.seq readV (.seq (WMX.inc rVD) checker))))

def body : Pg := .seq setup (.seq checker second)

/-! ## The verdict condition -/

/-- The first simulation's check: a rejecting halt of `M` on `fr(x_1), fr(w_i)` (proof of `lem:multitape-refuter`). -/
def ChecksA (M : OrdinaryWeakMachine) (N i : ℕ) (w : List Bool) : Prop :=
  TraceChecks M.verifier.machine (chkR0 w 0)
      (M.verifier.inputTapes (List.ofFn (record M N 0)) (List.ofFn (unrank (N / 16) i)))
      (traceOfD M.verifier.machine M.verifier.machine.start (chkDs w M.verifier.tapeCount 0)) ∧
    M.verifier.accepting (controlAfter M.verifier.machine.start
      (traceOfD M.verifier.machine M.verifier.machine.start (chkDs w M.verifier.tapeCount 0))) = false

/-- Where the second simulation's data start: after the first trace and the `g` guessed bits. -/
def startB (M : OrdinaryWeakMachine) (N : ℕ) (w : List Bool) : ℕ := chkEnd w M.verifier.tapeCount 0 + N / 16

/-- The second simulation's guessed witness `v`. -/
def guessV (M : OrdinaryWeakMachine) (N : ℕ) (w : List Bool) : List Bool :=
  gbits w (chkEnd w M.verifier.tapeCount 0) (N / 16)

/-- The second simulation's check: an accepting halt of `M` on `fr(x_{i+1}), fr(v)` (proof of `lem:multitape-refuter`). -/
def ChecksB (M : OrdinaryWeakMachine) (N i : ℕ) (w : List Bool) : Prop :=
  TraceChecks M.verifier.machine (chkR0 w (startB M N w))
      (M.verifier.inputTapes (List.ofFn (record M N (i + 1))) (guessV M N w))
      (traceOfD M.verifier.machine M.verifier.machine.start (chkDs w M.verifier.tapeCount (startB M N w))) ∧
    M.verifier.accepting (controlAfter M.verifier.machine.start
      (traceOfD M.verifier.machine M.verifier.machine.start (chkDs w M.verifier.tapeCount (startB M N w)))) = true

/-- **The body accepts** iff both required simulations are certified (proof of `lem:multitape-refuter`). -/
def BodyCond (M : OrdinaryWeakMachine) (N i : ℕ) (w : List Bool) : Prop :=
  ChecksA M N i w ∧ (i + 1 < 2 ^ (N / 16) → ChecksB M N i w)

/-- The body's cost: `c_0N` (absolute `c_0`) `+ a_M +` the two checks. -/
def bodyCost (M : OrdinaryWeakMachine) (N : ℕ) (w : List Bool) : ℕ :=
  300 * (N + 3) + 30 * ((code M.verifier).length + 2) * (machineIndex M + 2) +
    5000 * ((code M.verifier).length + 1) ^ 2 + 10 +
    checkerCost M.verifier (chkR0 w 0) (chkDs w M.verifier.tapeCount 0).length + 100 * (N + 1) + 200 * (N + 1) +
    100 * (N / 16 + 1) + checkerCost M.verifier (chkR0 w (startB M N w))
      (chkDs w M.verifier.tapeCount (startB M N w)).length + 30

/-- The register bound the body's semantics needs. -/
def bodyCap (M : OrdinaryWeakMachine) (N : ℕ) (w : List Bool) : ℕ :=
  64 * ((code M.verifier).length + 5 * w.length + 8) + 16 * (N + 4) + 2 * machineIndex M +
    200 * ((code M.verifier).length + 1) ^ 2

/-! ## After the first check -/

set_option maxHeartbeats 400000 in
theorem second_spec (M : OrdinaryWeakMachine) (N i : ℕ) (w : List Bool) (hv : machineIndex M + 2 + N / 16 ≤ N)
    (hg1 : 1 ≤ N / 16) (hi : i < 2 ^ (N / 16)) (τ1 : St)
    (hpre : ChkPre M.verifier w (chkEnd w M.verifier.tapeCount 0) (List.ofFn (record M N 0))
      (List.ofFn (unrank (N / 16) i)) τ1)
    (hX : τ1.st sIN = RepairOrdinary.frame (List.ofFn (record M N i))) (hXh : τ1.sh sIN = 0) (hE : τ1.val rTE = N)
    (hS : τ1.val rS = N / 16) (hLS : τ1.val rLS = 0) (hVD : τ1.val rVD = 0) (hcap : bodyCap M N w ≤ cap) :
    ∃ τ c, WXExec cap second τ1 τ c ∧
      (τ.val rALL ≠ 0 ↔ τ1.val rALL ≠ 0 ∧ (i + 1 < 2 ^ (N / 16) → ChecksB M N i w)) ∧
      c ≤ 100 * (N + 1) + 200 * (N + 1) + 100 * (N / 16 + 1) + checkerCost M.verifier (chkR0 w (startB M N w))
        (chkDs w M.verifier.tapeCount (startB M N w)).length + 20 := by
  have hcap' : bodyCap M N w ≤ cap := hcap
  unfold bodyCap at hcap'
  set g := N / 16 with hg
  set v := M.verifier with hvv
  set L := List.ofFn (record M N i) with hL
  have hLl : L.length = N := by simp [L]
  have hz := hpre.zero
  by_cases hall : ∀ m < g, i.testBit m = true
  · -- the last record: no second simulation
    obtain ⟨c1, e1, hc1⟩ := incr_spec cap τ1 L N g hLl hg1 (by omega) hX hXh hE hS (hz rTD (by decide))
      (hz rCONT (by decide)) hLS (hz rTA (by decide)) (hz rTB (by decide)) (by omega) none
      (fun m hm => (record_bit M N i m hm (by omega) hv).trans (hall m hm))
    have e2 : WXExec cap (.ifr rLS WMX.skip (.seq copyX (.seq readV (.seq (WMX.inc rVD) checker))))
        (incrOut τ1 L N g none) (incrOut τ1 L N g none) 1 :=
      WXExec.ifrT (by simp [incrOut]) (WXExec.skip cap _)
    refine ⟨_, _, WXExec.seq e1 e2, ?_, by omega⟩
    have hlast : ¬ i + 1 < 2 ^ g := by rw [all_ones_last g i hi hall]; omega
    simp only [incrOut, ist, Function.update_apply]
    simp [hlast]
  · -- the second simulation
    have hex : ∃ m, m < g ∧ i.testBit m = false := by
      by_contra h; push Not at h; exact hall (fun m hm => by simpa using h m hm)
    classical
    set k := Nat.find hex with hk
    obtain ⟨hkg, hkz⟩ := Nat.find_spec hex
    have hkm : ∀ m < k, i.testBit m = true := by
      intro m hm
      have := Nat.find_min hex hm
      push Not at this
      by_contra h'; exact absurd (this (by omega)) (by simpa using h')
    have hnext : i + 1 < 2 ^ g := not_all_ones g i hi k hkg hkz
    obtain ⟨c1, e1, hc1⟩ := incr_spec cap τ1 L N g hLl hg1 (by omega) hX hXh hE hS (hz rTD (by decide))
      (hz rCONT (by decide)) hLS (hz rTA (by decide)) (hz rTB (by decide)) (by omega) (some k)
      ⟨hkg, fun m hm => (record_bit M N i m (by omega) (by omega) hv).trans (hkm m hm),
        (record_bit M N i k hkg (by omega) hv).trans hkz⟩
    set L1 := List.ofFn (record M N (i + 1)) with hL1
    have hinc : (clrL L k).set (N - 1 - k) true = L1 := record_incr M N i k hkg hv hkm hkz
    simp only [incrOut, hinc] at e1
    set σa := ist τ1 L1 (2 * N - 1 - 2 * k) 0 0 0 with hσa
    -- XS := fr(x_{i+1})
    obtain ⟨c2, e2, hc2⟩ := copyX_spec cap σa L1 N (by simp [L1]) (by simp [σa]) (by simp [σa]; omega)
      (by simp [σa, ist, Function.update_apply, hpre.xs, frame_length]) (by simp [σa, ist, Function.update_apply, hpre.xh])
      (by simp [σa, ist, Function.update_apply, hE]) (by simp [σa])
      (by simp [σa, ist, Function.update_apply, hz rTA (by decide)])
      (by simp [σa, ist, Function.update_apply, hz rTB (by decide)])
      (by simp [σa, ist, Function.update_apply, hz rTG (by decide)]) (by omega)
    set σb := (σa.seth sIN 0).sets sXS (RepairOrdinary.frame L1) with hσb
    -- YS := fr(v)
    set e := chkEnd w v.tapeCount 0 with he
    obtain ⟨c3, e3, hc3⟩ := readV_spec cap σb w e g (by simp [σb, σa, ist, Function.update_apply, hpre.wit])
      (by simp [σb, σa, ist, Function.update_apply, hpre.wh])
      (by simp [σb, σa, ist, Function.update_apply, hpre.ys, frame_length])
      (by simp [σb, σa, ist, Function.update_apply, hpre.yh]) (by simp [σb, σa, ist, Function.update_apply, hS])
      (by simp [σb, σa, ist, Function.update_apply, hz rBIT (by decide)])
      (by simp [σb, σa, ist, Function.update_apply, hz rWP (by decide)])
      (by simp [σb, σa, ist, Function.update_apply, hz rTG (by decide)])
      (by simp [σb, σa, ist, Function.update_apply, hz rTB (by decide)]) (by omega)
    set σc := (σb.seth sWIT (2 * min (e + g) w.length)).sets sYS (RepairOrdinary.frame (gbits w e g)) with hσc
    have vc : σc.val rVD = 0 := by simp [σc, σb, σa, ist, Function.update_apply, hVD]
    have e4 := WXExec.inc cap rVD σc (by rw [vc]; omega)
    rw [vc, Nat.zero_add] at e4
    set σd := σc.setv rVD 1 with hσd
    -- σd agrees with τ1 off the touched fields
    have dv : ∀ R, R ≠ rTD → R ≠ rCONT → R ≠ rLS → R ≠ rVD → σd.val R = τ1.val R := by
      intro R h1 h2 h3 h4; simp [σd, σc, σb, σa, ist, Function.update_apply, h1, h2, h3, h4]
    have dst : ∀ X, X ≠ sIN → X ≠ sXS → X ≠ sYS → σd.st X = τ1.st X := by
      intro X h1 h2 h3; simp [σd, σc, σb, σa, ist, Function.update_apply, h1, h2, h3]
    have dsh : ∀ X, X ≠ sIN → X ≠ sWIT → σd.sh X = τ1.sh X := by
      intro X h1 h2; simp [σd, σc, σb, σa, ist, Function.update_apply, h1, h2]
    have hpreB : ChkPre v w (startB M N w) L1 (guessV M N w) σd := {
      code := by rw [dst _ (by decide) (by decide) (by decide)]; exact hpre.code
      codeh := by rw [dsh _ (by decide) (by decide)]; exact hpre.codeh
      t := by rw [dv _ (by decide) (by decide) (by decide) (by decide)]; exact hpre.t
      wd := by rw [dv _ (by decide) (by decide) (by decide) (by decide)]; exact hpre.wd
      ew := by rw [dv _ (by decide) (by decide) (by decide) (by decide)]; exact hpre.ew
      hb := by rw [dv _ (by decide) (by decide) (by decide) (by decide)]; exact hpre.hb
      tbl := by rw [dv _ (by decide) (by decide) (by decide) (by decide)]; exact hpre.tbl
      bs := by rw [dv _ (by decide) (by decide) (by decide) (by decide)]; exact hpre.bs
      start := by rw [dv _ (by decide) (by decide) (by decide) (by decide)]; exact hpre.start
      wit := by rw [dst _ (by decide) (by decide) (by decide)]; exact hpre.wit
      wh := by simp [σd, σc, startB, he, hg]; rfl
      rs := by rw [dst _ (by decide) (by decide) (by decide)]; exact hpre.rs
      rsh := by rw [dsh _ (by decide) (by decide)]; exact hpre.rsh
      simh := by rw [dsh _ (by decide) (by decide)]; exact hpre.simh
      disph := by rw [dsh _ (by decide) (by decide)]; exact hpre.disph
      xs := by simp [σd, σc, σb, Function.update_apply]
      ys := by simp [σd, σc, guessV, he, hg]; rfl
      z := by rw [dst _ (by decide) (by decide) (by decide)]; exact hpre.z
      xh := by rw [dsh _ (by decide) (by decide)]; exact hpre.xh
      yh := by rw [dsh _ (by decide) (by decide)]; exact hpre.yh
      zh := by rw [dsh _ (by decide) (by decide)]; exact hpre.zh
      vd := by simp [σd]
      all := by rw [dv _ (by decide) (by decide) (by decide) (by decide)]; exact hpre.all
      zero := by
        intro R hR
        by_cases h1 : R = rTD
        · subst h1; simp [σd, σc, σb, σa, ist, Function.update_apply]
        · by_cases h2 : R = rCONT
          · subst h2; simp [σd, σc, σb, σa, ist, Function.update_apply]
          · rw [dv R h1 h2 (by rintro rfl; simp at hR) (by rintro rfl; simp at hR)]; exact hz R hR }
    obtain ⟨τ, c5, e5, _, hall5, _, hc5⟩ := checker_spec cap v w (startB M N w) L1 (guessV M N w) σd hpreB
      (by omega)
    have e6 : WXExec cap (.ifr rLS WMX.skip (.seq copyX (.seq readV (.seq (WMX.inc rVD) checker)))) σa τ _ :=
      WXExec.ifrF (by simp [σa]) (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))
    refine ⟨τ, _, WXExec.seq e1 e6, ?_, ?_⟩
    · rw [hall5, dv _ (by decide) (by decide) (by decide) (by decide)]
      simp only [σd, WState.setv_val, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, decide_true]
      unfold ChecksB
      simp only [hnext, true_implies]
      exact Iff.rfl
    · omega

/-! ## The whole body -/

set_option maxHeartbeats 400000 in
/-- **The body** (proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`): on the record `x_i` of `M` (valid, `g ≥ 1`) and every witness
word, it terminates with `ALL ≠ 0 ↔ BodyCond M N i w`, within `bodyCost M N w`. -/
theorem body_spec (M : OrdinaryWeakMachine) (N i : ℕ) (w : List Bool) (hv : machineIndex M + 2 + N / 16 ≤ N)
    (hg1 : 1 ≤ N / 16) (hi : i < 2 ^ (N / 16)) (hcap : bodyCap M N w ≤ cap) :
    ∃ τ c, WXExec cap body (coldSt (List.ofFn (record M N i)) w) τ c ∧
      (τ.val rALL ≠ 0 ↔ BodyCond M N i w) ∧ c ≤ bodyCost M N w := by
  have hcap' : bodyCap M N w ≤ cap := hcap
  unfold bodyCap at hcap'
  obtain ⟨σ1, c1, e1, hpre1, hX1, hXh1, hE1, hS1, hLS1, hVD1, hALL1, hc1⟩ :=
    setup_spec cap M N i w hv (by omega)
  obtain ⟨τ1, c2, e2, hpre2, hall2, hf2, hc2⟩ := checker_spec cap M.verifier w 0 _ _ σ1 hpre1 (by omega)
  have fv : ∀ R, R ∉ chkR → τ1.val R = σ1.val R := fun R hR => hf2.2.1 R hR
  have fs : ∀ X, X ∉ chkS → τ1.st X = σ1.st X := fun X hX => (hf2.1 X hX).1
  have fsh : ∀ X, X ∉ chkS → τ1.sh X = σ1.sh X := fun X hX => (hf2.1 X hX).2
  obtain ⟨τ, c3, e3, hall3, hc3⟩ := second_spec cap M N i w hv hg1 hi τ1 hpre2
    (by rw [fs _ (by decide)]; exact hX1) (by rw [fsh _ (by decide)]; exact hXh1)
    (by rw [fv _ (by decide)]; exact hE1) (by rw [fv _ (by decide)]; exact hS1)
    (by rw [fv _ (by decide)]; exact hLS1) (by rw [fv _ (by decide)]; exact hVD1) hcap
  refine ⟨τ, _, WXExec.seq e1 (WXExec.seq e2 e3), ?_, ?_⟩
  · rw [hall3, hall2, hALL1, hVD1]
    unfold BodyCond ChecksA
    simp
  · unfold bodyCost; omega

end NearCubicGates.Adapters.Refuter.Mach
