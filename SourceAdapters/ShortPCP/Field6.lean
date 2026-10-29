import SourceAdapters.ShortPCP.VerifierAmplified
import SourceAdapters.Joins.ComputationToCircuit
import SourceAdapters.Machine.OrdinaryToTM2
import SourceAdapters.Assembly.OrdinaryField

/-!
# Input 6 from the affine constraint reduction, the single-run time, and the circuit compiler

Consumers: `NearCubicWires.Bindings.MW20.MW20_OracleCircuitPCP_TM2` (the `shortPCP` field of `NineInputs`) and its
ordinary-machine form `Assembly.OrdinaryOracleCircuitPCP`.

Paper anchors: proof of `thm:short-pcp-ours` (`n = 1`, Steps 1–4, "The properties of `C^O_x`"); `cor:short-pcp-clock`
(the clock `t = T(n)` is supplied in binary); "The exact Lean interface" (input `fr(x) fr(bits t)`, the zero-input
constant-false circuit for `n ≤ 1`, the two resource inequalities, the TM2 realization).

The construction (one constructor for every input length):
- `n ≥ 2`: `r = (x, T(n))`; Step 1 (`Joins.AffineConstraintReduction`) gives the instance `c` and the padded input
  `x̄`; the request of the time program is `SingleRun.request c x̄ S` (H-test parameter `d_H = 2^{f−2}`) with
  `S = Amplified.masks c n K1 b1` (Step 3); `ℓ = |bits K_L| + f + b_L·|bits f|`; the compilation request is
  `(data, ℓ, K_T(|data| + ℓ + 1)^{e_T})`; the circuit is the compiler's (`Joins.ComputationToCircuit`) on it;
- `n ≤ 1`: the zero-input, one-node constant-false circuit.

Proved here (Step 4 and "The properties of `C^O_x`"): the satisfying assignments of the compiled circuit are exactly
the seeds on which `V1` rejects, unsatisfiability for the honest oracle, the count `≥ 2^ℓ(1 − 1/n)` otherwise
(prefix uniformity), `2^ℓ ≤ K·t·logScale(t)^e`, the circuit size and the compilation-request size
`poly(n + natBitLength t + 1)`, and the TM2 realization through the ordinary-to-TM2 simulation.

Hypotheses: `Joins.AffineConstraintReduction` (Step 1), `Joins.AmplifiedVerifier` (Steps 2–3; proved from
BCGT13 Theorem 11.1 by `amplifiedVerifier`), `Joins.SingleRunTime` (Step 2, "Time and queries"),
`Joins.ComputationToCircuit` (Step 4), and the two machines `MaskMachine` (Step 3: "constructing the field and listing
the multiset also take `poly(n, log T)` time") and `AssemblyMachine` (Step 4: "The algorithm `A` computes `T`, `I_x`,
`S` and `C^O_x` in `poly(n, log T)` time").
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.Bindings.MW20
open NearCubicWires.WireExponent3_5 NearCubicGates.Published.BCGT13
open NearCubicGates.Adapters.ACSP.Affine NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun
open NearCubicGates.Adapters.Joins.SingleRun.Amplified NearCubicGates.Adapters.Compile
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Verifier

/-! ## The construction -/

/-- "The exact Lean interface": "a zero-input, one-node constant-false circuit, with `ℓ = 0` and oracle arity zero". -/
def falseCircuit : OracleCircuit 0 0 where
  nodes := [.const false]
  output := ⟨0, by simp⟩
  wellFormed := by
    intro i
    rcases i with ⟨_ | k, h⟩
    · trivial
    · simp at h

/-- The output for `n ≤ 1` (proof of `thm:short-pcp-ours`; "The exact Lean interface"). -/
def falseOutput : OracleOutput := ⟨0, falseCircuit⟩

theorem falseCircuit_eval (O : BitInput 0 → Bool) (z : BitInput 0) : falseCircuit.eval O z = false := rfl

/-- The multiset `S` of Step 3 as a function of `(r_0, f, n)`; `Amplified.masks` depends on the instance only through
`r_0` and `f`. -/
def masksOf (r f n K1 b1 : ℕ) : List (List Bool) :=
  let m := mDeg (r ^ 2 * n * K1 * f ^ b1)
  (List.range (2 ^ m)).flatMap fun a => (List.range (2 ^ m)).map fun b => sigma m r a b

theorem masks_eq_masksOf (c : Instance) (n K1 b1 : ℕ) : masks c n K1 b1 = masksOf (r0 c) c.f n K1 b1 := rfl

/-- `r_0` as a function of `f` alone: `max(rand_{RS,=}(f), f)` (Step 2 (a): every sub-verifier on a domain of
dimension `f > η` uses `rand_{RS,=}(f)` or `max(rand_{RS,=}(f), f)` coins, and the consistency test uses `f`). -/
def r0f (f : ℕ) : ℕ := max (randEq tuple0 f) f

theorem randRS_le (κ d : ℕ) : randRS tuple0 κ d ≤ max (randEq tuple0 κ) κ := by
  unfold randRS; split_ifs <;> omega

theorem randRS_ge (κ d : ℕ) (h : tuple0.η < κ) : randEq tuple0 κ ≤ randRS tuple0 κ d := by
  unfold randRS; split_ifs <;> omega

/-- **`r_0 = max(rand_{RS,=}(f), f)`** for `f > η = 2`. -/
theorem r0_eq (c : Instance) (hf : 2 < c.f) : r0 c = r0f c.f := by
  have h1 := randRS_le c.f (2 ^ c.mH - 1)
  have h2 := randRS_le c.f (dH c - 2 ^ c.mH)
  have h3 := randRS_le c.f (2 ^ c.mH - 1 - 2 ^ c.m)
  have h4 := randRS_ge c.f (2 ^ c.mH - 1) hf
  unfold r0 r0f randVRS
  omega

/-- The fixed data of the construction for one verifier: Step 1's instance map and padded input, Step 3's constants
`K1, b1`, the fuel constants `KT, eT` of the time program, the resource constants `KL, bL` of Step 2 (a), and the
compiler's circuit family. -/
structure Pipeline where
  inst : ClockRequest → Instance
  xbar : ClockRequest → List Bool
  K1 : ℕ
  b1 : ℕ
  KT : ℕ
  eT : ℕ
  KL : ℕ
  bL : ℕ
  circuit : (q : OracleCompilationRequest) → OracleCircuit q.ell q.ell

namespace Pipeline

variable (P : Pipeline) (r : ClockRequest)

/-- Steps 2–3: the request of the time program: the instance, `d_H`, and the multiset `S` of the powering
construction. -/
def request : Request := SingleRun.request (P.inst r) (P.xbar r) (masks (P.inst r) r.1.1 P.K1 P.b1)

/-- Step 4: the seed and address length. The proof takes `ℓ = max{r_0, ⌈log L_π⌉}`; we take the computable upper
bound `ℓ = |bits K_L| + f + b_L·|bits f|` from `2^{r_0}, L_π ≤ K_L·2^f·f^{b_L}`, which has the same two properties
used (`r_0 ≤ ℓ`, `L_π ≤ 2^ℓ`) and the same order `log T + O(log log T)`; it needs only `f`. -/
def ell : ℕ := natBitLength P.KL + (P.inst r).f + P.bL * natBitLength (P.inst r).f

/-- Step 4: the compilation request: the data word, `ℓ`, and the fuel `K_T(|data| + ℓ + 1)^{e_T}` of the time program
on `ℓ` coins. -/
def compRequest : OracleCompilationRequest where
  data := (P.request r).data
  ell := P.ell r
  fuel := P.KT * ((P.request r).data.length + P.ell r + 1) ^ P.eT

/-- "Let `C^O_x` be its negation" (Step 4): the compiler's circuit on the compilation request. -/
def pcpOutput : OracleOutput := ⟨(P.compRequest r).ell, P.circuit (P.compRequest r)⟩

/-- One constructor for every input length ("The exact Lean interface"). -/
def output : OracleOutput := if 2 ≤ r.1.1 then P.pcpOutput r else falseOutput

end Pipeline

/-! ## The two machine hypotheses -/

/-- The request word of the mask machine: `f`, `n` as self-delimiting numbers. -/
def maskWord (q : ℕ × ℕ) : List Bool := natWord q.1 ++ natWord q.2

/-- **The mask machine** (Step 3: "Choosing `m` uses only integer comparisons; constructing the field and listing the
multiset also take `poly(n, log T)` time"): for fixed `K1, b1`, one ordinary word function lists the multiset `S`
(`2^{2m}` vectors of `r_0 = r0f f` bits, `σ_{a,b} = (a^j · b)_{j<r_0}` over `𝔽_{2^m}`) from `(f, n)` in time
polynomial in `f + n`. -/
def MaskMachine : Prop :=
  ∀ K1 b1 : ℕ, ∃ K e : ℕ, Nonempty (OrdinaryWordFunction (ℕ × ℕ) maskWord
    (fun q => listWord frame (masksOf (r0f q.1) q.1 q.2 K1 b1))
    (fun q => K * (q.1 + q.2 + 1) ^ e))

/-- **The top-level ordinary machine** (Step 4: "The algorithm `A` computes `T`, `I_x` (`lem:generator`), `S` and
`C^O_x` in `poly(n, log T)` time"; "The exact Lean interface": it receives `fr(x) fr(bits(t))` and outputs the
constant-false circuit for `n ≤ 1`). From the generator of Step 1, the mask machine and the compiler's generator, one
ordinary word function maps `fr(x) fr(bits t)` (with `n ≤ t`) to the word of the output circuit, given the shape of
`x̄` (from which `n` is read) and the size of the compilation request on promised requests. -/
def AssemblyMachine : Prop :=
  ∀ (P : Pipeline) (KS eS KM eM KX dX KB eB : ℕ),
    -- `lem:generator`: the last conjunct of `AffineConstraintReduction` (framed, `x̄` first)
    Nonempty (OrdinaryWordFunction ClockRequest ClockRequest.word
      (fun r => frame (frame (P.xbar r) ++ (P.inst r).word)) (fun r => KS * (r.1.1 + natBitLength r.2 + 1) ^ eS)) →
    -- the mask machine for `P`'s constants
    Nonempty (OrdinaryWordFunction (ℕ × ℕ) maskWord
      (fun q => listWord frame (masksOf (r0f q.1) q.1 q.2 P.K1 P.b1))
      (fun q => KM * (q.1 + q.2 + 1) ^ eM)) →
    -- the compiler's generator for `P`'s circuits
    Nonempty (OrdinaryWordFunction OracleCompilationRequest OracleCompilationRequest.word
      (fun q => OracleOutput.word ⟨q.ell, P.circuit q⟩) (fun q => KX * q.measure ^ dX)) →
    -- on promised requests: the shape of `x̄` (`lem:tm-ram`), `r_0` and `d_H` as functions of `f` (`d_H = 2^{f−2}`
    -- holds by definition), the size of the compilation request, `2 ≤ f` and the modulus bit `irr_f = 1` (so
    -- `f < |word|`, which sizes the machine's registers)
    (∀ r : ClockRequest, 2 ≤ r.1.1 → r.1.1 ≤ r.2 →
      (∃ j, P.xbar r = List.ofFn r.1.2 ++ true :: List.replicate j false) ∧
      r0 (P.inst r) = r0f (P.inst r).f ∧ dH (P.inst r) = 2 ^ ((P.inst r).f - 2) ∧
      (P.compRequest r).measure ≤ KB * (r.1.1 + natBitLength r.2 + 1) ^ eB ∧
      2 ≤ (P.inst r).f ∧ (P.inst r).irr.testBit (P.inst r).f = true) →
    ∃ K e : ℕ, Nonempty (OrdinaryWordFunction {r : ClockRequest // r.1.1 ≤ r.2} (fun r => r.1.word)
      (fun r => (P.output r.1).word) (fun r => K * (r.1.word.length + 1) ^ e))

/-! ## Lengths and numeric facts -/

theorem frame_length (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [RepairSource.frame, RepairOrdinary.frame, List.length_cons] at ih ⊢; omega

theorem natWord_length (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := by
  simp [natWord, WilliamsPublishedForm.framedNatBits, WilliamsPublishedForm.fixedWidthNatBits]; omega

theorem flatten_frame_length (S : List (List Bool)) (k : ℕ) (hS : ∀ σ ∈ S, σ.length = k) :
    (S.map frame).flatten.length = S.length * (2 * k + 1) := by
  induction S with
  | nil => simp
  | cons σ S ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, frame_length, List.length_cons]
    rw [hS σ (by simp), ih (fun τ h => hS τ (by simp [h]))]
    ring

theorem log_le_self' (v : ℕ) : Nat.log 2 v ≤ v := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  · exact Nat.lt_two_pow_self.le.trans (Nat.pow_log_le_self 2 hv.ne')

theorem natBitLength_le_self (v : ℕ) : natBitLength v ≤ v + 1 := by
  unfold natBitLength; have := log_le_self' v; omega

theorem natBitLength_le_of_le_pow {v k : ℕ} (h : v ≤ 2 ^ k) : natBitLength v ≤ k + 1 := by
  unfold natBitLength
  have := Nat.log_mono_right (b := 2) h
  rw [Nat.log_pow (by norm_num)] at this
  omega

theorem logScale_le (t : ℕ) : logScale t ≤ natBitLength t + 1 := by
  unfold logScale natBitLength
  apply Nat.clog_le_of_le_pow
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) t
  rw [Nat.succ_eq_add_one] at h
  rw [pow_succ]
  omega

theorem one_le_logScale (t : ℕ) : 1 ≤ logScale t :=
  Nat.clog_pos (by norm_num) (by omega)

/-- `K·2^f·f^b ≤ 2^{K + f(b+1)}`. -/
theorem le_two_pow_of {K f b : ℕ} : K * 2 ^ f * f ^ b ≤ 2 ^ (K + f * (b + 1)) := by
  have hK : K ≤ 2 ^ K := Nat.lt_two_pow_self.le
  have hf : f ^ b ≤ 2 ^ (f * b) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le b
  calc K * 2 ^ f * f ^ b ≤ 2 ^ K * 2 ^ f * 2 ^ (f * b) := by gcongr
    _ = 2 ^ (K + f * (b + 1)) := by rw [← pow_add, ← pow_add]; ring_nf

theorem le_of_two_pow_le {r K f b : ℕ} (h : 2 ^ r ≤ K * 2 ^ f * f ^ b) : r ≤ K + f * (b + 1) :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp (h.trans le_two_pow_of)

/-! ## Polynomial bounds on a set of requests -/

/-- `g ≤ K·B^e` on the requests satisfying `D`. -/
def PolyOn {α : Type} (D : α → Prop) (B g : α → ℕ) : Prop := ∃ K e : ℕ, ∀ a, D a → g a ≤ K * B a ^ e

namespace PolyOn

variable {α : Type} {D : α → Prop} {B : α → ℕ}

theorem const (k : ℕ) : PolyOn D B fun _ => k := ⟨k, 0, fun _ _ => by simp⟩

theorem base : PolyOn D B B := ⟨1, 1, fun _ _ => by simp⟩

theorem mono {g h : α → ℕ} (hh : PolyOn D B h) (hle : ∀ a, D a → g a ≤ h a) : PolyOn D B g := by
  obtain ⟨K, e, hK⟩ := hh
  exact ⟨K, e, fun a ha => (hle a ha).trans (hK a ha)⟩

theorem add (hB : ∀ a, D a → 1 ≤ B a) {g h : α → ℕ} (hg : PolyOn D B g) (hh : PolyOn D B h) :
    PolyOn D B fun a => g a + h a := by
  obtain ⟨K1, e1, h1⟩ := hg
  obtain ⟨K2, e2, h2⟩ := hh
  refine ⟨K1 + K2, max e1 e2, fun a ha => ?_⟩
  have p1 : B a ^ e1 ≤ B a ^ max e1 e2 := Nat.pow_le_pow_right (hB a ha) (le_max_left _ _)
  have p2 : B a ^ e2 ≤ B a ^ max e1 e2 := Nat.pow_le_pow_right (hB a ha) (le_max_right _ _)
  calc g a + h a ≤ K1 * B a ^ e1 + K2 * B a ^ e2 := Nat.add_le_add (h1 a ha) (h2 a ha)
    _ ≤ K1 * B a ^ max e1 e2 + K2 * B a ^ max e1 e2 := by gcongr
    _ = (K1 + K2) * B a ^ max e1 e2 := by ring

theorem mul {g h : α → ℕ} (hg : PolyOn D B g) (hh : PolyOn D B h) : PolyOn D B fun a => g a * h a := by
  obtain ⟨K1, e1, h1⟩ := hg
  obtain ⟨K2, e2, h2⟩ := hh
  refine ⟨K1 * K2, e1 + e2, fun a ha => ?_⟩
  calc g a * h a ≤ (K1 * B a ^ e1) * (K2 * B a ^ e2) := Nat.mul_le_mul (h1 a ha) (h2 a ha)
    _ = K1 * K2 * B a ^ (e1 + e2) := by ring

theorem pow {g : α → ℕ} (hg : PolyOn D B g) (k : ℕ) : PolyOn D B fun a => g a ^ k := by
  obtain ⟨K, e, h⟩ := hg
  refine ⟨K ^ k, e * k, fun a ha => ?_⟩
  calc g a ^ k ≤ (K * B a ^ e) ^ k := Nat.pow_le_pow_left (h a ha) k
    _ = K ^ k * B a ^ (e * k) := by rw [mul_pow, ← pow_mul]

end PolyOn

/-! ## The verdict of the compiled circuit is `V1` -/

/-- The body of `Joins.SingleRunTime` for a fixed program and fuel constants. -/
def TimeSpec (prog : OrdinaryOracleProgram) (KT eT : ℕ) : Prop :=
  ∀ q : Request, q.Valid →
    ∀ (F : Type) [Field F] [DecidableEq F] (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F),
      Function.Bijective φ → ∀ (o : ℕ → Bool) (R : List Bool),
        OrdinaryOracleRuns o prog (q.input R) [q.patchedVerdict φ (q.decode φ o) R]
          (KT * (q.data.length + R.length + 1) ^ eT) ∧
        ∀ (out : List Bool) (budget : ℕ), OrdinaryOracleRuns o prog (q.input R) out budget →
          out = [q.patchedVerdict φ (q.decode φ o) R]

/-- **The compiled circuit evaluates to `false` exactly when `V1` accepts** (Step 4: the circuit "outputs the verdict
of `V_1` on the proof `π_O` whose bit at address `a` is `O(a)`", and `C^O_x` is its negation). -/
theorem eval_false_iff {Kc : ℕ} {c : Instance} {xs : List Bool} {prog : OrdinaryOracleProgram} {KT eT : ℕ}
    (hrun : TimeSpec prog KT eT)
    {circuit : (q : OracleCompilationRequest) → OracleCircuit q.ell q.ell}
    (hev : ∀ (q : OracleCompilationRequest) (O : BitInput q.ell → Bool) (z : BitInput q.ell),
      (circuit q).eval O z = false ↔ OrdinaryOracleRuns (fixedArityOracle O) prog (q.runInput z) [true] q.fuel)
    (hG : SingleRun.Good Kc c xs) (n K1 b1 ℓ : ℕ) (O : BitInput ℓ → Bool) (z : BitInput ℓ) :
    (circuit ⟨(SingleRun.request c xs (masks c n K1 b1)).data, ℓ,
        KT * ((SingleRun.request c xs (masks c n K1 b1)).data.length + ℓ + 1) ^ eT⟩).eval O z = false ↔
      Amplified.accepts c xs n K1 b1 (fixedArityOracle O) (List.ofFn z) = true := by
  haveI : Fact (Irreducible c.irrPoly) := ⟨Good.irr hG⟩
  letI : DecidableEq c.Fld := Classical.decEq _
  obtain ⟨hr, hdet⟩ := hrun _ (Good.valid_request hG _) c.Fld (RingHom.id c.Fld) Function.bijective_id
    (fixedArityOracle O) (List.ofFn z)
  rw [List.length_ofFn] at hr
  rw [hev, amplified_eq hG]
  change OrdinaryOracleRuns (fixedArityOracle O) prog
    ((SingleRun.request c xs (masks c n K1 b1)).input (List.ofFn z)) [true]
    (KT * ((SingleRun.request c xs (masks c n K1 b1)).data.length + ℓ + 1) ^ eT) ↔ _
  constructor
  · intro h
    have := hdet _ _ h
    simp only [List.cons.injEq, and_true] at this
    exact this.symm
  · intro h
    rw [h] at hr
    exact hr

/-! ## Completeness and soundness of the compiled circuit -/

open Finset in
/-- Counting through the first `r` of `ℓ` seed bits (prefix uniformity): if a test accepts at most an `s` fraction of
`{0,1}^r`, its rejecting seeds in `{0,1}^ℓ` number at least `2^ℓ(1 − s)`. -/
theorem count_reject {r ℓ : ℕ} (hℓ : r ≤ ℓ) (t : (Fin r → Bool) → Bool) (s : ℝ) (ht : acceptFrac t ≤ s) :
    (2 : ℝ) ^ ℓ * (1 - s) ≤ ((univ.filter fun z : Fin ℓ → Bool => t (pre r hℓ z) = false).card : ℝ) := by
  classical
  have hpre := acceptFrac_pre hℓ t
  have hfrac : ((univ.filter fun z : Fin ℓ → Bool => t (pre r hℓ z) = true).card : ℝ) / 2 ^ ℓ ≤ s := by
    have h := hpre.trans_le ht
    unfold acceptFrac at h
    exact h
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin ℓ → Bool)))
    (fun z => t (pre r hℓ z) = true)
  have hneg : (univ.filter fun z : Fin ℓ → Bool => ¬ t (pre r hℓ z) = true) =
      univ.filter fun z : Fin ℓ → Bool => t (pre r hℓ z) = false := by
    apply Finset.filter_congr; intro z _; simp
  rw [hneg, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hsplit
  have hpos : (0 : ℝ) < 2 ^ ℓ := by positivity
  have hle : ((univ.filter fun z : Fin ℓ → Bool => t (pre r hℓ z) = true).card : ℝ) ≤ s * 2 ^ ℓ := by
    rwa [div_le_iff₀ hpos] at hfrac
  have hcast : ((univ.filter fun z : Fin ℓ → Bool => t (pre r hℓ z) = true).card : ℝ) +
      ((univ.filter fun z : Fin ℓ → Bool => t (pre r hℓ z) = false).card : ℝ) = 2 ^ ℓ := by
    exact_mod_cast hsplit
  nlinarith

theorem fixedArityOracle_maskOfBits (π : ℕ → Bool) {ℓ a : ℕ} (ha : a < 2 ^ ℓ) :
    fixedArityOracle (fun w : BitInput ℓ => π (maskOfBits w)) a = π a := by
  show π (maskOfBits (bitsOf ℓ a)) = π a
  rw [maskOfBits_bitsOf ℓ a ha]

/-- The first `r` seed bits read as a list agree with the seed below `r`. -/
theorem ofFn_pre_getD {r ℓ : ℕ} (hℓ : r ≤ ℓ) (z : Fin ℓ → Bool) (i : ℕ) (hi : i < r) :
    (List.ofFn (pre r hℓ z)).getD i false = (List.ofFn z).getD i false := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simp; omega)]
  simp [pre]

/-! ## The size of the compilation request -/

/-- The data word of the time program's request: the instance word, `x̄`, `d_H`, and `S`. -/
theorem data_length_le (c : Instance) (xs : List Bool) (S : List (List Bool)) (hS : ∀ σ ∈ S, σ.length = r0 c) :
    (SingleRun.request c xs S).data.length ≤
      c.word.length + 2 * xs.length + 2 * c.f + 2 * S.length + S.length * (2 * r0 c + 1) + 8 := by
  have h1 := natBitLength_le_of_le_pow (show dH c ≤ 2 ^ c.f from Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
  have h2 := natBitLength_le_self S.length
  simp only [Request.data, SingleRun.request, listWord, List.length_append, natWord_length]
  rw [show RepairOrdinary.frame xs = frame xs from rfl, frame_length,
    show (S.map RepairOrdinary.frame) = S.map frame from rfl, flatten_frame_length S _ hS]
  omega

theorem bool_swap {a b : Bool} (h : a = false ↔ b = true) : b = false ↔ a = true := by
  cases a <;> cases b <;> simp_all

/-! ## `ℓ = log T + O(log log T)` -/

theorem two_pow_natBitLength_le (v : ℕ) : 2 ^ natBitLength v ≤ 2 * v + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  · have := Nat.pow_log_le_self 2 hv.ne'
    rw [pow_succ]; omega

theorem lt_two_pow_natBitLength (v : ℕ) : v < 2 ^ natBitLength v := Nat.lt_pow_succ_log_self (by norm_num) v

/-- The bound `K·2^f·f^b` of Step 2 (a) is at most `2^ℓ` for `ℓ = |bits K| + f + b·|bits f|`. -/
theorem bound_le_two_pow_ell {K f b : ℕ} : K * 2 ^ f * f ^ b ≤ 2 ^ (natBitLength K + f + b * natBitLength f) := by
  rw [pow_add, pow_add, mul_comm b, pow_mul]
  have h1 := (lt_two_pow_natBitLength K).le
  have h2 := Nat.pow_le_pow_left (lt_two_pow_natBitLength f).le b
  gcongr

/-- `2^ℓ ≤ K·t·logScale(t)^e` from `2^f ≤ K_S t L^{e_S}`, `f ≤ K_S(L + 1)` (`lem:acsp-degree`). -/
theorem two_pow_ell_le {f t ls KA bA KS eS : ℕ} (hf : f ≤ KS * (ls + 1)) (hft : 2 ^ f ≤ KS * t * ls ^ eS)
    (hls : 1 ≤ ls) :
    2 ^ (natBitLength KA + f + bA * natBitLength f) ≤
      ((2 * KA + 2) * KS * (4 * KS + 2) ^ bA) * t * ls ^ (eS + bA) := by
  have h1 := two_pow_natBitLength_le KA
  have h2 : 2 ^ natBitLength f ≤ (4 * KS + 2) * ls := (two_pow_natBitLength_le f).trans (by nlinarith)
  rw [pow_add, pow_add, mul_comm bA, pow_mul]
  calc 2 ^ natBitLength KA * 2 ^ f * (2 ^ natBitLength f) ^ bA
      ≤ (2 * KA + 2) * (KS * t * ls ^ eS) * ((4 * KS + 2) * ls) ^ bA := by gcongr
    _ = ((2 * KA + 2) * KS * (4 * KS + 2) ^ bA) * t * ls ^ (eS + bA) := by rw [mul_pow, pow_add]; ring

/-! ## The field -/

/-- **Input 6 in the ordinary model from the affine-constraint joins and the two machine hypotheses**
(`thm:short-pcp-ours` with `cor:short-pcp-clock` and "The exact Lean interface"): the construction, the four
properties, and the ordinary constructor `AssemblyMachine`. -/
theorem shortPCP_ordinary_of_joins (hS : ∀ V, AffineConstraintReduction V) (hA : AmplifiedVerifier)
    (hT : SingleRunTime) (hX : ComputationToCircuit) (hM : MaskMachine) (hP : AssemblyMachine) :
    NearCubicGates.Adapters.Assembly.OrdinaryOracleCircuitPCP := by
  intro V T hTn hRun
  obtain ⟨inst, xbar, KS, eS, hblk, hGen⟩ := hS V
  obtain ⟨K1, b1, KA, bA, -, hAmp⟩ := hA KS
  obtain ⟨prog, KT, eT, hrun⟩ := hT
  obtain ⟨KX, dX, circuit, -, hev, hsize, -, hgX⟩ := hX prog
  obtain ⟨KM, eM, hgM⟩ := hM K1 b1
  let P : Pipeline := ⟨inst, xbar, K1, b1, KT, eT, KA, bA, circuit⟩
  -- the promised requests `2 ≤ n ≤ t` and the size variable `n + natBitLength t + 1`
  let D : ClockRequest → Prop := fun r => 2 ≤ r.1.1 ∧ r.1.1 ≤ r.2
  let B : ClockRequest → ℕ := fun r => r.1.1 + natBitLength r.2 + 1
  have pB : ∀ r, D r → 1 ≤ B r := fun r _ => by simp only [B]; omega
  -- Step 1: the per-request facts
  have hG : ∀ r, D r → SingleRun.Good KS (inst r) (xbar r) := fun r hr => by
    obtain ⟨-, hV, hW, -, hlen, h1m, hmlt, hmH, -, -, hcN, -, -⟩ := hblk r hr.1 hr.2
    exact ⟨hW, hV, hlen, h1m, hmlt, hmH, hcN⟩
  have hxj : ∀ r, D r → ∃ j, xbar r = List.ofFn r.1.2 ++ true :: List.replicate j false := fun r hr => by
    obtain ⟨-, -, -, h, -⟩ := hblk r hr.1 hr.2; exact h
  have hfT : ∀ r, D r → 2 ^ (inst r).f ≤ KS * r.2 * logScale r.2 ^ eS ∧ (inst r).f ≤ KS * (logScale r.2 + 1) :=
    fun r hr => by
      obtain ⟨-, -, -, -, -, -, -, -, h1, h2, -, -, -⟩ := hblk r hr.1 hr.2; exact ⟨h1, h2⟩
  have hxb : ∀ r, D r → (xbar r).length ≤ KS * (r.1.1 + logScale r.2) := fun r hr => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hblk r hr.1 hr.2; exact h
  have hwd : ∀ r, D r → (inst r).word.length ≤ KS * (logScale r.2 + 1) ^ eS := fun r hr => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h⟩ := hblk r hr.1 hr.2; exact h
  -- Steps 2–3: the amplified verifier
  have hV1 := fun r (hr : D r) => hAmp (inst r) (xbar r) r.1.1 (hG r hr) hr.1
  have hres : ∀ r, D r → 2 ^ r0 (inst r) ≤ KA * 2 ^ (inst r).f * (inst r).f ^ bA ∧
      proofBits (inst r) ≤ KA * 2 ^ (inst r).f * (inst r).f ^ bA := fun r hr => by
    obtain ⟨-, -, -, -, -, -, -, -, h1, h2⟩ := hV1 r hr; exact ⟨h1, h2⟩
  have hr0ℓ : ∀ r, D r → r0 (inst r) ≤ P.ell r := fun r hr =>
    (Nat.pow_le_pow_iff_right (by norm_num)).mp ((hres r hr).1.trans bound_le_two_pow_ell)
  have hLℓ : ∀ r, D r → proofBits (inst r) ≤ 2 ^ P.ell r := fun r hr => (hres r hr).2.trans bound_le_two_pow_ell
  have hf3 : ∀ r, D r → 2 < (inst r).f := fun r hr => by
    have h1 := (hG r hr).mH_two_le; have h2 := (hG r hr).one_le_m; have h3 := (hG r hr).m_lt; omega
  -- Step 4: the compiled circuit is the negated verdict of `V1` on the first `r_0` seed bits
  have hiff : ∀ r (hr : D r) (O : BitInput (P.ell r) → Bool) (z : BitInput (P.ell r)),
      (P.circuit (P.compRequest r)).eval O z = false ↔
        Amplified.accepts (inst r) (xbar r) r.1.1 K1 b1 (fixedArityOracle O) (List.ofFn (pre _ (hr0ℓ r hr) z)) =
          true := by
    intro r hr O z
    obtain ⟨-, -, -, -, hcoin, -⟩ := hV1 r hr
    rw [← hcoin (fixedArityOracle O) _ _ (fun i hi => (ofFn_pre_getD (hr0ℓ r hr) z i hi).symm)]
    exact eval_false_iff hrun hev (hG r hr) r.1.1 K1 b1 (P.ell r) O z
  -- the size of the compilation request is `poly(n, log t)`
  have pLS : PolyOn D B (fun r => logScale r.2) :=
    PolyOn.base.mono fun r _ => by have := logScale_le r.2; simp only [B]; omega
  have pn : PolyOn D B (fun r => r.1.1) := PolyOn.base.mono fun r _ => by simp only [B]; omega
  have pf : PolyOn D B (fun r => (inst r).f) :=
    ((PolyOn.const KS).mul (pLS.add pB (PolyOn.const 1))).mono fun r hr => (hfT r hr).2
  have pK : PolyOn D B (fun r => KA + (inst r).f * (bA + 1)) := (PolyOn.const KA).add pB (pf.mul (PolyOn.const _))
  have pr0 : PolyOn D B (fun r => r0 (inst r)) :=
    pK.mono fun r hr => le_of_two_pow_le (hres r hr).1
  have pell : PolyOn D B (fun r => P.ell r) :=
    ((PolyOn.const (KA + 1)).add pB (pf.add pB ((PolyOn.const bA).mul (pf.add pB (PolyOn.const 1))))).mono
      fun r _ => by
        have h1 := natBitLength_le_self KA
        have h2 := Nat.mul_le_mul_left bA (natBitLength_le_self (inst r).f)
        show natBitLength KA + (inst r).f + bA * natBitLength (inst r).f ≤
          KA + 1 + ((inst r).f + bA * ((inst r).f + 1))
        omega
  have pS : PolyOn D B (fun r => (masks (inst r) r.1.1 K1 b1).length) :=
    ((PolyOn.const 4).mul ((((pr0.pow 2).mul pn).mul (PolyOn.const K1)).mul (pf.pow b1))).mono fun r hr =>
      (hV1 r hr).2.2.1.le
  have pw : PolyOn D B (fun r => (inst r).word.length) :=
    ((PolyOn.const KS).mul ((pLS.add pB (PolyOn.const 1)).pow eS)).mono fun r hr => hwd r hr
  have px : PolyOn D B (fun r => (xbar r).length) :=
    ((PolyOn.const KS).mul (pn.add pB pLS)).mono fun r hr => hxb r hr
  have pdata : PolyOn D B (fun r => (P.request r).data.length) :=
    (((((pw.add pB ((PolyOn.const 2).mul px)).add pB ((PolyOn.const 2).mul pf)).add pB
      ((PolyOn.const 2).mul pS)).add pB (pS.mul (((PolyOn.const 2).mul pr0).add pB (PolyOn.const 1)))).add pB
      (PolyOn.const 8)).mono fun r hr => data_length_le _ _ _ (hV1 r hr).2.2.2.1
  have pmeas : PolyOn D B (fun r => (P.compRequest r).measure) :=
    (((pdata.add pB pell).add pB ((PolyOn.const KT).mul (((pdata.add pB pell).add pB (PolyOn.const 1)).pow eT))).add
      pB (PolyOn.const 1)).mono fun r _ => le_rfl
  have pcirc : PolyOn D B (fun r => (P.circuit (P.compRequest r)).size) :=
    ((PolyOn.const KX).mul (pmeas.pow dX)).mono fun r _ => hsize (P.compRequest r)
  have hout2 : ∀ x : InputRequest, 2 ≤ x.1 → P.output (x, T x.1) = P.pcpOutput (x, T x.1) :=
    fun x h => if_pos h
  have hout1 : ∀ x : InputRequest, ¬ 2 ≤ x.1 → P.output (x, T x.1) = falseOutput := fun x h => if_neg h
  refine ⟨fun x => P.output (x, T x.1), ?_, ?_, ?_, ?_, ?_⟩
  · -- the ordinary constructor ("The exact Lean interface"), on the requests `(x, T(n))`
    obtain ⟨KB, eB, hKB⟩ := pmeas
    obtain ⟨K, e, ⟨W⟩⟩ := hP P KS eS KM eM KX dX KB eB hGen hgM hgX
      (fun r h2 hnt => ⟨hxj r ⟨h2, hnt⟩, r0_eq _ (hf3 r ⟨h2, hnt⟩), rfl, hKB r ⟨h2, hnt⟩,
        (hf3 r ⟨h2, hnt⟩).le, (hG r ⟨h2, hnt⟩).wellFormed.1⟩)
    let W' : OrdinaryWordFunction InputRequest
        (fun x : InputRequest => frame (List.ofFn x.2) ++ frame (T x.1).bits)
        (fun x => ((fun x : InputRequest => P.output (x, T x.1)) x).word)
        (fun x => K * ((frame (List.ofFn x.2) ++ frame (T x.1).bits).length + 1) ^ e) :=
      ⟨W.program, fun x => W.realizes ⟨(x, T x.1), hTn x.1⟩⟩
    unfold NearCubicGates.Adapters.Assembly.OrdinaryPolyTime
    exact ⟨K, e, ⟨W'⟩⟩
  · -- "ℓ = log₂ T(n) + O(log log T(n)) inputs"
    refine ⟨(2 * KA + 2) * KS * (4 * KS + 2) ^ bA + 1, eS + bA, fun x hx => ?_⟩
    have hT1 : 1 ≤ T x.1 := le_trans hx (hTn x.1)
    by_cases h2 : 2 ≤ x.1
    · have hr : D (x, T x.1) := ⟨h2, hTn x.1⟩
      show 2 ^ (P.output (x, T x.1)).ell ≤ _
      rw [hout2 x h2]
      refine (two_pow_ell_le (KA := KA) (bA := bA) (hfT _ hr).2 (hfT _ hr).1 (one_le_logScale _)).trans ?_
      gcongr
      omega
    · show 2 ^ (P.output (x, T x.1)).ell ≤ _
      rw [hout1 x h2]
      have h3 : 1 * 1 ≤ T x.1 * logScale (T x.1) ^ (eS + bA) :=
        Nat.mul_le_mul hT1 (Nat.one_le_pow (eS + bA) _ (one_le_logScale (T x.1)))
      show 1 ≤ _
      rw [mul_assoc]
      exact le_trans (by simpa using h3) (Nat.le_mul_of_pos_left _ (by omega))
  · -- "poly(n, log T(n)) size"
    obtain ⟨Kz, ez, hz⟩ := pcirc
    refine ⟨Kz + 1, ez, fun x hx => ?_⟩
    have hB1 : 1 ≤ (x.1 + natBitLength (T x.1) + 1) ^ ez := Nat.one_le_pow _ _ (by omega)
    by_cases h2 : 2 ≤ x.1
    · show (P.output (x, T x.1)).circuit.size ≤ _
      rw [hout2 x h2]
      have := hz (x, T x.1) ⟨h2, hTn x.1⟩
      exact this.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
    · show (P.output (x, T x.1)).circuit.size ≤ _
      rw [hout1 x h2]
      show 1 ≤ _
      nlinarith
  · -- completeness ("The properties of `C^O_x`")
    intro x hx hacc
    show ∃ O : BitInput (P.output (x, T x.1)).ell → Bool, ∀ z, (P.output (x, T x.1)).circuit.eval O z = false
    by_cases h2 : 2 ≤ x.1
    · have hr : D (x, T x.1) := ⟨h2, hTn x.1⟩
      rw [hout2 x h2]
      have hAcc := ((hblk (x, T x.1) hr.1 hr.2).1 (fun y => hRun x.1 x.2 y)).1 hacc
      obtain ⟨hc, -, -, -, -, hloc, -⟩ := hV1 _ hr
      obtain ⟨π, hπ⟩ := hc hAcc
      have hO : ∀ a < proofBits (inst (x, T x.1)),
          fixedArityOracle (fun w : BitInput (P.ell (x, T x.1)) => π (maskOfBits w)) a = π a :=
        fun a ha => fixedArityOracle_maskOfBits π (lt_of_lt_of_le ha (hLℓ _ hr))
      refine ⟨fun w => π (maskOfBits w), fun z => ?_⟩
      exact (hiff _ hr _ z).2 ((hloc _ π hO _).trans (hπ _))
    · rw [hout1 x h2]
      exact ⟨fun _ => false, fun z => falseCircuit_eval _ z⟩
  · -- soundness ("The properties of `C^O_x`")
    intro x hx hrej
    show ∀ O : BitInput (P.output (x, T x.1)).ell → Bool,
      (2 : ℝ) ^ (P.output (x, T x.1)).ell * (1 - 1 / (x.1 : ℝ)) ≤ ((P.output (x, T x.1)).satCount O : ℝ)
    by_cases h2 : 2 ≤ x.1
    · have hr : D (x, T x.1) := ⟨h2, hTn x.1⟩
      rw [hout2 x h2]
      intro O
      have hNA : ¬ (inst (x, T x.1)).Accepts (xbar (x, T x.1)) := fun h =>
        hrej (((hblk (x, T x.1) hr.1 hr.2).1 (fun y => hRun x.1 x.2 y)).2 h)
      have hcnt := count_reject (hr0ℓ (x, T x.1) hr)
        (fun R => Amplified.accepts (inst (x, T x.1)) (xbar (x, T x.1)) x.1 K1 b1 (fixedArityOracle O)
          (List.ofFn R)) _ ((hV1 _ hr).2.1 hNA (fixedArityOracle O))
      refine hcnt.trans (le_of_eq ?_)
      unfold OracleOutput.satCount
      congr 2
      apply Finset.filter_congr
      intro z _
      exact bool_swap (hiff _ hr O z)
    · rw [hout1 x h2]
      intro O
      have h1 : (x.1 : ℝ) = 1 := by exact_mod_cast (show x.1 = 1 by omega)
      rw [h1]
      simp

/-- The ordinary form gives the TM2 form by the polynomial-overhead simulation ("The exact Lean interface"). -/
theorem tm2_of_ordinary (hTM : OrdinaryToTM2PolyTime) (h : NearCubicGates.Adapters.Assembly.OrdinaryOracleCircuitPCP) :
    MW20_OracleCircuitPCP_TM2 := by
  intro V T hT hrun
  obtain ⟨out, ⟨K, e, hW⟩, hell, hsize, hc, hs⟩ := h V T hT hrun
  exact ⟨out, hTM _ (fun w : List Bool => w) (fun x => (out x).word) _ hW ⟨K, e, fun _ => le_rfl⟩,
    hell, hsize, hc, hs⟩

/-- **Input 6 (`MW20_OracleCircuitPCP_TM2`) from the affine-constraint joins and the two machine hypotheses.** -/
theorem shortPCP_of_joins (hS : ∀ V, AffineConstraintReduction V) (hA : AmplifiedVerifier)
    (hT : SingleRunTime) (hX : ComputationToCircuit) (hTM : OrdinaryToTM2PolyTime) (hM : MaskMachine)
    (hP : AssemblyMachine) : MW20_OracleCircuitPCP_TM2 :=
  tm2_of_ordinary hTM (shortPCP_ordinary_of_joins hS hA hT hX hM hP)

/-- **Input 6 in the ordinary model from BCGT13 Theorem 11.1**: the amplified verifier is `amplifiedVerifier`;
the theorem also assumes Step 1, the single-run time, the compiler, and the two machines. -/
theorem shortPCP_ordinary_of_leaves (h11 : BCGT13_Theorem11_1) (hS : ∀ V, AffineConstraintReduction V)
    (hT : SingleRunTime) (hX : ComputationToCircuit) (hM : MaskMachine) (hP : AssemblyMachine) :
    NearCubicGates.Adapters.Assembly.OrdinaryOracleCircuitPCP :=
  shortPCP_ordinary_of_joins hS (amplifiedVerifier h11) hT hX hM hP

/-- **Input 6 (`MW20_OracleCircuitPCP_TM2`) from BCGT13 Theorem 11.1**, with the ordinary-to-TM2 simulation proved
(`Machine.ordinaryToTM2PolyTime`). -/
theorem shortPCP_of_leaves (h11 : BCGT13_Theorem11_1) (hS : ∀ V, AffineConstraintReduction V)
    (hT : SingleRunTime) (hX : ComputationToCircuit) (hM : MaskMachine) (hP : AssemblyMachine) :
    MW20_OracleCircuitPCP_TM2 :=
  tm2_of_ordinary NearCubicGates.Adapters.Machine.ordinaryToTM2PolyTime
    (shortPCP_ordinary_of_leaves h11 hS hT hX hM hP)

end NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP
