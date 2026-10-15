import Proof.Wire_3_5.Statement
import Proof.Wire_3_5.Runtime
import Bindings.CLW20_Theorem1_13
import Proof.CaseAnalysis.Assembly
import Proof.Circuits.PolynomialOrdinaryClock
import Proof.Foundations.SupplierPipeline
import Proof.Wire_3_5.Shared.Carrier
import Proof.Wire_3_5.Shared.GapFilter

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Theorem113 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Filters

/-- One class clause of `WireExponent3_5Hard` at one multiplier, in the Theorem 2.5 vocabulary (`wireCount`,
`agreement`), which is what the Case 1 and Case 2 hardness results produce. -/
def ThrHardAt (c KT : ℝ) (language : Language) (AT : ℝ) : Prop :=
  ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n → ∀ circuit : ThresholdThresholdCircuit n,
    (circuit.wireCount : ℝ) ≤ AT * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KT →
      agreement circuit.eval (language n) < 1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c)

/-- The `SYM∘THR` clause of `WireExponent3_5Hard` at one multiplier. -/
def SymHardAt (c KS : ℝ) (language : Language) (AS : ℝ) : Prop :=
  ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n → ∀ circuit : SymmetricThresholdCircuit n,
    (circuit.wireCount : ℝ) ≤ AS * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KS →
      agreement circuit.eval (language n) < 1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c)

/-- The statement's THR wire count is the Theorem 2.5 `wireCount`. -/
theorem thr_wires_eq {n : ℕ} (circuit : ThresholdThresholdCircuit n) :
    ((∑ i : Fin circuit.bottomCount,
        if circuit.topWeight i = 0 then 0 else (circuit.bottom i).support.card + 1 : ℕ) : ℝ) =
      (circuit.wireCount : ℝ) := by
  unfold ThresholdThresholdCircuit.wireCount
  rw [Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : circuit.topWeight i = 0 <;> simp [h]

/-- The statement's SYM wire count is the Theorem 2.5 `wireCount`. -/
theorem sym_wires_eq {n : ℕ} (circuit : SymmetricThresholdCircuit n) :
    ((∑ i : Fin circuit.bottomCount, ((circuit.bottom i).support.card + 1) : ℕ) : ℝ) =
      (circuit.wireCount : ℝ) := rfl

theorem wireExponent3_5_of_parts (c KT KS : ℝ) (language : Language)
    (certificate : OrdinaryENPCertificate RecoveryOracle.correctedSat language)
    (thr : ∀ AT : ℝ, 0 < AT → ThrHardAt c KT language AT)
    (sym : ∀ AS : ℝ, 0 < AS → SymHardAt c KS language AS) :
    WireExponent3_5 c KT KS := by
  refine ⟨language, Closeout.membership language certificate, ?_⟩
  intro AT AS hAT hAS
  obtain ⟨o₁, h₁⟩ := thr AT hAT
  obtain ⟨o₂, h₂⟩ := sym AS hAS
  refine ⟨max o₁ o₂, fun n hn => ⟨fun circuit hcap => ?_, fun circuit hcap => ?_⟩⟩
  · rw [thr_wires_eq] at hcap
    exact h₁ n (le_of_max_le_left hn) circuit hcap
  · rw [sym_wires_eq] at hcap
    exact h₂ n (le_of_max_le_right hn) circuit hcap

def OneSided (M : OrdinaryWeakMachine) (L : Language) : Prop :=
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ x : BitInput n, M.accepts n x → L n x = true

theorem refuter_rejected_yes (literal : CLW20_Theorem1_13) {T : ℕ → ℕ}
    (hT : TimeConstructible T) (hR : InClockRange T) :
    ∃ L : Language, InNTIME T L ∧ ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M T → OneSided M L →
      ∃ onset : ℕ, ∀ n, onset ≤ n → ∃ x : BitInput n, L n x = true ∧ ¬ M.accepts n x := by
  obtain ⟨L, hL, _R, _d, refutes⟩ := literal T hT hR
  refine ⟨L, hL, fun M hM hone => ?_⟩
  obtain ⟨n₀, hone⟩ := hone
  obtain ⟨_C, onset, hrun⟩ := refutes M hM
  refine ⟨max onset n₀, fun n hn => ?_⟩
  obtain ⟨x, _hx, hne⟩ := hrun n (le_of_max_le_left hn)
  have hiff := (machineValue_ne_iff M n x (L n x)).mp hne
  have hrej : ¬ M.accepts n x := fun hacc => by
    have h1 := hone n (le_of_max_le_right hn) x hacc
    have h2 := hiff.mp hacc
    rw [h1] at h2
    exact Bool.noConfusion h2
  refine ⟨x, ?_, hrej⟩
  cases hLx : L n x
  · exact absurd (hiff.mpr hLx) hrej
  · rfl

theorem hierarchyClock_timeConstructible (kclk : ℕ) : TimeConstructible (fun n => n ^ (kclk + 2)) :=
  clock_timeConstructible (RepairOrdinary.PolynomialClock.ordinaryClock kclk)

/-- The hierarchy clock lies in the refuter's range `n ≤ T(n) ≤ 2^{poly(n)}`. -/
theorem hierarchyClock_inClockRange (kclk : ℕ) : InClockRange (fun n => n ^ (kclk + 2)) :=
  clock_inClockRange (RepairOrdinary.PolynomialClock.ordinaryClock kclk)

def Mode.Circuit : Mode → ℕ → Type
  | .thr, n => SupplierPipeline.NormalizedThresholdThresholdCircuit n
  | .sym, n => SupplierPipeline.NormalizedSymmetricThresholdCircuit n

/-- The circuit's function: the standard semantics of each class mode. -/
def Mode.eval {n : ℕ} : (m : Mode) → m.Circuit n → BitInput n → Bool
  | .thr, c => SupplierPipeline.NormalizedThresholdThresholdCircuit.eval c
  | .sym, c => SupplierPipeline.NormalizedSymmetricThresholdCircuit.eval c

/-- The circuit's canonical code (the Theorem 2.5 family-tagged encoding). -/
def Mode.code {n : ℕ} : (m : Mode) → m.Circuit n → ℕ
  | .thr, c => SupplierPipeline.encodeNormalizedThresholdThresholdCircuit c
  | .sym, c => SupplierPipeline.encodeNormalizedSymmetricThresholdCircuit c

def Mode.gates {n : ℕ} : (m : Mode) → m.Circuit n → Stars.Carrier n
  | .thr, c => Stars.thrGates c
  | .sym, c => Stars.symGates c

/-- The circuit's public description length (the Theorem 2.5 `descriptionBits`). -/
def Mode.descriptionBits {n : ℕ} : (m : Mode) → m.Circuit n → ℕ
  | .thr, c => SupplierPipeline.NormalizedThresholdThresholdCircuit.descriptionBits c
  | .sym, c => SupplierPipeline.NormalizedSymmetricThresholdCircuit.descriptionBits c

noncomputable def maskedMean {Seed : Type} [Fintype Seed] {n a : ℕ}
    (M : Seed → BitInput n → Bool) (C : Fin a → BitInput n → Bool) : ℝ :=
  (∑ e, ∑ x, (if M e x then (1 : ℝ) else 0) * ∏ i, (if C i x then (1 : ℝ) else 0)) /
    ((Fintype.card Seed : ℝ) * 2 ^ n)

structure PrimRequest where
  n : ℕ
  mode : Mode
  a : ℕ
  ha : a ≤ 4
  circuits : Fin a → mode.Circuit n
  carriers : List (Stars.Carrier n)
  translation : List ℕ

/-- The framed encoding of a request: the circuits and the carriers by their canonical codes, and the translation's
syndrome codes. -/
def PrimRequest.word (r : PrimRequest) : List Bool :=
  natWord r.n ++ [(match r.mode with | .thr => true | .sym => false)] ++ natWord r.a ++
    (List.ofFn fun i => natWord (r.mode.code (r.circuits i))).flatten ++
    natListWord (r.carriers.map Stars.Carrier.code) ++ natListWord r.translation

/-- The charged gates of every circuit of a request. -/
def PrimRequest.gates (req : PrimRequest) : Fin req.a → Stars.Carrier req.n :=
  fun i => req.mode.gates (req.circuits i)

def PrimRequest.gatesIn (req : PrimRequest) (named : List (Stars.Carrier req.n)) : Prop :=
  Stars.GatesIn req.gates named

/-- The printed estimate: numerator and denominator words. -/
def ratWord (q : ℚ) : List Bool := intWord q.num ++ natWord q.den

structure PrimitiveInputs {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) where
  /-- the accuracy exponent `D > 0` -/
  D : ℕ
  D_pos : 0 < D
  /-- `k ≤ polylog(n)`: `k ≤ L(n)^kDeg` -/
  kDeg : ℕ
  /-- the polynomial description envelope: each circuit has at most `(n+1)^descDeg` description bits -/
  descDeg : ℕ
  /-- each call uses at most `nameCount` names -/
  nameCount : ℕ

  carrierDeg : ℕ

  filterErrDeg : ℕ

namespace PrimitiveInputs
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

def StarAt (I : PrimitiveInputs B) (n : ℕ) : Prop :=
  Even (B.rOf n) ∧ 2 ≤ B.rOf n ∧ 4 * B.rOf n ≤ n ∧
    Nat.clog 2 (n + 2) ≤ B.kOf n ∧ B.kOf n ≤ Nat.clog 2 (n + 2) ^ I.kDeg

def starParams (I : PrimitiveInputs B) (n : ℕ) (h : I.StarAt n) : Shared.StarParams :=
  ⟨n, B.rOf n, h.1, h.2.1, h.2.2.1⟩

def filterParams (I : PrimitiveInputs B) (m : Mode) (n : ℕ) : GapParams :=
  ⟨2 * (n + 1) ^ I.carrierDeg, B.capOf m n, I.filterErrDeg * Nat.clog 2 (n + 2)⟩

abbrev Seed (I : PrimitiveInputs B) (m : Mode) (n : ℕ) : Type := GapSeed (I.filterParams m n)

open Classical in

noncomputable def mask (I : PrimitiveInputs B) (req : PrimRequest) (e : I.Seed req.mode req.n)
    (x : BitInput req.n) : Bool :=
  if h : I.StarAt req.n then
    req.carriers.all fun X => gapFilter (I.filterParams req.mode req.n) e
      (Stars.inputResidualBits (I.starParams req.n h)
        ((I.starParams req.n h).translationOfCodes req.translation) X x)
  else true

def _root_.NearCubicWires.WireExponent3_5.Cost.TimeBudget.TranslationOk (B : TimeBudget kclk E) (req : PrimRequest) :
    Prop :=
  req.translation.length = B.rOf req.n ∧ ∀ t ∈ req.translation, t < 2 ^ Nat.log 2 (req.n / B.rOf req.n + 1)

def Call (I : PrimitiveInputs B) (req : PrimRequest) : Prop :=
  req.gatesIn req.carriers ∧ (∀ X ∈ req.carriers, X.WithinEnvelope I.carrierDeg) ∧
    (∀ i, req.mode.descriptionBits (req.circuits i) ≤ (req.n + 1) ^ I.descDeg) ∧
    req.carriers.length ≤ I.nameCount ∧ B.TranslationOk req ∧ I.StarAt req.n ∧ B.FitsAt req.n

noncomputable def truth (I : PrimitiveInputs B) (req : PrimRequest) : ℝ :=
  maskedMean (Seed := I.Seed req.mode req.n) (I.mask req) (fun i => req.mode.eval (req.circuits i))

end PrimitiveInputs

structure FusedPrimitive {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B) where
  /-- the printed estimate -/
  value : PrimRequest → ℚ
  /-- one program printing `value` within the per-call budget, on every call meeting the precondition -/
  estimator : OrdinaryWordFunction {req : PrimRequest // I.Call req} (fun req => req.1.word)
    (fun req => ratWord (value req.1)) (fun req => B.callBudget req.1.n)
  /-- error `n^{−D}` against the caller's masked mean, for every call meeting the precondition -/
  error : ∀ req, I.Call req → |(value req : ℝ) - I.truth req| ≤ (req.n : ℝ) ^ (-(I.D : ℝ))

structure UnionConstruction {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B) where
  build : FusedPrimitive I → Language → OrdinaryWeakMachine

  soundness : ∀ (P : FusedPrimitive I) (L : Language), InNTIME (fun n => n ^ (kclk + 2)) L →
    OneSided (build P L) L

  time : ∀ (P : FusedPrimitive I) (L : Language), B.Split (build P L)

/-- The built machine's `Runtime3`: the ledger with the machine's split. -/
def UnionConstruction.runtime3 {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
    (U : UnionConstruction I) (P : FusedPrimitive I) (L : Language) :
    Runtime3 (U.build P L) kclk E :=
  { B with split := U.time P L }

structure Recovery {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
    (U : UnionConstruction I) (P : FusedPrimitive I) where
  language : Language → Language
  certificate : ∀ L, OrdinaryENPCertificate RecoveryOracle.correctedSat (language L)
  thr : ∀ L, InNTIME (fun n => n ^ (kclk + 2)) L →
    (∃ onset : ℕ, ∀ n, onset ≤ n → ∃ x : BitInput n, L n x = true ∧ ¬ (U.build P L).accepts n x) →
      ∀ AT : ℝ, 0 < AT → ThrHardAt (1 / 8) (11 / 2) (language L) AT
  sym : ∀ L, InNTIME (fun n => n ^ (kclk + 2)) L →
    (∃ onset : ℕ, ∀ n, onset ≤ n → ∃ x : BitInput n, L n x = true ∧ ¬ (U.build P L).accepts n x) →
      ∀ AS : ℝ, 0 < AS → SymHardAt (1 / 8) (9 / 2) (language L) AS

theorem rowB_of_fused (literals : Literals) {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
    {I : PrimitiveInputs B} (U : UnionConstruction I) (P : FusedPrimitive I) (D : Recovery U P) : rowB := by
  obtain ⟨L, hL, refuted⟩ := refuter_rejected_yes literals.clw113
    (hierarchyClock_timeConstructible kclk) (hierarchyClock_inClockRange kclk)
  have hrej := refuted (U.build P L) (U.runtime3 P L).littleO (U.soundness P L hL)
  exact wireExponent3_5_of_parts (1 / 8) (11 / 2) (9 / 2) (D.language L) (D.certificate L)
    (D.thr L hL hrej) (D.sym L hL hrej)

/-! ## The one open part -/

/-- The premises of `rowB_of_fused`, fused: the time ledger (with its clock exponent and envelope), the
primitive's caller inputs, the union construction, the primitive at those inputs, and the recovery obligations for
the machine built from that primitive. -/
structure Parts where
  kclk : ℕ
  envelope : Envelope
  budget : TimeBudget kclk envelope
  inputs : PrimitiveInputs budget
  union : UnionConstruction inputs
  primitive : FusedPrimitive inputs
  recovery : Recovery union primitive

/-- Row B from the nine literals and one `Parts`. -/
theorem rowB_of_parts (literals : Literals) (parts : Parts) : rowB :=
  rowB_of_fused literals parts.union parts.primitive parts.recovery

theorem literals_rowB_of_parts (parts : Literals → Parts) : Literals → rowB :=
  fun literals => rowB_of_parts literals (parts literals)

end NearCubicWires.WireExponent3_5
