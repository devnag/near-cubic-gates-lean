import Proof.Gates.Recovery.AfterProg

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-- The graph's configuration entering piece `k` on the ambient tapes `A`. -/
noncomputable def start (K : Kit s P g) (c : Cfg) (k : Fin 31) (A : Fin (T K) → List Bool) : (prog K c).Config :=
  controlConfig (RecoveryCalls.code (fun j => (pieces K c j).states) k) (initialConfiguration (pieces K c k).machine A)

/-- The graph's stopped configuration with the tapes `A` (every head at `0`). -/
noncomputable def stopAt (K : Kit s P g) (c : Cfg) (A : Fin (T K) → List Bool) : (prog K c).Config :=
  RecoveryCalls.stopped (fun j => (pieces K c j).states) (fun _ => 0) A

end

/-- A live source index for the final length `n` (what `Recovery.AfterRun.run` grants, with the cutoff read as the
succinct verifier's onset). -/
structure Live (s : GateSources) (g : GateParams) (n ν : ℕ) : Prop where
  pos : 1 ≤ ν
  arity : g.coreArity s ν ≤ n / 2
  onset : (g.sv s).onset ≤ ν
  amp : 1 ≤ g.ampFactor
  ampLarge : (selectedAmplifier s.amplification g.degree).arityCoefficient ≤ g.ampFactor

/-- At a live index, `ν < q ≤ m(q) ≤ n/2` (`K_amp ≥ 1`). -/
theorem Live.width_le {s : GateSources} {g : GateParams} {n ν : ℕ} (h : Live s g n ν) :
    ν < g.width s ν ∧ g.width s ν ≤ g.coreArity s ν ∧ g.coreArity s ν ≤ n / 2 := by
  refine ⟨g.nu_lt_width s ν, ?_, h.arity⟩
  unfold GateParams.coreArity GateParams.tableArity
  have := h.amp
  nlinarith

/-- `StageBudget d` at the capacity parameters `(A, B)` and the cost constants `(C, E)`. -/
def StageBudgetAt (d A B C E : ℕ) : Prop :=
  ∀ (n w R : ℕ) (vals : List Bool) (hw : w ≤ R) {m : ℕ} (x : BitInput m),
    R ≤ n → vals.length = 2 ^ w →
    originalWorkspace R (oracleSizeBound d R) vals.length vals.length ≤ CloseoutCapacity.capacity A B n ∧
    (DedupBytes.fields (ENP.unitPCP w vals)).length ≤ CloseoutCapacity.capacity A B n ∧
    2 ^ R ≤ CloseoutCapacity.capacity A B n ∧
    (0 < oracleSizeBound d R →
      ENP.UStage.cost d w R (CloseoutCapacity.capacity A B n) vals hw x ≤ C * (2 ^ n + 1) ^ E)

/-- **The tail after stage 2** (paper §11.6, stage 3 and the two last branches): entering piece 24 (the copies of
`frame O*`) with stage 2's table `O*` on its table tape and the words of the preparation on the shared tapes, the
program stops with the gate core's bit on the output tape, within `C (2^n + 1)^E`. -/
def TailRuns {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg) : Prop :=
  ∀ C0 E0 : ℕ, StageBudgetAt g.degree c.A c.B C0 E0 →
  ∃ C E : ℕ, ∀ (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)) (A : Fin (T K) → List Bool)
    (h1 : g.SrcExists s ν z) (h2 : ∃ t, HonestTable (g.outC s ν (g.firstSrc s ν z h1)).circuit t),
    Live s g n ν → K.ht.cutoff ≤ 2 ^ ν →
    A (tbl K) = RepairOrdinary.frame (List.ofFn (Classical.choice (existsFirstTable _ h2)).table) →
    A (sh K 1) = RepairOrdinary.frame (List.ofFn point) →
    (A (sh K 3)).length ≤ CloseoutCapacity.capacity c.Aq c.Bq n →
    A (sh K 9) = List.replicate ν true →
    A (sh K 10) = List.replicate (g.width s ν) true →
    A (sh K 11) = List.replicate (CloseoutCapacity.capacity c.A c.B n) true →
    A (sh K 12) = List.replicate (g.width s ν) true →
    A (sh K 13) = List.replicate (g.bound s ν) true →
    A (sh K 15) = List.replicate (CloseoutCapacity.capacity c.Aq c.Bq n) true →
    A (sh K 17) = PCPPNative.descriptor (g.firstSrc s ν z h1) →
    A (sh K 2) = [] → A (sh K 21) = [] → A (sh K 22) = [] → A (sh K 23) = [] → A (sh K 24) = [] →
    A (sh K 31) = [] →
    (∀ x : Fin (T K), off K 24 ≤ x.val → A x = []) →
    ∃ cost, cost ≤ C * (2 ^ n + 1) ^ E ∧ ∃ B : Fin (T K) → List Bool,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 24 A) (stopAt K c B) ∧
      B (sh K 2) = RepairOrdinary.frame (g.gateCore s P (selectedAmplifier s.amplification g.degree) ν z
        (CloseoutLanguage.clauseWidth g.clauseDegree (g.width s ν)) g.positionLog n point).toNat.bits

def QFits {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg) : Prop :=
  ∀ n ν : ℕ, Live s g n ν →
    K.ts.K * (2 ^ g.width s ν + (39 * (g.width s ν + g.bound s ν + 5) ^ 2 + ν +
      (aR s g).K * (ν + 1) ^ (aR s g).e) + 1) ^ K.ts.e ≤ CloseoutCapacity.capacity c.Aq c.Bq n

def MidRuns {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg) : Prop :=
  QFits K c →
  ∃ C E : ℕ, ∀ (n : ℕ) (ν : ℕ) (z : BitInput (2 ^ ν)) (A : Fin (T K) → List Bool) (h1 : g.SrcExists s ν z),
    Live s g n ν →
    A (sh K 14) = RepairOrdinary.frame
      (OuterPCPRecovery.canonicalBoundedCircuitDescription (g.bound s ν) (g.firstSrc s ν z h1)) →
    (A (sh K 3)).length ≤ CloseoutCapacity.capacity c.Aq c.Bq n →
    A (sh K 15) = List.replicate (CloseoutCapacity.capacity c.Aq c.Bq n) true →
    A (sh K 7) = List.replicate (g.width s ν) true →
    A (sh K 8) = List.replicate (g.bound s ν) true →
    A (sh K 9) = List.replicate ν true →
    A (sh K 16) = [] → A (sh K 17) = [] → A (sh K 18) = [] →
    (∀ x : Fin (T K), off K 18 ≤ x.val → A x = []) →
    ∃ cost, cost ≤ C * (2 ^ n + 1) ^ E ∧ ∃ A' : Fin (T K) → List Bool,
      (∀ i : Fin 32, i ∉ [3, 7, 8, 16, 17, 18] → A' (sh K i) = A (sh K i)) ∧
      A' (sh K 17) = PCPPNative.descriptor (g.firstSrc s ν z h1) ∧
      (A' (sh K 3)).length ≤ CloseoutCapacity.capacity c.Aq c.Bq n ∧
      (∀ x : Fin (T K), off K 23 ≤ x.val → A' x = []) ∧
      (∀ h2 : ∃ t, HonestTable (g.outC s ν (g.firstSrc s ν z h1)).circuit t,
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 18 A) (start K c 24 A') ∧
        A' (tbl K) = RepairOrdinary.frame (List.ofFn (Classical.choice (existsFirstTable _ h2)).table)) ∧
      ((¬ ∃ t, HonestTable (g.outC s ν (g.firstSrc s ν z h1)).circuit t) →
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 18 A) (start K c 23 A'))

/-- The after-prefix program's entry bank: `frame z ++ post` on shared `0`, `frame point` on shared `1`. -/
noncomputable def entry {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) {n ν : ℕ}
    (point : BitInput n) (z : BitInput (2 ^ ν)) (post : List Bool) : Fin (T K) → List Bool :=
  afterBank (sh K 0) (sh K 1) (RepairOrdinary.frame (List.ofFn z) ++ post) (RepairOrdinary.frame (List.ofFn point))

def HeadRuns {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg) : Prop :=
  ∀ C0 E0 : ℕ, StageBudgetAt g.degree c.A c.B C0 E0 →
  ∃ C E : ℕ, ∀ (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)) (post : List Bool),
    Live s g n ν →
    ∃ cost, cost ≤ C * (2 ^ n + 1) ^ E ∧ ∃ A' : Fin (T K) → List Bool,
      A' (sh K 0) = RepairOrdinary.frame (List.ofFn z) ++ post ∧
      A' (sh K 1) = RepairOrdinary.frame (List.ofFn point) ∧
      A' (sh K 2) = [] ∧
      (A' (sh K 3)).length ≤ C0 * (2 ^ n + 1) ^ E0 ∧
      A' (sh K 7) = List.replicate (g.width s ν) true ∧
      A' (sh K 8) = List.replicate (g.bound s ν) true ∧
      A' (sh K 9) = List.replicate ν true ∧
      A' (sh K 10) = List.replicate (g.width s ν) true ∧
      A' (sh K 11) = List.replicate (CloseoutCapacity.capacity c.A c.B n) true ∧
      A' (sh K 12) = List.replicate (g.width s ν) true ∧
      A' (sh K 13) = List.replicate (g.bound s ν) true ∧
      A' (sh K 15) = List.replicate (CloseoutCapacity.capacity c.Aq c.Bq n) true ∧
      A' (sh K 16) = [] ∧ A' (sh K 17) = [] ∧ A' (sh K 18) = [] ∧ A' (sh K 21) = [] ∧ A' (sh K 22) = [] ∧
      A' (sh K 23) = [] ∧ A' (sh K 24) = [] ∧ A' (sh K 31) = [] ∧
      (∀ x : Fin (T K), off K 17 ≤ x.val → A' x = []) ∧
      (∀ h1 : g.SrcExists s ν z,
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 0 (entry K point z post))
          (start K c 18 A') ∧
        A' (sh K 14) = RepairOrdinary.frame
          (OuterPCPRecovery.canonicalBoundedCircuitDescription (g.bound s ν) (g.firstSrc s ν z h1))) ∧
      (¬ g.SrcExists s ν z →
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 0 (entry K point z post))
          (start K c 17 A'))

def HeadTwoRuns {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (K : Kit s P g) (c : Cfg) : Prop :=
  ∀ C0 E0 : ℕ, StageBudgetAt g.degree c.A c.B C0 E0 →
  ∃ C E : ℕ, ∀ (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)) (post : List Bool)
    (A : Fin (T K) → List Bool), Live s g n ν →
    A (sh K 0) = RepairOrdinary.frame (List.ofFn z) ++ post →
    A (sh K 1) = RepairOrdinary.frame (List.ofFn point) →
    A (sh K 4) = RepairOrdinary.frame (List.ofFn z) →
    A (sh K 5) = List.replicate (g.width s ν) true →
    A (sh K 7) = List.replicate (g.width s ν) true →
    A (sh K 9) = List.replicate ν true →
    A (sh K 10) = List.replicate (g.width s ν) true →
    A (sh K 12) = List.replicate (g.width s ν) true →
    (∀ i : Fin 32, i ∈ [2, 3, 6, 8, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 31] → A (sh K i) = []) →
    (∀ x : Fin (T K), off K 11 ≤ x.val → A x = []) →
    ∃ cost, cost ≤ C * (2 ^ n + 1) ^ E ∧ ∃ A' : Fin (T K) → List Bool,
      A' (sh K 0) = RepairOrdinary.frame (List.ofFn z) ++ post ∧
      A' (sh K 1) = RepairOrdinary.frame (List.ofFn point) ∧
      A' (sh K 2) = [] ∧
      (A' (sh K 3)).length ≤ C0 * (2 ^ n + 1) ^ E0 ∧
      A' (sh K 7) = List.replicate (g.width s ν) true ∧
      A' (sh K 8) = List.replicate (g.bound s ν) true ∧
      A' (sh K 9) = List.replicate ν true ∧
      A' (sh K 10) = List.replicate (g.width s ν) true ∧
      A' (sh K 11) = List.replicate (CloseoutCapacity.capacity c.A c.B n) true ∧
      A' (sh K 12) = List.replicate (g.width s ν) true ∧
      A' (sh K 13) = List.replicate (g.bound s ν) true ∧
      A' (sh K 15) = List.replicate (CloseoutCapacity.capacity c.Aq c.Bq n) true ∧
      A' (sh K 16) = [] ∧ A' (sh K 17) = [] ∧ A' (sh K 18) = [] ∧ A' (sh K 21) = [] ∧ A' (sh K 22) = [] ∧
      A' (sh K 23) = [] ∧ A' (sh K 24) = [] ∧ A' (sh K 31) = [] ∧
      (∀ x : Fin (T K), off K 17 ≤ x.val → A' x = []) ∧
      (∀ h1 : g.SrcExists s ν z,
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 11 A) (start K c 18 A') ∧
        A' (sh K 14) = RepairOrdinary.frame
          (OuterPCPRecovery.canonicalBoundedCircuitDescription (g.bound s ν) (g.firstSrc s ν z h1))) ∧
      (¬ g.SrcExists s ν z →
        OrdinaryOracleTrace RecoveryOracle.correctedSat (prog K c) cost (start K c 11 A) (start K c 17 A'))

end NearCubicGates.Close.Recovery.After
