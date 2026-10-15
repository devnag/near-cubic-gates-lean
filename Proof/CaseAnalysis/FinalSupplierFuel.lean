import Proof.CaseAnalysis.FinalRuntimeBridge
import Proof.CaseAnalysis.FinalStageSeam
import Proof.CaseAnalysis.FinalTailCompose

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierFuel

open SelectedRecoveryIntegration SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain (workerBudget)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam (stagedFuel dockedFuel)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose (bodyThreeFuel)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. Arithmetic: constants and the single residual factor -/

/-- A constant is absorbed by a power of any base at least two.  This is what lets a
coefficient move into the exponent `c` of `(q+1)^c` without a new constant. -/
theorem const_le_pow (B : ℕ) (hB : 2 ≤ B) : ∀ m : ℕ, m ≤ B ^ m := by
  intro m
  induction m with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h1 : 1 ≤ B ^ n := Nat.one_le_pow _ _ (by omega)
    calc n + 1 ≤ B ^ n + B ^ n := by omega
      _ = 2 * B ^ n := by ring
      _ ≤ B * B ^ n := Nat.mul_le_mul hB (Nat.le_refl _)
      _ = B ^ (n + 1) := by rw [pow_succ]; ring

/-- The exponent arithmetic of A.8:2307, with every product an opaque atom. -/
theorem sub_exp_le {w a b d L : ℕ} (haw : a ≤ w) (h : b + d + 2 * L ≤ a) :
    2 * L + (w - a) + d ≤ w - b := by omega

/-- **Paper A.8:2298-2301 and A.8:2307.**  `m` copies of one residual table factor
`2 ^ (q - kappa * L_q)` times a fixed power `(q+1)^c` of the residual arity still fit
under the single damped factor `2 ^ (q - sigma * L_q)`, provided
`sigma + c + 2 <= kappa` (A.8:2307) and `m <= 2 ^ (2 * L_q)`.
There is exactly ONE residual factor on either side. -/
theorem hot_absorb {w L kappa sigma c m : ℕ}
    (hlog : w + 1 ≤ 2 ^ L) (hfit : kappa * L ≤ w)
    (hslack : sigma + c + 2 ≤ kappa) (hm : m ≤ 2 ^ (2 * L)) :
    m * (2 ^ (w - kappa * L) * (w + 1) ^ c) ≤ 2 ^ (w - sigma * L) := by
  have hpow : (w + 1) ^ c ≤ 2 ^ (c * L) := by
    calc (w + 1) ^ c ≤ (2 ^ L) ^ c := Nat.pow_le_pow_left hlog c
      _ = 2 ^ (L * c) := (pow_mul 2 L c).symm
      _ = 2 ^ (c * L) := by rw [Nat.mul_comm]
  have hmul : sigma * L + c * L + 2 * L ≤ kappa * L := by
    calc sigma * L + c * L + 2 * L = (sigma + c + 2) * L := by ring
      _ ≤ kappa * L := Nat.mul_le_mul hslack (Nat.le_refl L)
  have hexp : 2 * L + (w - kappa * L) + c * L ≤ w - sigma * L :=
    sub_exp_le hfit hmul
  calc m * (2 ^ (w - kappa * L) * (w + 1) ^ c)
      ≤ 2 ^ (2 * L) * (2 ^ (w - kappa * L) * 2 ^ (c * L)) :=
        Nat.mul_le_mul hm (Nat.mul_le_mul (Nat.le_refl _) hpow)
    _ = 2 ^ (2 * L + (w - kappa * L) + c * L) := by
        rw [pow_add, pow_add, mul_assoc]
    _ ≤ 2 ^ (w - sigma * L) := Nat.pow_le_pow_right (by norm_num) hexp

/-! ## 2. The supplier stage's fuel (paper A.8:2249-2307) -/

def stageExponent (driverCoeff driverExp tableCoeff tableExp rowExp : ℕ) : ℕ :=
  max (driverCoeff + driverExp) (max (rowExp + tableExp + tableCoeff) 2) + 2

theorem stageFuel_core
    (width logWidth : ℕ → ℕ) (stageFuel driver rowCount rowFuel : Phase → ℕ → ℕ)
    (kappa driverCoeff driverExp tableCoeff tableExp rowExp onset : ℕ)
    (hwidth : ∀ N, onset ≤ N → 1 ≤ width N)
    (hsplit : ∀ ph N, onset ≤ N →
      stageFuel ph N ≤ driver ph N + rowCount ph N * rowFuel ph N)
    (hdriver : ∀ ph N, onset ≤ N → driver ph N ≤ driverCoeff * (width N + 1) ^ driverExp)
    (hrows : ∀ ph N, onset ≤ N → rowCount ph N ≤ (width N + 1) ^ rowExp)
    (hrow : ∀ ph N, onset ≤ N → rowFuel ph N ≤
      tableCoeff * (2 ^ (width N - kappa * logWidth N) * (width N + 1) ^ tableExp))
    (ph : Phase) (N : ℕ) (hN : onset ≤ N) :
    stageFuel ph N + 2 ≤ 2 ^ (width N - kappa * logWidth N) *
      (width N + 1) ^ stageExponent driverCoeff driverExp tableCoeff tableExp rowExp := by
  have hB : 2 ≤ width N + 1 := by have := hwidth N hN; omega
  have hone : 1 ≤ width N + 1 := by omega
  have hh : 1 ≤ 2 ^ (width N - kappa * logWidth N) := Nat.one_le_pow _ _ (by norm_num)
  set B := width N + 1 with hBval
  set h := 2 ^ (width N - kappa * logWidth N) with hhval
  set M := max (driverCoeff + driverExp) (max (rowExp + tableExp + tableCoeff) 2) with hMval
  -- the driver's summand
  have hd1 : driver ph N ≤ B ^ (driverCoeff + driverExp) := by
    calc driver ph N ≤ driverCoeff * B ^ driverExp := hdriver ph N hN
      _ ≤ B ^ driverCoeff * B ^ driverExp :=
        Nat.mul_le_mul (const_le_pow B hB driverCoeff) (Nat.le_refl _)
      _ = B ^ (driverCoeff + driverExp) := by rw [pow_add]
  have hd2 : driver ph N ≤ h * B ^ M := by
    calc driver ph N ≤ B ^ (driverCoeff + driverExp) := hd1
      _ ≤ B ^ M := Nat.pow_le_pow_right hone (le_max_left _ _)
      _ ≤ h * B ^ M := Nat.le_mul_of_pos_left _ hh
  -- the external-row loop's summand
  have hr1 : rowCount ph N * rowFuel ph N ≤ h * B ^ (rowExp + tableExp + tableCoeff) := by
    calc rowCount ph N * rowFuel ph N
        ≤ B ^ rowExp * (tableCoeff * (h * B ^ tableExp)) :=
          Nat.mul_le_mul (hrows ph N hN) (hrow ph N hN)
      _ ≤ B ^ rowExp * (B ^ tableCoeff * (h * B ^ tableExp)) :=
          Nat.mul_le_mul (Nat.le_refl _)
            (Nat.mul_le_mul (const_le_pow B hB tableCoeff) (Nat.le_refl _))
      _ = h * B ^ (rowExp + tableExp + tableCoeff) := by ring
  have hr2 : rowCount ph N * rowFuel ph N ≤ h * B ^ M := by
    calc rowCount ph N * rowFuel ph N ≤ h * B ^ (rowExp + tableExp + tableCoeff) := hr1
      _ ≤ h * B ^ M := Nat.mul_le_mul (Nat.le_refl _)
          (Nat.pow_le_pow_right hone (le_trans (le_max_left _ _) (le_max_right _ _)))

  have ht2 : 2 ≤ h * B ^ M := by
    have h4 : (2 : ℕ) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hB 2
    have h5 : B ^ 2 ≤ B ^ M :=
      Nat.pow_le_pow_right hone (le_trans (le_max_right _ _) (le_max_right _ _))
    have h6 : B ^ M ≤ h * B ^ M := Nat.le_mul_of_pos_left _ hh
    have h7 : (4 : ℕ) ≤ (2 : ℕ) ^ 2 := by norm_num
    omega
  -- three summands, absorbed by `3 <= B ^ 2`
  have hthree : (3 : ℕ) ≤ B ^ 2 := by
    have h4 : (2 : ℕ) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hB 2
    have h7 : (4 : ℕ) = (2 : ℕ) ^ 2 := by norm_num
    omega
  calc stageFuel ph N + 2 ≤ (driver ph N + rowCount ph N * rowFuel ph N) + 2 := by
        have := hsplit ph N hN; omega
    _ ≤ 3 * (h * B ^ M) := by omega
    _ ≤ B ^ 2 * (h * B ^ M) := Nat.mul_le_mul hthree (Nat.le_refl _)
    _ = h * B ^ (M + 2) := by ring

/-- **`stageFuel_le` (P2R section 2.3), the existential headline.**  Per phase, the
supplier stage's fuel is one table factor times a fixed power of `q` (A.8:2259-2263),
plus `T_prep` (A.8:2275-2296), which A.8:2298-2301 places in the same bucket.
Stated at the machine's input length `N` with `q := width N`, because that is the
index `Runtime.hpoly` quantifies over; taking `width := id` is P2R's literal form. -/
theorem stageFuel_le
    (width logWidth : ℕ → ℕ) (stageFuel driver rowCount rowFuel : Phase → ℕ → ℕ)
    (kappa driverCoeff driverExp tableCoeff tableExp rowExp onset : ℕ)
    (hwidth : ∀ N, onset ≤ N → 1 ≤ width N)
    (hsplit : ∀ ph N, onset ≤ N →
      stageFuel ph N ≤ driver ph N + rowCount ph N * rowFuel ph N)
    (hdriver : ∀ ph N, onset ≤ N → driver ph N ≤ driverCoeff * (width N + 1) ^ driverExp)
    (hrows : ∀ ph N, onset ≤ N → rowCount ph N ≤ (width N + 1) ^ rowExp)
    (hrow : ∀ ph N, onset ≤ N → rowFuel ph N ≤
      tableCoeff * (2 ^ (width N - kappa * logWidth N) * (width N + 1) ^ tableExp))
    (ph : Phase) :
    ∃ stageOnset c : ℕ, ∀ N, stageOnset ≤ N →
      stageFuel ph N + 2 ≤ 2 ^ (width N - kappa * logWidth N) * (width N + 1) ^ c :=
  ⟨onset, stageExponent driverCoeff driverExp tableCoeff tableExp rowExp,
    fun N hN => stageFuel_core width logWidth stageFuel driver rowCount rowFuel kappa
      driverCoeff driverExp tableCoeff tableExp rowExp onset hwidth hsplit hdriver hrows
      hrow ph N hN⟩

/-! ## 3. The A.8 split of the composed worker budget -/

/-- `Fmaj` of `Proof/CaseAnalysis/FinalTailCompose.lean`, as a function of the input
length, at the per-phase supplier stage.  `tailBudget n` is `tbud (Wmax n)` of the
decision tail; `entryWidth n` and `callCap n` are the record width and the len-only
call-count cap (`phaseRecords_length_le` / `staged_le_majorant`). -/
def budgetOf (onset : ℕ) (stageFuel : Phase → ℕ → ℕ)
    (emitFuel entryWidth callCap tailBudget : ℕ → ℕ) : ℕ → ℕ :=
  fun n => workerBudget onset
    (fun _ => bodyThreeFuel
        (fun ph => stagedFuel (stageFuel ph) emitFuel (entryWidth n) (callCap n) n)
      + 1 + (2 * tailBudget n + 2)) n

/-- Every summand of `Fmaj`, expanded.  The three phase fuels occur with coefficient
`2` each (`bodyThreeFuel`), hence SIX copies of the supplier stage. -/
theorem budgetOf_eq (onset : ℕ) (stageFuel : Phase → ℕ → ℕ)
    (emitFuel entryWidth callCap tailBudget : ℕ → ℕ) (n : ℕ) :
    budgetOf onset stageFuel emitFuel entryWidth callCap tailBudget n + 2
      = 2 * (stageFuel Phase.penalty n + stageFuel Phase.moment n + stageFuel Phase.clause n)
        + (6 * dockedFuel emitFuel (entryWidth n) (callCap n) n
            + 2 * tailBudget n + (4 * onset + 32)) := by
  simp only [budgetOf, workerBudget, bodyThreeFuel, stagedFuel]
  omega

theorem budget_core
    (width logWidth : ℕ → ℕ) (stageFuel : Phase → ℕ → ℕ)
    (emitFuel entryWidth callCap tailBudget : ℕ → ℕ)
    (onset A a sigma kappa c : ℕ)
    (hslack : sigma + c + 2 ≤ kappa)
    (hlog : ∀ N, onset ≤ N → width N + 1 ≤ 2 ^ logWidth N)
    (hfit : ∀ N, onset ≤ N → kappa * logWidth N ≤ width N)
    (hlogTwo : ∀ N, onset ≤ N → 2 ≤ logWidth N)
    (hstage : ∀ ph N, onset ≤ N →
      stageFuel ph N + 2 ≤ 2 ^ (width N - kappa * logWidth N) * (width N + 1) ^ c)
    (hrest : ∀ N, onset ≤ N →
      dockedFuel emitFuel (entryWidth N) (callCap N) N + tailBudget N ≤ A * (N + 1) ^ a)
    (N : ℕ) (hN : onset ≤ N) :
    budgetOf onset stageFuel emitFuel entryWidth callCap tailBudget N + 2
      ≤ (8 * A + 4 * onset + 32) * (N + 1) ^ a + hotOf sigma width logWidth N := by
  have hsum : 2 * (stageFuel Phase.penalty N + stageFuel Phase.moment N
      + stageFuel Phase.clause N)
      ≤ 6 * (2 ^ (width N - kappa * logWidth N) * (width N + 1) ^ c) := by
    have h1 := hstage Phase.penalty N hN
    have h2 := hstage Phase.moment N hN
    have h3 := hstage Phase.clause N hN
    omega
  have hm : (6 : ℕ) ≤ 2 ^ (2 * logWidth N) := by
    have h4 : (4 : ℕ) ≤ 2 * logWidth N := by have := hlogTwo N hN; omega
    calc (6 : ℕ) ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * logWidth N) := Nat.pow_le_pow_right (by norm_num) h4
  have hhot : 2 * (stageFuel Phase.penalty N + stageFuel Phase.moment N
      + stageFuel Phase.clause N) ≤ hotOf sigma width logWidth N :=
    le_trans hsum (hot_absorb (hlog N hN) (hfit N hN) hslack hm)
  have hpow1 : 1 ≤ (N + 1) ^ a := Nat.one_le_pow _ _ (by omega)
  have hd := hrest N hN
  have hpoly : 6 * dockedFuel emitFuel (entryWidth N) (callCap N) N
      + 2 * tailBudget N + (4 * onset + 32) ≤ (8 * A + 4 * onset + 32) * (N + 1) ^ a := by
    have h8 : 8 * (A * (N + 1) ^ a) + (4 * onset + 32) * 1
        ≤ 8 * (A * (N + 1) ^ a) + (4 * onset + 32) * (N + 1) ^ a :=
      Nat.add_le_add (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_refl _) hpow1)
    have h9 : (8 * A + 4 * onset + 32) * (N + 1) ^ a
        = 8 * (A * (N + 1) ^ a) + (4 * onset + 32) * (N + 1) ^ a := by ring
    omega
  rw [budgetOf_eq]
  exact le_trans (Nat.add_le_add hhot hpoly) (Nat.le_of_eq (Nat.add_comm _ _))

theorem budget_split (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2)))
    (logWidth : ℕ → ℕ) (stageFuel : Phase → ℕ → ℕ)
    (emitFuel entryWidth callCap tailBudget : ℕ → ℕ)
    (onset A a sigma kappa c : ℕ)
    (ha : a ≤ k + 1)
    (hslack : sigma + c + 2 ≤ kappa)
    (hlog : ∀ N, onset ≤ N →
      (outer sources k clock).result.pcp.nativeWidth N + 1 ≤ 2 ^ logWidth N)
    (hfit : ∀ N, onset ≤ N →
      kappa * logWidth N ≤ (outer sources k clock).result.pcp.nativeWidth N)
    (hlogTwo : ∀ N, onset ≤ N → 2 ≤ logWidth N)
    (hstage : ∀ ph N, onset ≤ N → stageFuel ph N + 2 ≤
      2 ^ ((outer sources k clock).result.pcp.nativeWidth N - kappa * logWidth N)
        * ((outer sources k clock).result.pcp.nativeWidth N + 1) ^ c)
    (hrest : ∀ N, onset ≤ N →
      dockedFuel emitFuel (entryWidth N) (callCap N) N + tailBudget N ≤ A * (N + 1) ^ a) :
    ∃ splitOnset A' a' : ℕ, a' ≤ k + 1 ∧ ∀ N, splitOnset ≤ N →
      budgetOf onset stageFuel emitFuel entryWidth callCap tailBudget N + 2
        ≤ A' * (N + 1) ^ a'
          + hotOf sigma (fun N => (outer sources k clock).result.pcp.nativeWidth N)
              logWidth N :=
  ⟨onset, 8 * A + 4 * onset + 32, a, ha,
    fun N hN => budget_core (fun N => (outer sources k clock).result.pcp.nativeWidth N)
      logWidth stageFuel emitFuel entryWidth callCap tailBudget onset A a sigma kappa c
      hslack hlog hfit hlogTwo hstage hrest N hN⟩

noncomputable def runtime_of_supplierFuel (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2)))
    (logWidth : ℕ → ℕ) (stageFuel : Phase → ℕ → ℕ)
    (emitFuel entryWidth callCap tailBudget : ℕ → ℕ)
    (onset A a sigma kappa c : ℕ)
    (ha : a ≤ k + 1)
    (hsigma : 6 + (fixedProjection sources).degrees.proofLog ≤ sigma)
    (hslack : sigma + c + 2 ≤ kappa)
    (hlog : ∀ N, onset ≤ N →
      (outer sources k clock).result.pcp.nativeWidth N + 1 ≤ 2 ^ logWidth N)
    (hfit : ∀ N, onset ≤ N →
      kappa * logWidth N ≤ (outer sources k clock).result.pcp.nativeWidth N)
    (hlogTwo : ∀ N, onset ≤ N → 2 ≤ logWidth N)
    (hstage : ∀ ph N, onset ≤ N → stageFuel ph N + 2 ≤
      2 ^ ((outer sources k clock).result.pcp.nativeWidth N - kappa * logWidth N)
        * ((outer sources k clock).result.pcp.nativeWidth N + 1) ^ c)
    (hrest : ∀ N, onset ≤ N →
      dockedFuel emitFuel (entryWidth N) (callCap N) N + tailBudget N ≤ A * (N + 1) ^ a) :
    Runtime sources k clock (budgetOf onset stageFuel emitFuel entryWidth callCap tailBudget) :=
  runtime_of_ledger sources k clock
    (budgetOf onset stageFuel emitFuel entryWidth callCap tailBudget)
    (8 * A + 4 * onset + 32) a sigma sigma onset logWidth ha hsigma (Nat.le_refl sigma)
    (fun N hN => budget_core (fun N => (outer sources k clock).result.pcp.nativeWidth N)
      logWidth stageFuel emitFuel entryWidth callCap tailBudget onset A a sigma kappa c
      hslack hlog hfit hlogTwo hstage hrest N hN)
    (fun N hN => le_trans (Nat.le_succ _) (hlog N hN))
    (fun N hN => le_trans (Nat.mul_le_mul (show sigma ≤ kappa by omega) (Nat.le_refl (logWidth N)))
      (hfit N hN))

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierFuel
