import Proof.CaseAnalysis.WeakRuntime

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5

inductive Mode
  | thr
  | sym

end NearCubicWires.WireExponent3_5

namespace NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutWeakRuntime

/-- P18: the budget classes of `prim:runtime` / `tr:time`, plus the two non-exponential ones. -/
inductive BudgetClass

  | sourcePoly

  | selection

  | preprocessing

  | table

  | mainPass
  deriving DecidableEq

structure Envelope where

  sigma : ℕ

  callDeg : ℕ

  Amain : ℕ

  Atable : ℕ

  Asel : ℕ
  csel : ℕ

  Apre : ℕ
  cpsi : ℕ

def classBound (E : Envelope) : BudgetClass → (q k psi : ℕ) → ℕ
  | .sourcePoly, q, _, _ => q ^ E.Amain
  | .selection, q, k, _ => 2 ^ (q / 2 + E.csel * k) * q ^ E.Asel
  | .preprocessing, q, _, psi => 2 ^ (E.cpsi * psi) * q ^ E.Apre
  | .table, q, k, _ => 2 ^ (q - k) * q ^ E.Atable
  | .mainPass, q, k, _ => 2 ^ (q - k / 4) * q ^ E.Amain

/-- The frozen per-call cost contracts of C1-C6 (the machine contracts' budget fields are exactly these).
Each is a function of `(q, k, Ψ)` for EVERY `k`: a machine family uniform in `r`. One constant
coefficient `coef` is shared (it becomes the `B` of `littleO_of_split`). -/
structure ComponentCosts (E : Envelope) where
  coef : ℕ
  /-- C1 coset selection. -/
  sel : ℕ → ℕ → ℕ → ℕ
  /-- C2 explicit lists and expansions, C4 conditional-probability coefficients. -/
  pre : ℕ → ℕ → ℕ → ℕ
  /-- C3 printer table work of all `O(L²+k+L)` prefix decisions of one call. -/
  table : ℕ → ℕ → ℕ → ℕ
  /-- C5 final pass plus C6 per-call glue. -/
  main : ℕ → ℕ → ℕ → ℕ
  hsel : ∀ q k psi, sel q k psi ≤ coef * classBound E .selection q k psi
  hpre : ∀ q k psi, pre q k psi ≤ coef * classBound E .preprocessing q k psi
  htable : ∀ q k psi, table q k psi ≤ coef * classBound E .table q k psi
  hmain : ∀ q k psi, main q k psi ≤ coef * classBound E .mainPass q k psi

/-- One primitive call's time at `(q, k, Ψ)`: the sum of the component costs. -/
def ComponentCosts.perCall {E : Envelope} (C : ComponentCosts E) (q k psi : ℕ) : ℕ :=
  C.sel q k psi + C.pre q k psi + C.table q k psi + C.main q k psi

/-- The Ledger's fit conditions at one width (the only place `r`, through `k`, and `Ψ` meet the
envelope). `lg` is a supplied binary-log bound, as in REL's `hdamp_of_ledger`. -/
structure Fits (E : Envelope) (q lg k psi : ℕ) : Prop where
  hlog : q ≤ 2 ^ lg

  main : (E.Amain + E.callDeg + E.sigma) * lg ≤ k / 4
  table : (E.Atable + E.callDeg + E.sigma) * lg ≤ k
  kq : k ≤ q
  sel : E.csel * k + (E.Asel + E.callDeg + E.sigma) * lg ≤ q - q / 2

  pre : E.cpsi * psi + (E.Apre + E.callDeg + E.sigma) * lg ≤ q

theorem damp_of_pow_le {width tableExp power : ℕ} (hK : tableExp ≤ width)
    (h : width^power ≤ 2^tableExp) :
    2^(width-tableExp)*width^power ≤ 2^width := by
  calc 2^(width-tableExp)*width^power
      ≤ 2^(width-tableExp)*2^tableExp := Nat.mul_le_mul_left _ h
    _ = 2^((width-tableExp)+tableExp) := (pow_add 2 (width-tableExp) tableExp).symm
    _ = 2^width := by rw [Nat.sub_add_cancel hK]

theorem pow_le_two_pow {q lg P e : ℕ} (hlog : q ≤ 2 ^ lg) (h : P * lg ≤ e) : q ^ P ≤ 2 ^ e :=
  calc q ^ P ≤ (2 ^ lg) ^ P := Nat.pow_le_pow_left hlog P
    _ = 2 ^ (P * lg) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h

/-- One class, damped: `bound · q^{callDeg+sigma} ≤ 2^q`. -/
theorem damp_class (E : Envelope) (cls : BudgetClass) (q lg k psi : ℕ) (F : Fits E q lg k psi)
    (hcls : cls ≠ .sourcePoly) :
    classBound E cls q k psi * q ^ (E.callDeg + E.sigma) ≤ 2 ^ q := by
  cases cls with
  | sourcePoly => exact absurd rfl hcls
  | selection =>
    have hP : q ^ (E.Asel + (E.callDeg + E.sigma)) ≤ 2 ^ (q - q / 2 - E.csel * k) :=
      pow_le_two_pow F.hlog (by have := F.sel; rw [← Nat.add_assoc]; omega)
    calc classBound E .selection q k psi * q ^ (E.callDeg + E.sigma)
        = 2 ^ (q / 2 + E.csel * k) * q ^ (E.Asel + (E.callDeg + E.sigma)) := by
          simp only [classBound, pow_add]; ring
      _ ≤ 2 ^ (q / 2 + E.csel * k) * 2 ^ (q - q / 2 - E.csel * k) := Nat.mul_le_mul_left _ hP
      _ = 2 ^ q := by
          rw [← pow_add]; congr 1; have := F.sel; omega
  | preprocessing =>
    have hP : q ^ (E.Apre + (E.callDeg + E.sigma)) ≤ 2 ^ (q - E.cpsi * psi) :=
      pow_le_two_pow F.hlog (by have := F.pre; rw [← Nat.add_assoc]; omega)
    calc classBound E .preprocessing q k psi * q ^ (E.callDeg + E.sigma)
        = 2 ^ (E.cpsi * psi) * q ^ (E.Apre + (E.callDeg + E.sigma)) := by
          simp only [classBound, pow_add]; ring
      _ ≤ 2 ^ (E.cpsi * psi) * 2 ^ (q - E.cpsi * psi) := Nat.mul_le_mul_left _ hP
      _ = 2 ^ q := by rw [← pow_add]; congr 1; have := F.pre; omega
  | table =>
    have hP : q ^ (E.Atable + (E.callDeg + E.sigma)) ≤ 2 ^ k :=
      pow_le_two_pow F.hlog (by have := F.table; rw [← Nat.add_assoc]; exact this)
    calc classBound E .table q k psi * q ^ (E.callDeg + E.sigma)
        = 2 ^ (q - k) * q ^ (E.Atable + (E.callDeg + E.sigma)) := by
          simp only [classBound, pow_add]; ring
      _ ≤ 2 ^ q := damp_of_pow_le F.kq hP
  | mainPass =>
    have hP : q ^ (E.Amain + (E.callDeg + E.sigma)) ≤ 2 ^ (k / 4) :=
      pow_le_two_pow F.hlog (by have := F.main; rw [← Nat.add_assoc]; exact this)
    calc classBound E .mainPass q k psi * q ^ (E.callDeg + E.sigma)
        = 2 ^ (q - k / 4) * q ^ (E.Amain + (E.callDeg + E.sigma)) := by
          simp only [classBound, pow_add]; ring
      _ ≤ 2 ^ q := damp_of_pow_le (le_trans (Nat.div_le_self k 4) F.kq) hP

/-- All verification calls of one input length, damped: `B = 4·coef`. -/
theorem damp_calls (E : Envelope) (C : ComponentCosts E) (q lg k psi : ℕ)
    (F : Fits E q lg k psi) :
    (q ^ E.callDeg * C.perCall q k psi) * q ^ E.sigma ≤ (4 * C.coef) * 2 ^ q := by
  have hs := Nat.mul_le_mul_left C.coef (damp_class E .selection q lg k psi F (by decide))
  have hp := Nat.mul_le_mul_left C.coef (damp_class E .preprocessing q lg k psi F (by decide))
  have ht := Nat.mul_le_mul_left C.coef (damp_class E .table q lg k psi F (by decide))
  have hm := Nat.mul_le_mul_left C.coef (damp_class E .mainPass q lg k psi F (by decide))
  have hsum : C.perCall q k psi ≤ C.coef * classBound E .selection q k psi +
      C.coef * classBound E .preprocessing q k psi + C.coef * classBound E .table q k psi +
      C.coef * classBound E .mainPass q k psi := by
    unfold ComponentCosts.perCall
    have := C.hsel q k psi; have := C.hpre q k psi; have := C.htable q k psi
    have := C.hmain q k psi; omega
  have hq : q ^ E.callDeg * q ^ E.sigma = q ^ (E.callDeg + E.sigma) := (pow_add q _ _).symm
  set P := q ^ (E.callDeg + E.sigma)
  calc (q ^ E.callDeg * C.perCall q k psi) * q ^ E.sigma
      = C.perCall q k psi * P := by rw [← hq]; ring
    _ ≤ (C.coef * classBound E .selection q k psi + C.coef * classBound E .preprocessing q k psi +
          C.coef * classBound E .table q k psi + C.coef * classBound E .mainPass q k psi) * P :=
          Nat.mul_le_mul_right _ hsum
    _ = C.coef * (classBound E .selection q k psi * P) +
          C.coef * (classBound E .preprocessing q k psi * P) +
          C.coef * (classBound E .table q k psi * P) +
          C.coef * (classBound E .mainPass q k psi * P) := by ring
    _ ≤ (4 * C.coef) * 2 ^ q := by
          have e : (4 * C.coef) * 2 ^ q = C.coef * 2 ^ q + C.coef * 2 ^ q + C.coef * 2 ^ q +
            C.coef * 2 ^ q := by ring
          rw [e]; exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hs hp) ht) hm

/-- An upper square root: `√x ≤ sqrtUp x`. -/
def sqrtUp (x : ℕ) : ℕ := Nat.sqrt x + 1

def starWidth (r q : ℕ) : ℕ := r * Nat.log 2 (q / r + 1)

def loadThr (CD k L B : ℕ) : ℕ := CD * ((k + L) ^ 2 * (CD * (sqrtUp (B * L) + L ^ 2)) + k + L ^ 2)

def loadSym (CD k L B : ℕ) : ℕ := CD * ((k + L) ^ 2 * (CD * (sqrtUp B + L)) + k + L ^ 2)

def loadAux (CD k L : ℕ) : ℕ := CD * (k + L ^ 2 + (k + L ^ 3) * L ^ 2 * (k + L))

def loadPsi (CD k L BT BS : ℕ) : ℕ := max (loadThr CD k L BT) (max (loadSym CD k L BS) (loadAux CD k L))

structure TimeBudget (kclk : ℕ) (E : Envelope) where

  q : ℕ → ℕ
  lg : ℕ → ℕ

  rOf : ℕ → ℕ

  capOf : Mode → ℕ → ℕ
  capOf_pos : ∀ m q, 1 ≤ capOf m q

  CD : ℕ
  costs : ComponentCosts E

  A : ℕ
  a : ℕ
  ha : a ≤ kclk + 1

  Ctab : ℕ
  d : ℕ
  hsigma : d + 1 ≤ E.sigma
  growth : ∀ m, ∃ onset, ∀ N, onset ≤ N → m ≤ q N
  onset : ℕ
  table : ∀ N, onset ≤ N → 2 ^ q N ≤ Ctab * N ^ (kclk + 2) * q N ^ d
  fits : ∀ N, onset ≤ N → Fits E (q N) (lg (q N)) (starWidth (rOf (q N)) (q N))
    (loadPsi CD (starWidth (rOf (q N)) (q N)) (Nat.clog 2 (q N + 2)) (capOf .thr (q N)) (capOf .sym (q N)))

def TimeBudget.kOf {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (q : ℕ) : ℕ := starWidth (B.rOf q) q

def TimeBudget.psiOf {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (q : ℕ) : ℕ :=
  loadPsi B.CD (B.kOf q) (Nat.clog 2 (q + 2)) (B.capOf .thr q) (B.capOf .sym q)

def TimeBudget.callBudget {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (q : ℕ) : ℕ :=
  B.costs.perCall q (B.kOf q) (B.psiOf q)

def TimeBudget.FitsAt {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (n : ℕ) : Prop :=
  Fits E n (B.lg n) (B.kOf n) (B.psiOf n)

def TimeBudget.Split {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (M : OrdinaryWeakMachine) : Prop :=
  ∀ N, B.onset ≤ N → M.runtime N ≤ B.A * (N + 1) ^ B.a + B.q N ^ E.callDeg * B.callBudget (B.q N)

/-- **`Runtime3`.** The weak machine's runtime split into the source-polynomial part and `q^callDeg` primitive
calls, each costed by the frozen contracts; the ledger fits hold eventually along the machine's own schedule
`k = kOf (q N)`, `Ψ = psiOf (q N)`. -/
structure Runtime3 (M : OrdinaryWeakMachine) (kclk : ℕ) (E : Envelope) extends TimeBudget kclk E where
  split : toTimeBudget.Split M

theorem Runtime3.littleO {M : OrdinaryWeakMachine} {kclk : ℕ} {E : Envelope}
    (R : Runtime3 M kclk E) : OrdinaryLittleO M (fun n => n ^ (kclk + 2)) :=
  littleO_of_split M kclk R.A (4 * R.costs.coef) R.Ctab R.a R.d E.sigma R.q
    (fun N => R.q N ^ E.callDeg * R.costs.perCall (R.q N) (R.kOf (R.q N)) (R.psiOf (R.q N)))
    R.ha R.hsigma R.growth
    ⟨R.onset, fun N hN => ⟨R.split N hN,
      damp_calls E R.costs (R.q N) (R.lg (R.q N)) (R.kOf (R.q N)) (R.psiOf (R.q N)) (R.fits N hN),
      R.table N hN⟩⟩

theorem final_pass_count (q k Q A C' c : ℕ) (hk : k ≤ q) (hQ : Q ≤ 2 ^ ((3 * k + 3) / 4) * q ^ C') :
    2 ^ (q - k) * (Q * (c * q ^ A)) ≤ c * (2 ^ (q - k / 4) * q ^ (A + C')) := by
  have he : q - k + (3 * k + 3) / 4 = q - k / 4 := by omega
  calc 2 ^ (q - k) * (Q * (c * q ^ A))
      ≤ 2 ^ (q - k) * ((2 ^ ((3 * k + 3) / 4) * q ^ C') * (c * q ^ A)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hQ)
    _ = c * (2 ^ (q - k + (3 * k + 3) / 4) * q ^ (A + C')) := by rw [pow_add, pow_add]; ring
    _ = c * (2 ^ (q - k / 4) * q ^ (A + C')) := by rw [he]

theorem selection_count (q k A c : ℕ) (hk : k ≤ q) :
    2 ^ k * (2 ^ k * (2 ^ ((q - k + 1) / 2) * (c * q ^ A))) ≤
      (2 * c) * (2 ^ (q / 2 + 2 * k) * q ^ A) := by
  have he : k + (k + (q - k + 1) / 2) ≤ q / 2 + 2 * k + 1 := by omega
  have hp : 2 ^ (k + (k + (q - k + 1) / 2)) ≤ 2 ^ (q / 2 + 2 * k + 1) :=
    Nat.pow_le_pow_right (by norm_num) he
  calc 2 ^ k * (2 ^ k * (2 ^ ((q - k + 1) / 2) * (c * q ^ A)))
      = 2 ^ (k + (k + (q - k + 1) / 2)) * (c * q ^ A) := by rw [pow_add, pow_add]; ring
    _ ≤ 2 ^ (q / 2 + 2 * k + 1) * (c * q ^ A) := Nat.mul_le_mul_right _ hp
    _ = (2 * c) * (2 ^ (q / 2 + 2 * k) * q ^ A) := by rw [pow_succ]; ring

theorem printer_calls_count (q k P pc A c : ℕ) (hP : P ≤ q ^ pc) :
    P * (c * (2 ^ (q - k) * q ^ A)) ≤ c * (2 ^ (q - k) * q ^ (A + pc)) := by
  calc P * (c * (2 ^ (q - k) * q ^ A)) ≤ q ^ pc * (c * (2 ^ (q - k) * q ^ A)) :=
        Nat.mul_le_mul_right _ hP
    _ = c * (2 ^ (q - k) * q ^ (A + pc)) := by rw [pow_add]; ring

theorem per_column_2k_breaks (q k : ℕ) (hk : 4 ≤ k) (hq : k ≤ q) :
    2 ^ (q - k / 4) < 2 ^ (q - k) * 2 ^ k := by
  rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ## Satisfiability: the fit premises hold at a plausible instantiation

Envelope: sigma = 8, callDeg = 4, every other exponent 6, csel = 2, cpsi = 1.
Width q = 2^40 (lg = 40). Star width k = 4·(6+4+8)·40 = 2880, i.e. `r·s` with `s ≈ 40`,
`r = 72`. Load Ψ = q/2 (a stand-in for the `o(q)` load of `tr:load`). -/
def satEnvelope : Envelope :=
  { sigma := 8, callDeg := 4, Amain := 6, Atable := 6, Asel := 6, csel := 2, Apre := 6, cpsi := 1 }

theorem sat_fits : Fits satEnvelope (2 ^ 40) 40 2880 (2 ^ 39) := by
  refine ⟨le_refl _, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [satEnvelope]

theorem paper_k_r96 : 96 * Nat.log 2 (2 ^ 40 / 96 + 1) = 3168 := by
  have h : Nat.log 2 (2 ^ 40 / 96 + 1) = 33 := by
    rw [Nat.log_eq_iff (by norm_num)]; norm_num
  rw [h]

theorem sat_fits_paper_k : Fits satEnvelope (2 ^ 40) 40 3168 (2 ^ 39) := by
  refine ⟨le_refl _, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [satEnvelope]

theorem r80_fails : ¬ ((6 + 4 + 8) * 40 ≤ 80 * Nat.log 2 (2 ^ 40 / 80 + 1) / 4) := by
  have h : Nat.log 2 (2 ^ 40 / 80 + 1) = 33 := by
    rw [Nat.log_eq_iff (by norm_num)]; norm_num
  rw [h]; norm_num

end NearCubicWires.WireExponent3_5.Cost
