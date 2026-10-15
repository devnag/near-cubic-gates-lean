import Proof.Gates.CounterMachine.CellTablesCls4

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem pow_ge (T L c : ℕ) (h : T ≤ 2 ^ L) : T ^ c ≤ 2 ^ (c * L) := by
  rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left h c

theorem lamW_le (r : CellReq B1 B2 cT) :
    lamW r.c r.p ≤ 12 * (r.c.n + 1 + (cellInput r).length + 3) ^ 2 := by
  have sz := sizes r
  set Z := r.c.n + 1 + (cellInput r).length + 3 with hZ
  have hKB : keyBits r.p ≤ 2 * Z := by
    unfold keyBits; have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := r.p.P + r.p.J + 3))
    have := sz.P; have := sz.JX; omega
  have hKL : keyLen r.c r.p ≤ 2 * Z := by
    have : keyLen r.c r.p = dOf r.c r.p + 3 := by unfold keyLen dOf; omega
    have := sz.D; omega
  have hVW : valueWidth r.c r.p ≤ 6 * Z ^ 2 + Z := by
    unfold valueWidth
    have h1 : r.p.k ≤ Z := by have := sz.k; omega
    have h2 : Nat.size (deltaBound r.c r.p) ≤ 3 * Z := by have := sz.db; omega
    have h3 : 2 * r.p.k * Nat.size (deltaBound r.c r.p) ≤ 6 * Z ^ 2 := by
      calc 2 * r.p.k * Nat.size (deltaBound r.c r.p) ≤ 2 * Z * (3 * Z) := Nat.mul_le_mul (by omega) h2
        _ = 6 * Z ^ 2 := by ring
    have := sz.k
    omega
  unfold lamW
  have h1 : keyBits r.p * keyLen r.c r.p ≤ 2 * Z * (2 * Z) := Nat.mul_le_mul hKB hKL
  have h2 : 2 * Z * (2 * Z) = 4 * Z ^ 2 := by ring
  have h3 : Z ≤ Z ^ 2 := by nlinarith
  have h4 : r.c.n ≤ Z := by omega
  omega

theorem fit_of (RK : TabCallMachine B1 B2 cT PolyTab) (C0 e0 : ℕ)
    (hRK : ∀ x : TabCallReq B1 B2 cT, RK.budget x ≤ C0 * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ e0)
    (r : CellReq B1 B2 cT) :
    Fit RK r ((zK (zOf B1 B2 C0 e0) cT r.c.n (leadOnes (cellInput r))).W (leadOnes (cellInput r)))
      ((zK (zOf B1 B2 C0 e0) cT r.c.n (leadOnes (cellInput r))).Lk (leadOnes (cellInput r)))
      ((zK (zOf B1 B2 C0 e0) cT r.c.n (leadOnes (cellInput r))).Bk (leadOnes (cellInput r)))
      (C0 * (r.c.n + 1) ^ e0) ∧
    wdNeed r ≤ (zK (zOf B1 B2 C0 e0) cT r.c.n (leadOnes (cellInput r))).W (leadOnes (cellInput r)) := by
  have sz := sizes r
  have hs := cellReq_spec r
  rw [leadOnes_cellInput]
  set L := natBitLength r.c.n with hL
  set T := r.c.n + 1 with hT
  set X := (cellInput r).length with hX
  set Z := T + X + 3 with hZ
  set b0 := b0Of B1 B2 with hb0
  have hZle : Z ≤ zeta * T ^ b0 := Z_le r
  have hZ2 : Z ^ 2 ≤ zeta ^ 2 * T ^ (2 * b0) := by
    calc Z ^ 2 ≤ (zeta * T ^ b0) ^ 2 := Nat.pow_le_pow_left hZle 2
      _ = zeta ^ 2 * T ^ (2 * b0) := by ring
  have hTL : T ≤ 2 ^ L := sz.L1
  have hT1 : 1 ≤ T := by omega
  have hb1 : 1 ≤ b0 := by unfold b0 b0Of; omega
  -- the width
  have hW : C0 * T ^ e0 + 100 * Z ^ 2 + 16 ≤ (zK (zOf B1 B2 C0 e0) cT r.c.n L).W L := by
    show C0 * T ^ e0 + 100 * Z ^ 2 + 16 ≤ 2 ^ ((e0 + 2 * b0) * L) * (C0 + 100 * zeta ^ 2 + 16)
    have h1 := pow_ge T L (e0 + 2 * b0) hTL
    have h2 : T ^ e0 ≤ T ^ (e0 + 2 * b0) := Nat.pow_le_pow_right hT1 (by omega)
    have h3 : T ^ (2 * b0) ≤ T ^ (e0 + 2 * b0) := Nat.pow_le_pow_right hT1 (by omega)
    have h4 : 1 ≤ T ^ (e0 + 2 * b0) := Nat.one_le_pow _ _ hT1
    have h5 : C0 * T ^ e0 + 100 * Z ^ 2 + 16 ≤ T ^ (e0 + 2 * b0) * (C0 + 100 * zeta ^ 2 + 16) := by
      have := Nat.mul_le_mul_left C0 h2
      have := Nat.mul_le_mul_left (100 * zeta ^ 2) h3
      nlinarith
    exact h5.trans (Nat.mul_le_mul_right _ h1)
  set Wd := (zK (zOf B1 B2 C0 e0) cT r.c.n L).W L with hWd
  have hWlt : Wd < 2 ^ Wd := Nat.lt_two_pow_self
  have hlam := lamW_le r
  rw [← hT, ← hX, ← hZ] at hlam
  have hZ4 : 4 ≤ Z := by omega
  -- powers of the primes
  have hpow : ∀ q ∈ r.p.primes, ∀ m : ℕ, m ≤ 2 * Z ^ 2 → L * m ≤ 2 * Z ^ 2 * Z → q ^ m ≤ 2 ^ (L * m) := by
    intro q hq m _ _
    have hq' : q ≤ 2 ^ L := by have := (sz.q q hq).1; have := sz.P; omega
    rw [pow_mul]; exact Nat.pow_le_pow_left hq' m
  refine ⟨⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, ?_, fun q hq => ?_, fun q hq => ?_⟩, ?_⟩
  · -- the call bound
    have h1 := hRK x
    rw [hx] at h1
    show RK.budget x ≤ 2 ^ (e0 * L) * (2 ^ (r.c.n - kLow cT L) * (C0 + 1))
    have hk : kLow cT L ≤ r.p.k := by rw [hs.k_eq]; exact kLow_le cT _
    have h2 : 2 ^ (r.c.n - r.p.k) ≤ 2 ^ (r.c.n - kLow cT L) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 := pow_ge T L e0 hTL
    calc RK.budget x ≤ C0 * 2 ^ (r.c.n - r.p.k) * T ^ e0 := h1
      _ ≤ (C0 + 1) * 2 ^ (r.c.n - kLow cT L) * 2 ^ (e0 * L) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) h2) h3
      _ = _ := by ring
  · -- RK's input
    have h1 := tabCallInput_le x
    rw [hx, ← hX] at h1
    show (tabCallInput x).length ≤ 2 ^ (2 * b0 * L) * (20 * zeta ^ 2)
    have h2 := pow_ge T L (2 * b0) hTL
    have h3 : (r.c.n + X + 3) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (by omega) 2
    calc (tabCallInput x).length ≤ 20 * Z ^ 2 := by omega
      _ ≤ 20 * (zeta ^ 2 * T ^ (2 * b0)) := Nat.mul_le_mul_left _ hZ2
      _ ≤ 20 * (zeta ^ 2 * 2 ^ (2 * b0 * L)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ = _ := by ring
  · have := width_le RK C0 e0 hRK x; rw [hx] at this; exact this
  · show C0 * T ^ e0 + lamW r.c r.p + 4 ≤ Wd; omega
  · -- `4 q^e`
    have he : r.p.e ≤ 2 * T := by have := sz.e; have := sz.k; omega
    have hLT : L ≤ T := sz.L3
    have hLe : L * r.p.e ≤ 2 * Z ^ 2 := by
      have := Nat.mul_le_mul hLT he; nlinarith
    have h1 : r.p.e ≤ 2 * Z ^ 2 := by nlinarith
    have hq1 := hpow q hq r.p.e h1 (by nlinarith)
    calc 4 * q ^ r.p.e ≤ 4 * 2 ^ (L * r.p.e) := Nat.mul_le_mul_left _ hq1
      _ = 2 ^ (L * r.p.e + 2) := by rw [pow_add]; ring
      _ ≤ 2 ^ Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  · -- `2 q^D`
    have hLT : L ≤ T := sz.L3
    have hD := sz.D
    have hLD : L * dOf r.c r.p ≤ 2 * Z ^ 2 := by
      have := Nat.mul_le_mul hLT hD; nlinarith
    have hq1 := hpow q hq (dOf r.c r.p) (by nlinarith) (by nlinarith)
    calc 2 * q ^ dOf r.c r.p ≤ 2 * 2 ^ (L * dOf r.c r.p) := Nat.mul_le_mul_left _ hq1
      _ = 2 ^ (L * dOf r.c r.p + 1) := by rw [pow_add]; ring
      _ ≤ 2 ^ Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  · -- the program's width
    unfold wdNeed
    have := sz.P; have := sz.JX; have := sz.D; have := sz.db
    have hZZ : Z ≤ Z ^ 2 := by nlinarith
    omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
