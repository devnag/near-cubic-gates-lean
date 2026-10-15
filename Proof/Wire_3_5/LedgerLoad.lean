import Proof.Wire_3_5.LedgerCap

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost Filter

def rowBr (cr q : ℕ) : ℕ := 2 * (Nat.log 2 (Lq q) + cr)

theorem rowBr_even (cr q : ℕ) : Even (rowBr cr q) := ⟨Nat.log 2 (Lq q) + cr, by unfold rowBr; ring⟩

theorem two_le_rowBr {cr : ℕ} (hcr : 1 ≤ cr) (q : ℕ) : 2 ≤ rowBr cr q := by unfold rowBr; omega

/-- `r + 1 ≤ (2c_r + 3)·L`. -/
theorem rowBr_succ_le (cr q : ℕ) : rowBr cr q + 1 ≤ (2 * cr + 3) * Lq q := by
  unfold rowBr
  have h1 : Nat.log 2 (Lq q) ≤ Lq q := Nat.log_le_self 2 _
  have h2 := Lq_pos q
  have h3 : cr ≤ cr * Lq q := Nat.le_mul_of_pos_right cr h2
  have h4 : (2 * cr + 3) * Lq q = 2 * (cr * Lq q) + 3 * Lq q := by ring
  omega

/-- The star width is at most `r·L`. -/
theorem starWidth_le (r q : ℕ) : starWidth r q ≤ r * Lq q := by
  unfold starWidth
  apply Nat.mul_le_mul_left
  calc Nat.log 2 (q / r + 1) ≤ Nat.log 2 (q + 2) := Nat.log_mono_right (by
        have := Nat.div_le_self q r; omega)
    _ ≤ Lq q := Nat.log_le_clog 2 (q + 2)

/-- **`(log L)^{O(1)} = o(L^{1/32})`, at the 64th power**: `K·(r(q)+1)^{176} ≤ L(q)²` eventually. -/
theorem eventually_rowBr_pow_le (cr K : ℕ) : ∀ᶠ q : ℕ in atTop, K * (rowBr cr q + 1) ^ 176 ≤ Lq q ^ 2 := by
  have h := tendsto_log_Lq.eventually (eventually_mul_affine_pow_le_two_pow K 2 (2 * cr + 1) 176)
  filter_upwards [h] with q hq
  have h1 : rowBr cr q + 1 = 2 * Nat.log 2 (Lq q) + (2 * cr + 1) := by unfold rowBr; ring
  have h2 : 2 ^ Nat.log 2 (Lq q) ≤ Lq q := Nat.pow_log_le_self 2 (by have := Lq_pos q; omega)
  have h3 : Lq q ≤ Lq q ^ 2 := Nat.le_self_pow (by norm_num) _
  rw [h1]; omega

/-- `s^{32} ≤ C_sp^4 L^{12}` from `s^8 ≤ C_sp L^3`. -/
theorem sp_pow32_le {s Csp L : ℕ} (hs : s ^ 8 ≤ Csp * L ^ 3) : s ^ 32 ≤ Csp ^ 4 * L ^ 12 := by
  calc s ^ 32 = (s ^ 8) ^ 4 := by rw [← pow_mul]
    _ ≤ (Csp * L ^ 3) ^ 4 := Nat.pow_le_pow_left hs 4
    _ = Csp ^ 4 * L ^ 12 := by ring

/-- The square-root term: `2A·√x ≤ q` from `4A²x ≤ q²`. -/
theorem two_mul_sqrt_le {A x q : ℕ} (h : 4 * A ^ 2 * x ≤ q ^ 2) : 2 * A * Nat.sqrt x ≤ q := by
  have hs : Nat.sqrt x * Nat.sqrt x ≤ x := Nat.sqrt_le x
  have h2 : (2 * A * Nat.sqrt x) ^ 2 ≤ q ^ 2 := by
    calc (2 * A * Nat.sqrt x) ^ 2 = 4 * A ^ 2 * (Nat.sqrt x * Nat.sqrt x) := by ring
      _ ≤ 4 * A ^ 2 * x := Nat.mul_le_mul_left _ hs
      _ ≤ q ^ 2 := h
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2

theorem mainRoot_pow_mul_le (C : CapParams) (m : Mode) (r s q : ℕ) :
    ceilRoot 31 (capMainPow C m r s q) ^ 32 * Lq q ^ capExp32 m ≤
      2 ^ 32 * (capMainNum C m r s q + 2 * Lq q ^ capExp32 m) := by
  have h1 := ceilRoot_pow_le 31 (capMainPow C m r s q)
  have h2 := capMainPow_mul_le C m r s q
  calc ceilRoot 31 (capMainPow C m r s q) ^ 32 * Lq q ^ capExp32 m
      ≤ 2 ^ 32 * (capMainPow C m r s q + 1) * Lq q ^ capExp32 m := Nat.mul_le_mul_right _ h1
    _ = 2 ^ 32 * (capMainPow C m r s q * Lq q ^ capExp32 m + Lq q ^ capExp32 m) := by ring
    _ ≤ 2 ^ 32 * (capMainNum C m r s q + Lq q ^ capExp32 m + Lq q ^ capExp32 m) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ 32 * (capMainNum C m r s q + 2 * Lq q ^ capExp32 m) := by ring

/-- The encoding part of the square-root term: `2·4X²(1+E)L^e ≤ q²`. -/
theorem enc_part_le {X E L q e KX KE : ℕ} (hX : X ≤ KX * L ^ 4) (hE : 1 + E ≤ KE * L ^ 3 * q)
    (hLe : L ^ e ≤ L) (h3 : 8 * KX ^ 2 * KE * L ^ 12 ≤ q) : 2 * (4 * X ^ 2 * (1 + E) * L ^ e) ≤ q ^ 2 := by
  have hX2 : X ^ 2 ≤ (KX * L ^ 4) ^ 2 := Nat.pow_le_pow_left hX 2
  calc 2 * (4 * X ^ 2 * (1 + E) * L ^ e) ≤ 2 * (4 * (KX * L ^ 4) ^ 2 * (KE * L ^ 3 * q) * L) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hX2) hE) hLe
    _ = (8 * KX ^ 2 * KE * L ^ 12) * q := by ring
    _ ≤ q * q := Nat.mul_le_mul_right _ h3
    _ = q ^ 2 := by ring

/-- Cancel a positive factor from a 32nd-power comparison. -/
theorem le_of_pow32_mul_le {Z Q D : ℕ} (hD : 0 < D) (h : Z ^ 32 * D ≤ Q ^ 32 * D) : Z ≤ Q :=
  (Nat.pow_le_pow_iff_left (by norm_num)).mp (Nat.le_of_mul_le_mul_right h hD)

theorem root_part_le {Y M N D Q : ℕ} (hD : 0 < D) (hroot : M ^ 32 * D ≤ 2 ^ 32 * (N + 2 * D))
    (hA : 2 * (Y ^ 32 * 2 ^ 32 * N) ≤ Q ^ 32 * D) (hB : 2 * (Y ^ 32 * 2 ^ 32 * (2 * D)) ≤ Q ^ 32 * D) :
    Y * M ≤ Q := by
  apply le_of_pow32_mul_le hD
  calc (Y * M) ^ 32 * D = Y ^ 32 * (M ^ 32 * D) := by ring
    _ ≤ Y ^ 32 * (2 ^ 32 * (N + 2 * D)) := Nat.mul_le_mul_left _ hroot
    _ = Y ^ 32 * 2 ^ 32 * N + Y ^ 32 * 2 ^ 32 * (2 * D) := by ring
    _ ≤ Q ^ 32 * D := by omega

/-- The smallness of the main part: `2Y^{32}2^{32}N ≤ Q^{32}L^K` with `Y = 8X²L^e`, `Q = q²`. -/
theorem main_small {X R L q e N KX KN Kexp : ℕ} (hX : X ≤ KX * R ^ 2 * L ^ 2) (hN : N ≤ KN * R ^ 48 * L ^ 12 * q ^ 64)
    (hK : 142 + 32 * e ≤ Kexp) (hL : 1 ≤ L)
    (h1 : 2 * (8 ^ 32 * KX ^ 64 * 2 ^ 32 * KN) * R ^ 176 ≤ L ^ 2) :
    2 * ((8 * X ^ 2 * L ^ e) ^ 32 * 2 ^ 32 * N) ≤ (q ^ 2) ^ 32 * L ^ Kexp := by
  have hX64 : X ^ 64 ≤ (KX * R ^ 2 * L ^ 2) ^ 64 := Nat.pow_le_pow_left hX 64
  have hLK : L ^ (142 + 32 * e) ≤ L ^ Kexp := Nat.pow_le_pow_right hL hK
  calc 2 * ((8 * X ^ 2 * L ^ e) ^ 32 * 2 ^ 32 * N) = 2 * (8 ^ 32 * X ^ 64 * L ^ (32 * e) * 2 ^ 32 * N) := by ring
    _ ≤ 2 * (8 ^ 32 * (KX * R ^ 2 * L ^ 2) ^ 64 * L ^ (32 * e) * 2 ^ 32 * (KN * R ^ 48 * L ^ 12 * q ^ 64)) := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hX64))) hN
    _ = (2 * (8 ^ 32 * KX ^ 64 * 2 ^ 32 * KN) * R ^ 176) * (L ^ (140 + 32 * e) * q ^ 64) := by ring
    _ ≤ L ^ 2 * (L ^ (140 + 32 * e) * q ^ 64) := Nat.mul_le_mul_right _ h1
    _ = (q ^ 2) ^ 32 * L ^ (142 + 32 * e) := by ring
    _ ≤ (q ^ 2) ^ 32 * L ^ Kexp := Nat.mul_le_mul_left _ hLK

theorem rest_small {X R L q e KX c1 Kexp : ℕ} (hX : X ≤ KX * R ^ 2 * L ^ 2) (hR : R ≤ c1 * L) (he : e ≤ 1)
    (hL : 1 ≤ L) (h2 : 2 * (8 ^ 32 * KX ^ 64 * 2 ^ 33) * c1 ^ 128 * L ^ 288 ≤ q) :
    2 * ((8 * X ^ 2 * L ^ e) ^ 32 * 2 ^ 32 * (2 * L ^ Kexp)) ≤ (q ^ 2) ^ 32 * L ^ Kexp := by
  have hX64 : X ^ 64 ≤ (KX * (c1 * L) ^ 2 * L ^ 2) ^ 64 :=
    Nat.pow_le_pow_left (hX.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hR 2)))) 64
  have hLe : L ^ (32 * e) ≤ L ^ 32 := Nat.pow_le_pow_right hL (by omega)
  have hq : q ≤ (q ^ 2) ^ 32 := by rw [← pow_mul]; exact Nat.le_self_pow (by norm_num) q
  calc 2 * ((8 * X ^ 2 * L ^ e) ^ 32 * 2 ^ 32 * (2 * L ^ Kexp))
      = (2 * (8 ^ 32 * 2 ^ 33) * X ^ 64 * L ^ (32 * e)) * L ^ Kexp := by ring
    _ ≤ (2 * (8 ^ 32 * 2 ^ 33) * (KX * (c1 * L) ^ 2 * L ^ 2) ^ 64 * L ^ 32) * L ^ Kexp := by
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hX64) hLe
    _ = (2 * (8 ^ 32 * KX ^ 64 * 2 ^ 33) * c1 ^ 128 * L ^ 288) * L ^ Kexp := by ring
    _ ≤ q * L ^ Kexp := Nat.mul_le_mul_right _ h2
    _ ≤ (q ^ 2) ^ 32 * L ^ Kexp := Nat.mul_le_mul_right _ hq

/-! ## The three loads at one width -/

theorem capExp32_sym : capExp32 .sym = 142 := rfl
theorem capExp32_thr : capExp32 .thr = 174 := rfl

/-- The cap's main numerator against `R^{48}L^{12}q^{64}`. -/
theorem capMainNum_le (C : CapParams) (m : Mode) {r s q Csp L : ℕ} (hs : s ^ 8 ≤ Csp * L ^ 3) :
    capMainNum C m r s q ≤ (2 ^ 80 * Csp ^ 4 * C.coef m ^ 32 * C.betaInv ^ 32) * (r + 1) ^ 48 * L ^ 12 * q ^ 64 := by
  unfold capMainNum
  have h1 := sp_pow32_le hs
  have h2 : r ^ 48 ≤ (r + 1) ^ 48 := Nat.pow_le_pow_left (Nat.le_succ r) _
  calc 2 ^ 80 * r ^ 48 * s ^ 32 * C.coef m ^ 32 * q ^ 64 * C.betaInv ^ 32
      ≤ 2 ^ 80 * (r + 1) ^ 48 * (Csp ^ 4 * L ^ 12) * C.coef m ^ 32 * q ^ 64 * C.betaInv ^ 32 := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h1
    _ = (2 ^ 80 * Csp ^ 4 * C.coef m ^ 32 * C.betaInv ^ 32) * (r + 1) ^ 48 * L ^ 12 * q ^ 64 := by ring

theorem one_add_enc_le (C : CapParams) {r q c1 L : ℕ} (hq : 1 ≤ q) (hL : 1 ≤ L) (hR : r + 1 ≤ c1 * L) :
    1 + ceilRoot 1 (capEncPow C r q) ≤ (1 + 32 * c1 ^ 3 * C.Cpar ^ 2 * C.betaInv ^ 2) * L ^ 3 * q := by
  have hE : ceilRoot 1 (capEncPow C r q) ≤ 32 * c1 ^ 3 * C.Cpar ^ 2 * C.betaInv ^ 2 * L ^ 3 * q := by
    calc ceilRoot 1 (capEncPow C r q) ≤ capEncPow C r q := ceilRoot_le_self 1 _
      _ = 32 * r ^ 3 * C.Cpar ^ 2 * q * C.betaInv ^ 2 := rfl
      _ ≤ 32 * (c1 * L) ^ 3 * C.Cpar ^ 2 * q * C.betaInv ^ 2 := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      _ = 32 * c1 ^ 3 * C.Cpar ^ 2 * C.betaInv ^ 2 * L ^ 3 * q := by ring
  have h1 : 1 ≤ L ^ 3 * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e1 : (1 + 32 * c1 ^ 3 * C.Cpar ^ 2 * C.betaInv ^ 2) * L ^ 3 * q =
      L ^ 3 * q + 32 * c1 ^ 3 * C.Cpar ^ 2 * C.betaInv ^ 2 * L ^ 3 * q := by ring
  omega

/-- `4X²·B_m·L^e ≤ q²` at one width, from the fixed smallness conditions (`e = 0` for `SYM`, `1` for `THR`). -/
theorem cap_term_le (C : CapParams) (m : Mode) (e : ℕ) (he : e ≤ 1) (hK : 142 + 32 * e ≤ capExp32 m)
    {X r s q c1 Csp KX : ℕ} (hq : 1 ≤ q) (hX : X ≤ KX * (r + 1) ^ 2 * Lq q ^ 2)
    (hR : r + 1 ≤ c1 * Lq q) (hs : s ^ 8 ≤ Csp * Lq q ^ 3)
    (h1 : 2 * (8 ^ 32 * KX ^ 64 * 2 ^ 32 * (2 ^ 80 * Csp ^ 4 * C.coef m ^ 32 * C.betaInv ^ 32)) * (r + 1) ^ 176 ≤
      Lq q ^ 2)
    (h2 : 2 * (8 ^ 32 * KX ^ 64 * 2 ^ 33) * c1 ^ 128 * Lq q ^ 288 ≤ q)
    (h3 : 8 * (KX * c1 ^ 2) ^ 2 * (1 + 32 * c1 ^ 3 * C.Cpar ^ 2 * C.betaInv ^ 2) * Lq q ^ 12 ≤ q) :
    4 * X ^ 2 * (rowBCap C m r s q * Lq q ^ e) ≤ q ^ 2 := by
  have hL : 1 ≤ Lq q := Lq_pos q
  have hX4 : X ≤ (KX * c1 ^ 2) * Lq q ^ 4 := by
    calc X ≤ KX * (r + 1) ^ 2 * Lq q ^ 2 := hX
      _ ≤ KX * (c1 * Lq q) ^ 2 * Lq q ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hR 2))
      _ = (KX * c1 ^ 2) * Lq q ^ 4 := by ring
  have hLe : Lq q ^ e ≤ Lq q := by
    calc Lq q ^ e ≤ Lq q ^ 1 := Nat.pow_le_pow_right hL he
      _ = Lq q := pow_one _
  have hE := one_add_enc_le C hq hL hR
  have henc := enc_part_le hX4 hE hLe h3
  have hroot := mainRoot_pow_mul_le C m r s q
  have hN := capMainNum_le C m (r := r) (q := q) hs
  have hA := main_small (e := e) (Kexp := capExp32 m) hX hN hK hL h1
  have hB := rest_small (e := e) (Kexp := capExp32 m) hX hR he hL h2
  have hmain := root_part_le (Y := 8 * X ^ 2 * Lq q ^ e) (pow_pos (by omega) _) hroot hA hB
  have hBdef : rowBCap C m r s q = (1 + ceilRoot 1 (capEncPow C r q)) + ceilRoot 31 (capMainPow C m r s q) := by
    unfold rowBCap; ring
  rw [hBdef]
  have e1 : 4 * X ^ 2 * (((1 + ceilRoot 1 (capEncPow C r q)) + ceilRoot 31 (capMainPow C m r s q)) * Lq q ^ e) =
      4 * X ^ 2 * (1 + ceilRoot 1 (capEncPow C r q)) * Lq q ^ e +
        (8 * X ^ 2 * Lq q ^ e * ceilRoot 31 (capMainPow C m r s q)) / 2 * 1 := by
    have : 8 * X ^ 2 * Lq q ^ e * ceilRoot 31 (capMainPow C m r s q) =
        2 * (4 * X ^ 2 * ceilRoot 31 (capMainPow C m r s q) * Lq q ^ e) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]; ring
  rw [e1]
  omega

/-- `(k + L)² ≤ (r+1)²L²` from `k ≤ rL`. -/
theorem kL_sq_le {k r L : ℕ} (hk : k ≤ r * L) : (k + L) ^ 2 ≤ (r + 1) ^ 2 * L ^ 2 := by
  calc (k + L) ^ 2 ≤ ((r + 1) * L) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
    _ = (r + 1) ^ 2 * L ^ 2 := by ring

/-- The additive remainder of `Ψ_T`/`Ψ_S` is polylogarithmic: at most `K_rest·L^7`. -/
theorem rest_le {c CD k r L c1 : ℕ} (hL : 1 ≤ L) (hk : k ≤ r * L) (hR : r + 1 ≤ c1 * L) (t : ℕ) (ht : t ≤ 2) :
    c * CD ^ 2 * (k + L) ^ 2 * (1 + L ^ t) + c * CD * k + c * CD * L ^ 2 ≤
      (2 * c * CD ^ 2 * c1 ^ 2 + c * CD * c1 + c * CD) * L ^ 7 := by
  have hkL : (k + L) ^ 2 ≤ c1 ^ 2 * L ^ 4 := by
    calc (k + L) ^ 2 ≤ (r + 1) ^ 2 * L ^ 2 := kL_sq_le hk
      _ ≤ (c1 * L) ^ 2 * L ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hR 2)
      _ = c1 ^ 2 * L ^ 4 := by ring
  have hLt : 1 + L ^ t ≤ 2 * L ^ 2 := by
    have h1 : L ^ t ≤ L ^ 2 := Nat.pow_le_pow_right hL ht
    have h2 : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ hL
    omega
  have hk' : k ≤ c1 * L ^ 2 := by
    calc k ≤ r * L := hk
      _ ≤ (c1 * L) * L := Nat.mul_le_mul_right _ (by omega)
      _ = c1 * L ^ 2 := by ring
  have hL6 : L ^ 6 ≤ L ^ 7 := Nat.pow_le_pow_right hL (by norm_num)
  have hL2 : L ^ 2 ≤ L ^ 7 := Nat.pow_le_pow_right hL (by norm_num)
  calc c * CD ^ 2 * (k + L) ^ 2 * (1 + L ^ t) + c * CD * k + c * CD * L ^ 2
      ≤ c * CD ^ 2 * (c1 ^ 2 * L ^ 4) * (2 * L ^ 2) + c * CD * (c1 * L ^ 2) + c * CD * L ^ 2 := by
        gcongr
    _ = 2 * c * CD ^ 2 * c1 ^ 2 * L ^ 6 + c * CD * c1 * L ^ 2 + c * CD * L ^ 2 := by ring
    _ ≤ 2 * c * CD ^ 2 * c1 ^ 2 * L ^ 7 + c * CD * c1 * L ^ 7 + c * CD * L ^ 7 := by gcongr
    _ = (2 * c * CD ^ 2 * c1 ^ 2 + c * CD * c1 + c * CD) * L ^ 7 := by ring

/-- The `SYM` load at one width: `c·Ψ_S ≤ q`. -/
theorem sym_load_le (C : CapParams) {CD c c1 Csp r s q k : ℕ} (hq : 1 ≤ q) (hk : k ≤ r * Lq q)
    (hR : r + 1 ≤ c1 * Lq q) (hs : s ^ 8 ≤ Csp * Lq q ^ 3)
    (h1 : 2 * (8 ^ 32 * (c * CD ^ 2) ^ 64 * 2 ^ 32 * (2 ^ 80 * Csp ^ 4 * C.coef .sym ^ 32 * C.betaInv ^ 32)) *
      (r + 1) ^ 176 ≤ Lq q ^ 2)
    (h2 : 2 * (8 ^ 32 * (c * CD ^ 2) ^ 64 * 2 ^ 33) * c1 ^ 128 * Lq q ^ 288 ≤ q)
    (h3 : 8 * ((c * CD ^ 2) * c1 ^ 2) ^ 2 * (1 + 32 * c1 ^ 3 * C.Cpar ^ 2 * C.betaInv ^ 2) * Lq q ^ 12 ≤ q)
    (h4 : 2 * ((2 * c * CD ^ 2 * c1 ^ 2 + c * CD * c1 + c * CD) * Lq q ^ 7) ≤ q) :
    c * loadSym CD k (Lq q) (rowBCap C .sym r s q) ≤ q := by
  have hL := Lq_pos q
  set X := c * CD ^ 2 * (k + Lq q) ^ 2 with hXdef
  have hX : X ≤ (c * CD ^ 2) * (r + 1) ^ 2 * Lq q ^ 2 := by
    calc X = (c * CD ^ 2) * (k + Lq q) ^ 2 := by rw [hXdef]
      _ ≤ (c * CD ^ 2) * ((r + 1) ^ 2 * Lq q ^ 2) := Nat.mul_le_mul_left _ (kL_sq_le hk)
      _ = (c * CD ^ 2) * (r + 1) ^ 2 * Lq q ^ 2 := by ring
  have hterm := cap_term_le C .sym 0 (by norm_num) (by rw [capExp32_sym]) hq hX hR hs h1 h2 h3
  rw [pow_zero, mul_one] at hterm
  have hsq := two_mul_sqrt_le hterm
  rw [mul_assoc] at hsq
  have hrest := rest_le (c := c) (CD := CD) hL hk hR 1 (by norm_num)
  rw [pow_one] at hrest
  have hsplit : c * loadSym CD k (Lq q) (rowBCap C .sym r s q) =
      X * Nat.sqrt (rowBCap C .sym r s q) +
        (c * CD ^ 2 * (k + Lq q) ^ 2 * (1 + Lq q) + c * CD * k + c * CD * Lq q ^ 2) := by
    rw [hXdef]; unfold loadSym sqrtUp; ring
  rw [hsplit]
  omega

/-- The `THR` load at one width: `c·Ψ_T ≤ q`. -/
theorem thr_load_le (C : CapParams) {CD c c1 Csp r s q k : ℕ} (hq : 1 ≤ q) (hk : k ≤ r * Lq q)
    (hR : r + 1 ≤ c1 * Lq q) (hs : s ^ 8 ≤ Csp * Lq q ^ 3)
    (h1 : 2 * (8 ^ 32 * (c * CD ^ 2) ^ 64 * 2 ^ 32 * (2 ^ 80 * Csp ^ 4 * C.coef .thr ^ 32 * C.betaInv ^ 32)) *
      (r + 1) ^ 176 ≤ Lq q ^ 2)
    (h2 : 2 * (8 ^ 32 * (c * CD ^ 2) ^ 64 * 2 ^ 33) * c1 ^ 128 * Lq q ^ 288 ≤ q)
    (h3 : 8 * ((c * CD ^ 2) * c1 ^ 2) ^ 2 * (1 + 32 * c1 ^ 3 * C.Cpar ^ 2 * C.betaInv ^ 2) * Lq q ^ 12 ≤ q)
    (h4 : 2 * ((2 * c * CD ^ 2 * c1 ^ 2 + c * CD * c1 + c * CD) * Lq q ^ 7) ≤ q) :
    c * loadThr CD k (Lq q) (rowBCap C .thr r s q) ≤ q := by
  have hL := Lq_pos q
  set X := c * CD ^ 2 * (k + Lq q) ^ 2 with hXdef
  have hX : X ≤ (c * CD ^ 2) * (r + 1) ^ 2 * Lq q ^ 2 := by
    calc X = (c * CD ^ 2) * (k + Lq q) ^ 2 := by rw [hXdef]
      _ ≤ (c * CD ^ 2) * ((r + 1) ^ 2 * Lq q ^ 2) := Nat.mul_le_mul_left _ (kL_sq_le hk)
      _ = (c * CD ^ 2) * (r + 1) ^ 2 * Lq q ^ 2 := by ring
  have hterm := cap_term_le C .thr 1 (by norm_num) (by rw [capExp32_thr]) hq hX hR hs h1 h2 h3
  rw [pow_one] at hterm
  have hsq := two_mul_sqrt_le hterm
  rw [mul_assoc] at hsq
  have hrest := rest_le (c := c) (CD := CD) hL hk hR 2 le_rfl
  have hsplit : c * loadThr CD k (Lq q) (rowBCap C .thr r s q) =
      X * Nat.sqrt (rowBCap C .thr r s q * Lq q) +
        (c * CD ^ 2 * (k + Lq q) ^ 2 * (1 + Lq q ^ 2) + c * CD * k + c * CD * Lq q ^ 2) := by
    rw [hXdef]; unfold loadThr sqrtUp; ring
  rw [hsplit]
  omega

theorem aux_load_le {CD c c1 r q k : ℕ} (hk : k ≤ r * Lq q) (hR : r + 1 ≤ c1 * Lq q)
    (h5 : 2 * (c * CD * (c1 + 1) ^ 2 * Lq q ^ 7) ≤ q) : c * loadAux CD k (Lq q) ≤ q := by
  have hL := Lq_pos q
  set L := Lq q
  have hk' : k ≤ c1 * L ^ 2 := by
    calc k ≤ r * L := hk
      _ ≤ (c1 * L) * L := Nat.mul_le_mul_right _ (by omega)
      _ = c1 * L ^ 2 := by ring
  have hkL : k + L ≤ c1 * L ^ 2 := by
    calc k + L ≤ (r + 1) * L := by nlinarith
      _ ≤ (c1 * L) * L := Nat.mul_le_mul_right _ hR
      _ = c1 * L ^ 2 := by ring
  have hL23 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right hL (by norm_num)
  have hL27 : L ^ 2 ≤ L ^ 7 := Nat.pow_le_pow_right hL (by norm_num)
  calc c * loadAux CD k L = c * CD * (k + L ^ 2 + (k + L ^ 3) * L ^ 2 * (k + L)) := by unfold loadAux; ring
    _ ≤ c * CD * (c1 * L ^ 2 + L ^ 2 + (c1 * L ^ 2 + L ^ 3) * L ^ 2 * (c1 * L ^ 2)) := by gcongr
    _ ≤ c * CD * ((c1 + 1) * L ^ 7 + ((c1 + 1) * L ^ 3) * L ^ 2 * (c1 * L ^ 2)) := by
        gcongr
        · calc c1 * L ^ 2 + L ^ 2 = (c1 + 1) * L ^ 2 := by ring
            _ ≤ (c1 + 1) * L ^ 7 := Nat.mul_le_mul_left _ hL27
        · calc c1 * L ^ 2 + L ^ 3 ≤ c1 * L ^ 3 + L ^ 3 := by gcongr
            _ = (c1 + 1) * L ^ 3 := by ring
    _ = c * CD * ((c1 + 1) * L ^ 7 + (c1 + 1) * c1 * L ^ 7) := by ring
    _ ≤ c * CD * ((c1 + 1) * L ^ 7 + (c1 + 1) * (c1 + 1) * L ^ 7) := by gcongr; omega
    _ = c * CD * (c1 + 1) * (c1 + 2) * L ^ 7 := by ring
    _ ≤ q := by
        have : c * CD * (c1 + 1) * (c1 + 2) * L ^ 7 ≤ c * CD * (c1 + 1) ^ 2 * L ^ 7 * 2 := by
          have : c1 + 2 ≤ 2 * (c1 + 1) := by omega
          calc c * CD * (c1 + 1) * (c1 + 2) * L ^ 7 ≤ c * CD * (c1 + 1) * (2 * (c1 + 1)) * L ^ 7 := by gcongr
            _ = c * CD * (c1 + 1) ^ 2 * L ^ 7 * 2 := by ring
        omega

/-- `c·max{a, b} ≤ q` from both. -/
theorem mul_max_le {c a b q : ℕ} (ha : c * a ≤ q) (hb : c * b ≤ q) : c * max a b ≤ q := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

theorem eventually_load_le (C : CapParams) (CD cr Csp : ℕ) (sp : ℕ → ℕ)
    (hsp : ∀ q, sp q ^ 8 ≤ Csp * Lq q ^ 3) (c : ℕ) :
    ∀ᶠ q : ℕ in atTop, c * loadPsi CD (starWidth (rowBr cr q) q) (Lq q)
      (rowBCap C .thr (rowBr cr q) (sp q) q) (rowBCap C .sym (rowBr cr q) (sp q) q) ≤ q := by
  filter_upwards [
    eventually_rowBr_pow_le cr (2 * (8 ^ 32 * (c * CD ^ 2) ^ 64 * 2 ^ 32 *
      (2 ^ 80 * Csp ^ 4 * C.coef .thr ^ 32 * C.betaInv ^ 32))),
    eventually_rowBr_pow_le cr (2 * (8 ^ 32 * (c * CD ^ 2) ^ 64 * 2 ^ 32 *
      (2 ^ 80 * Csp ^ 4 * C.coef .sym ^ 32 * C.betaInv ^ 32))),
    eventually_mul_Lq_pow_le (2 * (8 ^ 32 * (c * CD ^ 2) ^ 64 * 2 ^ 33) * (2 * cr + 3) ^ 128) 288,
    eventually_mul_Lq_pow_le (8 * ((c * CD ^ 2) * (2 * cr + 3) ^ 2) ^ 2 *
      (1 + 32 * (2 * cr + 3) ^ 3 * C.Cpar ^ 2 * C.betaInv ^ 2)) 12,
    eventually_mul_Lq_pow_le (2 * (2 * c * CD ^ 2 * (2 * cr + 3) ^ 2 + c * CD * (2 * cr + 3) + c * CD)) 7,
    eventually_mul_Lq_pow_le (2 * (c * CD * ((2 * cr + 3) + 1) ^ 2)) 7,
    eventually_ge_atTop 1] with q h1T h1S h2 h3 h4 h5 hq
  have hk := starWidth_le (rowBr cr q) q
  have hR := rowBr_succ_le cr q
  have h4' : 2 * ((2 * c * CD ^ 2 * (2 * cr + 3) ^ 2 + c * CD * (2 * cr + 3) + c * CD) * Lq q ^ 7) ≤ q := by
    rw [← mul_assoc]; exact h4
  have h5' : 2 * (c * CD * ((2 * cr + 3) + 1) ^ 2 * Lq q ^ 7) ≤ q := by rw [← mul_assoc]; exact h5
  have hT := thr_load_le C hq hk hR (hsp q) h1T h2 h3 h4'
  have hS := sym_load_le C hq hk hR (hsp q) h1S h2 h3 h4'
  have hA := aux_load_le (c := c) (CD := CD) hk hR h5'
  unfold loadPsi
  exact mul_max_le hT (mul_max_le hS hA)

end NearCubicWires.WireExponent3_5.Ledger
