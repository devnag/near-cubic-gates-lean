import Proof.Wire_3_5.LedgerLoad
import Proof.Wire_3_5.LedgerWidth

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost Filter

/-! ## The star width grows faster than every fixed multiple of `L` -/

/-- `q < r·2^{s+1}` with `s = ⌊log₂(q/r+1)⌋`. -/
theorem lt_r_mul_two_pow (q r : ℕ) (hr : 0 < r) : q < r * 2 ^ (Nat.log 2 (q / r + 1) + 1) := by
  have h1 : q < r * (q / r + 1) := by
    have := Nat.lt_mul_div_succ q hr; simpa [Nat.mul_comm] using this
  have h2 : q / r + 1 < 2 ^ (Nat.log 2 (q / r + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  calc q < r * (q / r + 1) := h1
    _ ≤ r * 2 ^ (Nat.log 2 (q / r + 1) + 1) := Nat.mul_le_mul_left _ h2.le

theorem eventually_starWidth_ge (cr A : ℕ) (hcr : 1 ≤ cr) :
    ∀ᶠ q : ℕ in atTop, A * Lq q ≤ starWidth (rowBr cr q) q := by
  -- `log₂ r + 4 ≤ L/2` and `4A ≤ r`, eventually
  have hμ : ∀ᶠ q : ℕ in atTop, 2 * (2 * Nat.log 2 (Lq q) + (2 * cr + 4)) ^ 1 ≤ 2 ^ Nat.log 2 (Lq q) :=
    tendsto_log_Lq.eventually (eventually_mul_affine_pow_le_two_pow 2 2 (2 * cr + 4) 1)
  have hA : ∀ᶠ q : ℕ in atTop, 2 * A ≤ Nat.log 2 (Lq q) := tendsto_log_Lq.eventually (eventually_ge_atTop _)
  filter_upwards [hμ, hA, eventually_ge_atTop 2] with q h1 h2 hq
  set L := Lq q
  set r := rowBr cr q
  set s := Nat.log 2 (q / r + 1)
  have hL : 1 ≤ L := Lq_pos q
  have hr : 2 ≤ r := two_le_rowBr hcr q
  have hrdef : r = 2 * (Nat.log 2 L + cr) := rfl
  have h2L : 2 ^ Nat.log 2 L ≤ L := Nat.pow_log_le_self 2 (by omega)
  -- 2^{L−2} ≤ q
  have hq2 : 2 ^ (L - 1) < q + 2 := two_pow_pred_Lq_lt q
  -- q < r·2^{s+1} ≤ 2^{log r + 1}·2^{s+1}
  have hqr : q < r * 2 ^ (s + 1) := lt_r_mul_two_pow q r (by omega)
  have hrlog : r < 2 ^ (Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self (by norm_num) r
  have hlogr : Nat.log 2 r ≤ r := Nat.log_le_self 2 r
  -- r + 4 ≤ L/2
  have hr4 : 2 * (r + 4) ≤ L := by rw [hrdef]; simp only [pow_one] at h1; omega
  -- L − 1 < log r + s + 3, i.e. s is at least about L/2
  have hexp : 2 ^ (L - 1) < 2 ^ (Nat.log 2 r + 1 + (s + 1) + 1) := by
    calc 2 ^ (L - 1) < q + 2 := hq2
      _ ≤ 2 * q := by omega
      _ < 2 * (r * 2 ^ (s + 1)) := by omega
      _ ≤ 2 * (2 ^ (Nat.log 2 r + 1) * 2 ^ (s + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hrlog.le)
      _ = 2 ^ (Nat.log 2 r + 1 + (s + 1) + 1) := by rw [pow_add, pow_add, pow_one]; ring
  have hLs : L - 1 < Nat.log 2 r + 1 + (s + 1) + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hexp
  have hs : L ≤ 2 * s + 1 := by omega
  have h4A : 4 * A ≤ r := by rw [hrdef]; omega
  have hs1 : 1 ≤ s := by omega
  show A * L ≤ r * s
  calc A * L ≤ A * (2 * s + 1) := Nat.mul_le_mul_left _ hs
    _ = 2 * A * s + A := by ring
    _ ≤ 2 * A * s + 2 * A * s := by
        have : A ≤ 2 * A * s := by
          calc A ≤ A * s := Nat.le_mul_of_pos_right A hs1
            _ ≤ 2 * A * s := Nat.mul_le_mul_right _ (by omega)
        omega
    _ = (4 * A) * s := by ring
    _ ≤ r * s := Nat.mul_le_mul_right _ h4A

/-! ## The fit conditions, eventually -/

theorem eventually_fits (E : Envelope) (C : CapParams) (CD cr Csp : ℕ) (hcr : 1 ≤ cr) (sp : ℕ → ℕ)
    (hsp : ∀ q, sp q ^ 8 ≤ Csp * Lq q ^ 3) :
    ∀ᶠ q : ℕ in atTop, Fits E q (Nat.clog 2 q) (starWidth (rowBr cr q) q)
      (loadPsi CD (starWidth (rowBr cr q) q) (Lq q)
        (rowBCap C .thr (rowBr cr q) (sp q) q) (rowBCap C .sym (rowBr cr q) (sp q) q)) := by
  filter_upwards [
    eventually_starWidth_ge cr (4 * (E.Amain + E.callDeg + E.sigma)) hcr,
    eventually_starWidth_ge cr (E.Atable + E.callDeg + E.sigma) hcr,
    eventually_mul_Lq_pow_le (2 * cr + 3) 2,
    eventually_mul_Lq_pow_le (2 * (E.csel * (2 * cr + 3) + (E.Asel + E.callDeg + E.sigma))) 2,
    eventually_load_le C CD cr Csp sp hsp (2 * E.cpsi),
    eventually_mul_Lq_pow_le (2 * (E.Apre + E.callDeg + E.sigma)) 1] with q hmain htab hkq hsel hpre hpre2
  set L := Lq q
  set r := rowBr cr q
  set k := starWidth r q
  have hL : 1 ≤ L := Lq_pos q
  have hcl : Nat.clog 2 q ≤ L := Nat.clog_mono_right 2 (by omega)
  have hkr : k ≤ r * L := starWidth_le r q
  have hR : r + 1 ≤ (2 * cr + 3) * L := rowBr_succ_le cr q
  have hkL : k ≤ (2 * cr + 3) * L ^ 2 := by
    calc k ≤ r * L := hkr
      _ ≤ ((2 * cr + 3) * L) * L := Nat.mul_le_mul_right _ (by omega)
      _ = (2 * cr + 3) * L ^ 2 := by ring
  have hLL : L ≤ L ^ 2 := Nat.le_self_pow (by norm_num) L
  refine ⟨Nat.le_pow_clog (by norm_num) q, ?_, ?_, ?_, ?_, ?_⟩
  · -- main: (Amain+callDeg+σ)·lg ≤ k/4
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    calc (E.Amain + E.callDeg + E.sigma) * Nat.clog 2 q * 4 ≤ (E.Amain + E.callDeg + E.sigma) * L * 4 := by
          gcongr
      _ = 4 * (E.Amain + E.callDeg + E.sigma) * L := by ring
      _ ≤ k := hmain
  · -- table
    calc (E.Atable + E.callDeg + E.sigma) * Nat.clog 2 q ≤ (E.Atable + E.callDeg + E.sigma) * L := by gcongr
      _ ≤ k := htab
  · -- k ≤ q
    exact hkL.trans hkq
  · -- sel: csel·k + (Asel+callDeg+σ)·lg ≤ q − q/2
    have h1 : E.csel * k ≤ E.csel * (2 * cr + 3) * L ^ 2 := by
      calc E.csel * k ≤ E.csel * ((2 * cr + 3) * L ^ 2) := Nat.mul_le_mul_left _ hkL
        _ = E.csel * (2 * cr + 3) * L ^ 2 := by ring
    have h2 : (E.Asel + E.callDeg + E.sigma) * Nat.clog 2 q ≤ (E.Asel + E.callDeg + E.sigma) * L ^ 2 := by
      calc (E.Asel + E.callDeg + E.sigma) * Nat.clog 2 q ≤ (E.Asel + E.callDeg + E.sigma) * L :=
            Nat.mul_le_mul_left _ hcl
        _ ≤ (E.Asel + E.callDeg + E.sigma) * L ^ 2 := Nat.mul_le_mul_left _ hLL
    have h3 : 2 * (E.csel * (2 * cr + 3) + (E.Asel + E.callDeg + E.sigma)) * L ^ 2 =
        2 * (E.csel * (2 * cr + 3) * L ^ 2 + (E.Asel + E.callDeg + E.sigma) * L ^ 2) := by ring
    omega
  · -- pre: cpsi·Ψ + (Apre+callDeg+σ)·lg ≤ q
    have h2 : (E.Apre + E.callDeg + E.sigma) * Nat.clog 2 q ≤ (E.Apre + E.callDeg + E.sigma) * L ^ 1 := by
      rw [pow_one]; exact Nat.mul_le_mul_left _ hcl
    have h3 : 2 * E.cpsi * loadPsi CD k L (rowBCap C .thr r (sp q) q) (rowBCap C .sym r (sp q) q) =
        2 * (E.cpsi * loadPsi CD k L (rowBCap C .thr r (sp q) q) (rowBCap C .sym r (sp q) q)) := by ring
    have h4 : 2 * (E.Apre + E.callDeg + E.sigma) * L ^ 1 = 2 * ((E.Apre + E.callDeg + E.sigma) * L ^ 1) := by ring
    omega

/-! ## The ledger -/

structure RowBParams where
  cap : CapParams
  CD : ℕ
  cr : ℕ
  cr_pos : 1 ≤ cr
  Csp : ℕ
  sp : ℕ → ℕ
  sp_le : ∀ q, sp q ^ 8 ≤ Csp * Lq q ^ 3

structure WidthData (kclk : ℕ) (E : Envelope) where
  q : ℕ → ℕ
  growth : ∀ m, ∃ onset, ∀ N, onset ≤ N → m ≤ q N
  Ctab : ℕ
  d : ℕ
  hsigma : d + 1 ≤ E.sigma
  tableOnset : ℕ
  table : ∀ N, tableOnset ≤ N → 2 ^ q N ≤ Ctab * N ^ (kclk + 2) * q N ^ d
  A : ℕ
  a : ℕ
  ha : a ≤ kclk + 1

/-- The fits hold at every `q(N)` past some onset. -/
theorem WidthData.fits_onset {kclk : ℕ} {E : Envelope} (W : WidthData kclk E) (P : RowBParams) :
    ∃ onset : ℕ, ∀ N, onset ≤ N → Fits E (W.q N) (Nat.clog 2 (W.q N)) (starWidth (rowBr P.cr (W.q N)) (W.q N))
      (loadPsi P.CD (starWidth (rowBr P.cr (W.q N)) (W.q N)) (Lq (W.q N))
        (rowBCap P.cap .thr (rowBr P.cr (W.q N)) (P.sp (W.q N)) (W.q N))
        (rowBCap P.cap .sym (rowBr P.cr (W.q N)) (P.sp (W.q N)) (W.q N))) :=
  eventually_atTop.1 ((tendsto_atTop_atTop.2 W.growth).eventually
    (Ledger.eventually_fits E P.cap P.CD P.cr P.Csp P.cr_pos P.sp P.sp_le))

noncomputable def rowBBudget {kclk : ℕ} (E : Envelope) (costs : ComponentCosts E) (P : RowBParams)
    (W : WidthData kclk E) : TimeBudget kclk E where
  q := W.q
  lg := Nat.clog 2
  rOf := rowBr P.cr
  capOf := fun m q => rowBCap P.cap m (rowBr P.cr q) (P.sp q) q
  capOf_pos := fun m _ => one_le_rowBCap P.cap m _ _ _
  CD := P.CD
  costs := costs
  A := W.A
  a := W.a
  ha := W.ha
  Ctab := W.Ctab
  d := W.d
  hsigma := W.hsigma
  growth := W.growth
  onset := max W.tableOnset (Classical.choose (W.fits_onset P))
  table := fun N hN => W.table N (le_of_max_le_left hN)
  fits := fun N hN => Classical.choose_spec (W.fits_onset P) N (le_of_max_le_right hN)

theorem rowBBudget_rOf {kclk : ℕ} (E : Envelope) (costs : ComponentCosts E) (P : RowBParams)
    (W : WidthData kclk E) (q : ℕ) : (rowBBudget E costs P W).rOf q = rowBr P.cr q := rfl

/-- The ledger's star width is `r(q)·⌊log₂(q/r(q)+1)⌋`. -/
theorem rowBBudget_kOf {kclk : ℕ} (E : Envelope) (costs : ComponentCosts E) (P : RowBParams)
    (W : WidthData kclk E) (q : ℕ) : (rowBBudget E costs P W).kOf q = starWidth (rowBr P.cr q) q := rfl

/-- The ledger's load is the paper's `max{Ψ_T(B_T), Ψ_S(B_S), Ψ_aux}` at the row-B parameters. -/
theorem rowBBudget_psiOf {kclk : ℕ} (E : Envelope) (costs : ComponentCosts E) (P : RowBParams)
    (W : WidthData kclk E) (q : ℕ) :
    (rowBBudget E costs P W).psiOf q = loadPsi P.CD (starWidth (rowBr P.cr q) q) (Lq q)
      (rowBCap P.cap .thr (rowBr P.cr q) (P.sp q) q) (rowBCap P.cap .sym (rowBr P.cr q) (P.sp q) q) := rfl

/-- The ledger's caps are the per-mode `B_i(q)` of `tr:B`. -/
theorem rowBBudget_capOf {kclk : ℕ} (E : Envelope) (costs : ComponentCosts E) (P : RowBParams)
    (W : WidthData kclk E) (m : Mode) (q : ℕ) :
    (rowBBudget E costs P W).capOf m q = rowBCap P.cap m (rowBr P.cr q) (P.sp q) q := rfl

def nativeWidthData (kclk Apad : ℕ) (E : Envelope) (hσ : Apad + 1 ≤ E.sigma) (A a : ℕ) (ha : a ≤ kclk + 1) :
    WidthData kclk E where
  q := nativeWidth kclk Apad
  growth := nativeWidth_growth kclk Apad
  Ctab := 2 * 12 ^ Apad
  d := Apad
  hsigma := hσ
  tableOnset := 1
  table := fun N hN => nativeWidth_table kclk Apad N hN
  A := A
  a := a
  ha := ha

/-- **The deliverable** (B9): for every envelope `E` with `A_pad + 1 ≤ σ` and every costs record, the row-B
`TimeBudget` on the paper's width. -/
noncomputable def rowBNativeBudget (kclk Apad : ℕ) (E : Envelope) (hσ : Apad + 1 ≤ E.sigma) (costs : ComponentCosts E)
    (P : RowBParams) (A a : ℕ) (ha : a ≤ kclk + 1) : TimeBudget kclk E :=
  rowBBudget E costs P (nativeWidthData kclk Apad E hσ A a ha)

/-- A satisfiable instance of the constants (the sparse count constant; any `s = O(L^{3/8})` works). -/
def satRowBParams : RowBParams where
  cap := ⟨1, 1, 8, 1⟩
  CD := 1
  cr := 1
  cr_pos := le_rfl
  Csp := 1
  sp := fun _ => 1
  sp_le := fun q => by have := Lq_pos q; simp only [one_pow, one_mul]; exact Nat.one_le_pow _ _ this

end NearCubicWires.WireExponent3_5.Ledger
