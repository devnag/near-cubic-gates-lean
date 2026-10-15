import Proof.Gates.WorkerArith.VerdictMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Worker

/-! ## Machine constants -/

/-- `γ − εT = c/e`: `e`, `e + c⁻`, `c⁺`. -/
def cE (γ εT : ℚ) : ℕ := (γ - εT).den
def cA1 (γ εT : ℚ) : ℕ := (γ - εT).den + (-(γ - εT).num).toNat
def cA2 (γ εT : ℚ) : ℕ := (γ - εT).num.toNat
/-- The guard's naturals: `γ < εT·X ⟺ gA + gB·X < gC + gD·X`. -/
def gA (γ εT : ℚ) : ℕ := (γ.num * εT.den).toNat
def gB (γ εT : ℚ) : ℕ := (-(εT.num * γ.den)).toNat
def gC (γ εT : ℚ) : ℕ := (-(γ.num * εT.den)).toNat
def gD (γ εT : ℚ) : ℕ := (εT.num * γ.den).toNat
/-- The width slack. -/
def kC (γ εT : ℚ) : ℕ := cA1 γ εT + cE γ εT + cA2 γ εT + cE γ εT + gA γ εT + gB γ εT + gC γ εT + gD γ εT + 4

/-- The verdict program. -/
def verdictP (γ εT : ℚ) : WMX 29 16 :=
  .seq (setupP (kC γ εT)) (.seq (BinW.one 9 4 0 1) (.seq pow2P (.seq (zread 4) (.seq (zread 5) (.seq (zread 6)
    (.seq (zread 7) (.seq (zread 8) (.seq (zread 13) (.seq counterP (.seq gloop
      (.seq (fin (cA1 γ εT) (cE γ εT) (cA2 γ εT) (cE γ εT)) (.seq g1 (.seq g2 (.seq g3
        (.seq (g4 (gA γ εT) (gB γ εT) (gC γ εT) (gD γ εT)) outP)))))))))))))))

/-! ## Size bounds -/

theorem lt_two_pow_self' (k : ℕ) : k < 2 ^ k := Nat.lt_two_pow_self

theorem lin_bound (a b y z S Q T : ℕ) (hy : y ≤ S) (hz : z ≤ S) (hab : a + b < Q) (hS : Q * S ≤ T) (hT : 0 < T) :
    a * y + b * z < T := by
  rcases Nat.eq_zero_or_pos S with h0 | hpos
  · subst h0; have : y = 0 := by omega
    have : z = 0 := by omega
    subst_vars; simpa using hT
  · calc a * y + b * z ≤ a * S + b * S := Nat.add_le_add (Nat.mul_le_mul_left _ hy) (Nat.mul_le_mul_left _ hz)
      _ = (a + b) * S := by ring
      _ < Q * S := Nat.mul_lt_mul_of_pos_right hab hpos
      _ ≤ T := hS

theorem posC_le (D : ℕ) (f : Bool) (x : ℚ) : posC D f x ≤ mag D x := by unfold posC; split_ifs <;> omega
theorem negC_le (D : ℕ) (f : Bool) (x : ℚ) : negC D f x ≤ mag D x := by unfold negC; split_ifs <;> omega

theorem mag_le (L : ℕ) (x : ℚ) (hn : x.num.natAbs < 2 ^ L) : mag (2 ^ L) x ≤ 2 ^ L * 2 ^ L := by
  unfold mag
  exact Nat.mul_le_mul hn.le (Nat.div_le_self _ _)

theorem posT_le (r : VerdictReq) (i : ℕ) (hi : i < r.I.length) (fs : Bool) :
    posT (2 ^ (verdictWord r).length) fs (r.I.getD i dT) ≤ 3 * (2 ^ (verdictWord r).length * 2 ^ (verdictWord r).length) := by
  set L := (verdictWord r).length
  have h1 := mag_le L (r.I.getD i dT).2.1 (field_lt r (mem_nats_term r i 2 hi (by norm_num)))
  have h2 := mag_le L (r.I.getD i dT).2.2 (field_lt r (mem_nats_term r i 5 hi (by norm_num)))
  have h3 := posC_le (2 ^ L) (xor fs (r.I.getD i dT).1) (r.I.getD i dT).2.1
  have h4 := posC_le (2 ^ L) false (r.I.getD i dT).2.2
  have h5 : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_left _ (by positivity)
  unfold posT
  split_ifs <;> omega

theorem negT_le (r : VerdictReq) (i : ℕ) (hi : i < r.I.length) (fs : Bool) :
    negT (2 ^ (verdictWord r).length) fs (r.I.getD i dT) ≤ 3 * (2 ^ (verdictWord r).length * 2 ^ (verdictWord r).length) := by
  set L := (verdictWord r).length
  have h1 := mag_le L (r.I.getD i dT).2.1 (field_lt r (mem_nats_term r i 2 hi (by norm_num)))
  have h2 := mag_le L (r.I.getD i dT).2.2 (field_lt r (mem_nats_term r i 5 hi (by norm_num)))
  have h3 := negC_le (2 ^ L) (xor fs (r.I.getD i dT).1) (r.I.getD i dT).2.1
  have h4 := negC_le (2 ^ L) false (r.I.getD i dT).2.2
  have h5 : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_left _ (by positivity)
  unfold negT
  split_ifs <;> omega

/-- `POS ≤ L·4^L`. -/
theorem posS_le (r : VerdictReq) :
    posS (2 ^ (verdictWord r).length) r.I r.I.length ≤
      (verdictWord r).length * (2 ^ (verdictWord r).length * 2 ^ (verdictWord r).length) := by
  set L := (verdictWord r).length
  have hs : posS (2 ^ L) r.I r.I.length ≤ r.I.length * (3 * (2 ^ L * 2 ^ L)) := by
    unfold posS
    calc ∑ i ∈ Finset.range r.I.length, posT (2 ^ L) (fsOf i) (r.I.getD i dT)
        ≤ ∑ _i ∈ Finset.range r.I.length, 3 * (2 ^ L * 2 ^ L) :=
          Finset.sum_le_sum (fun i hi => posT_le r i (Finset.mem_range.1 hi) _)
      _ = r.I.length * (3 * (2 ^ L * 2 ^ L)) := by simp
  have hl := len_ge r
  calc posS (2 ^ L) r.I r.I.length ≤ r.I.length * (3 * (2 ^ L * 2 ^ L)) := hs
    _ = (3 * r.I.length) * (2 ^ L * 2 ^ L) := by ring
    _ ≤ L * (2 ^ L * 2 ^ L) := Nat.mul_le_mul_right _ (by omega)

theorem negS_le (r : VerdictReq) :
    negS (2 ^ (verdictWord r).length) r.I r.I.length ≤
      (verdictWord r).length * (2 ^ (verdictWord r).length * 2 ^ (verdictWord r).length) := by
  set L := (verdictWord r).length
  have hs : negS (2 ^ L) r.I r.I.length ≤ r.I.length * (3 * (2 ^ L * 2 ^ L)) := by
    unfold negS
    calc ∑ i ∈ Finset.range r.I.length, negT (2 ^ L) (fsOf i) (r.I.getD i dT)
        ≤ ∑ _i ∈ Finset.range r.I.length, 3 * (2 ^ L * 2 ^ L) :=
          Finset.sum_le_sum (fun i hi => negT_le r i (Finset.mem_range.1 hi) _)
      _ = r.I.length * (3 * (2 ^ L * 2 ^ L)) := by simp
  have hl := len_ge r
  calc negS (2 ^ L) r.I r.I.length ≤ r.I.length * (3 * (2 ^ L * 2 ^ L)) := hs
    _ = (3 * r.I.length) * (2 ^ L * 2 ^ L) := by ring
    _ ≤ L * (2 ^ L * 2 ^ L) := Nat.mul_le_mul_right _ (by omega)

/-- `L·4^L ≤ 2^{10L}`, `2^W = 2^{10L}·2^K`. -/
theorem cube_le (L : ℕ) : L * (2 ^ L * 2 ^ L) ≤ 2 ^ (10 * L) := by
  have h1 : L ≤ 2 ^ L := (lt_two_pow_self' L).le
  calc L * (2 ^ L * 2 ^ L) ≤ 2 ^ L * (2 ^ L * 2 ^ L) := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (3 * L) := by rw [← pow_add, ← pow_add]; ring_nf
    _ ≤ 2 ^ (10 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ## Reading the bad count -/

theorem bitWord_eq (b : Bool) : NearCubicGates.Close.Interfaces.bitWord b = [true, false, b] := by
  cases b <;> rfl

/-- **The output bit is the verdict bit.** -/
theorem bad_verdict (γ εT : ℚ) (r : VerdictReq) :
    decide (0 + (!decide (cA1 γ εT * (2 * (max r.M 1 * 2 ^ (verdictWord r).length)) +
        cE γ εT * posS (2 ^ (verdictWord r).length) r.I r.I.length <
        cA2 γ εT * (2 * (max r.M 1 * 2 ^ (verdictWord r).length)) +
        cE γ εT * negS (2 ^ (verdictWord r).length) r.I r.I.length)).toNat +
      (decide (r.cl < r.rb)).toNat + (decide (r.q < 2)).toNat + (decide (r.N = 0)).toNat +
      (!decide (gA γ εT + gB γ εT * r.N ^ 10 < gC γ εT + gD γ εT * r.N ^ 10)).toNat = 0) = verdictBit γ εT r := by
  have hU := upper_test γ εT r.M r.I r.hlen (2 ^ (verdictWord r).length) (by positivity)
    (fun x hx => by
      obtain ⟨i, hi, rfl⟩ : ∃ i, ∃ hi : i < r.I.length, r.I[i] = x := List.getElem_of_mem hx
      have := term_dvd r i hi
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this)
  have hG := guard_test γ εT (r.N ^ 10)
  rw [← r.hlen] at hU
  unfold verdictBit
  apply decide_eq_decide.mpr
  simp only [Nat.zero_add, Nat.add_eq_zero_iff, Bool.toNat_eq_zero, Bool.not_eq_false', decide_eq_true_eq,
    decide_eq_false_iff_not, not_lt]
  rw [show ((r.N : ℚ) ^ 10) = ((r.N ^ 10 : ℕ) : ℚ) by push_cast; rfl, hU, hG]
  unfold cA1 cA2 cE gA gB gC gD
  rw [show (max r.M 1 * 2 ^ (verdictWord r).length) = max r.M 1 * 2 ^ (verdictWord r).length from rfl]
  simp only [mul_assoc]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h2, h3, by omega, h5, h1⟩
  · rintro ⟨h2, h3, h4, h5, h1⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, by omega⟩, h5⟩

/-! ## The run -/

/-- The composed cost, with the products abstracted. -/
theorem cost_core (W b s c P1 P2 P3 P5 : ℕ) (hW : W + 1 ≤ s) (hsc : s ≤ c) (hb : b ≤ 5) (h1 : P1 ≤ 33004 * c)
    (h2 : P2 ≤ 51 * P5 + 7000 * c) (h3 : P3 ≤ 51 * P5 + 7000 * c) :
    2000 * s + 1 + (50 * s + 1 + (100 * s + 1 + (140 * s + 1 + (140 * s + 1 + (140 * s + 1 + (140 * s + 1 +
      (140 * s + 1 + (140 * s + 1 + (200 * s + 1 + (P1 + 1 + 1 + (P2 + 1 + (60 * s + 1 + (300 * s + 1 +
        (60 * s + 1 + (P3 + 1 + (20 * W + 3 * b + 60)))))))))))))))) ≤ 60000 * c + 200 * P5 := by
  linarith

/-- The cost of the composed run, as a class bound. -/
theorem cost_le (W K M b a1 a2 a3 a4 c1 c2 c3 c4 : ℕ) (hM : M ≤ W + 1) (ha : a1 + a2 + a3 + a4 ≤ K)
    (hc : c1 + c2 + c3 + c4 ≤ K) (hb : b ≤ 5) :
    2000 * (W + 1) ^ 2 + 1 +
      (50 * (W + 1) ^ 2 + 1 +
        (100 * (W + 1) ^ 2 + 1 +
          (140 * (W + 1) ^ 2 + 1 +
            (140 * (W + 1) ^ 2 + 1 +
              (140 * (W + 1) ^ 2 + 1 +
                (140 * (W + 1) ^ 2 + 1 +
                  (140 * (W + 1) ^ 2 + 1 +
                    (140 * (W + 1) ^ 2 + 1 +
                      (200 * (W + 1) ^ 2 + 1 +
                        (M * (33000 * (W + 1) ^ 2 + 4) + 1 + 1 +
                          ((51 * (a1 + a2 + a3 + a4) + 7000) * (W + 1) ^ 2 + 1 +
                            (60 * (W + 1) ^ 2 + 1 +
                              (300 * (W + 1) ^ 2 + 1 +
                                (60 * (W + 1) ^ 2 + 1 +
                                  ((51 * (c1 + c2 + c3 + c4) + 7000) * (W + 1) ^ 2 + 1 +
                                    (20 * W + 3 * b + 60)))))))))))))))) ≤
    60000 * (W + 1) ^ 3 + 200 * (K * (W + 1) ^ 3) := by
  have hsc : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hW1s : W + 1 ≤ (W + 1) ^ 2 := one_le_sq W
  have hMc3 : M * (33000 * (W + 1) ^ 2 + 4) ≤ 33004 * (W + 1) ^ 3 := by
    calc M * (33000 * (W + 1) ^ 2 + 4) ≤ (W + 1) * (33004 * (W + 1) ^ 2) := Nat.mul_le_mul hM (by omega)
      _ = 33004 * (W + 1) ^ 3 := by ring
  have hK3 : (51 * K + 7000) * (W + 1) ^ 3 = 51 * (K * (W + 1) ^ 3) + 7000 * (W + 1) ^ 3 := by ring
  have h1 : (51 * (a1 + a2 + a3 + a4) + 7000) * (W + 1) ^ 2 ≤ 51 * (K * (W + 1) ^ 3) + 7000 * (W + 1) ^ 3 :=
    by rw [← hK3]; exact Nat.mul_le_mul (by omega) hsc
  have h2 : (51 * (c1 + c2 + c3 + c4) + 7000) * (W + 1) ^ 2 ≤ 51 * (K * (W + 1) ^ 3) + 7000 * (W + 1) ^ 3 :=
    by rw [← hK3]; exact Nat.mul_le_mul (by omega) hsc
  exact cost_core W b _ _ _ _ _ _ hW1s hsc hb hMc3 h1 h2

/-- The width. -/
def widthW (γ εT : ℚ) (r : VerdictReq) : ℕ := 10 * (verdictWord r).length + kC γ εT

/-- The register capacity. -/
def capW (γ εT : ℚ) (r : VerdictReq) : ℕ := 4 * widthW γ εT r + 4

/-- The budget. -/
def budgetW (γ εT : ℚ) (r : VerdictReq) : ℕ := (60000 + 200 * kC γ εT) * (widthW γ εT r + 1) ^ 3

theorem verdictRuns (γ εT : ℚ) (r : VerdictReq) :
    ∃ τ : WState 29 16, WXExec (capW γ εT r) (verdictP γ εT)
      (NearCubicGates.Close.Interfaces.startState 29 16 (verdictWord r)) τ (budgetW γ εT r) ∧
      τ.st 1 = NearCubicGates.Close.Interfaces.bitWord (verdictBit γ εT r) ∧ (∀ i, τ.sh i = 0) ∧ ∀ q, τ.val q = 0 := by
  set w := verdictWord r with hw
  set L := w.length with hL
  set K := kC γ εT with hK
  set W := widthW γ εT r with hW
  set cap := capW γ εT r with hcapdef
  have hWdef : W = 10 * L + K := rfl
  have hl : 21 * r.I.length + 6 ≤ L := len_ge r
  have hK4 : 4 ≤ K := by simp [hK, kC]
  have hLW : L ≤ W := by omega
  have hW1 : 1 ≤ W := by omega
  have hcap : 4 * W + 4 ≤ cap := le_rfl
  have hcap2 : 2 * W + 1 ≤ cap := by omega
  have hM : 10 * r.M = r.I.length := r.hlen.symm
  have hML : r.M ≤ L := by omega
  have hP2 : 2 ^ W = 2 ^ (10 * L) * 2 ^ K := by rw [hWdef, pow_add]
  have hPL : 2 ^ L ≤ 2 ^ (10 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKW : 2 ^ K ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLWp : 2 ^ (10 * L) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKlt := lt_two_pow_self' K
  have hfield : ∀ k < 6, (nats r).getD k 0 < 2 ^ L := fun k hk =>
    field_lt r (getD_mem _ _ (by rw [nats_length]; omega))
  have hfW : ∀ k < 6, (nats r).getD k 0 < 2 ^ W := fun k hk =>
    lt_of_lt_of_le (hfield k hk) (le_trans hPL hLWp)
  have f0 : (nats r).getD 0 0 = r.q := rfl
  have f1 : (nats r).getD 1 0 = r.M := rfl
  have f2 : (nats r).getD 2 0 = r.N := rfl
  have f3 : (nats r).getD 3 0 = r.rb := rfl
  have f4 : (nats r).getD 4 0 = r.cl := rfl
  have hn6 : 6 ≤ (nats r).length := by rw [nats_length]; omega
  -- set-up, ONE, D
  have e0 := setupM w K cap hcap
  have e1 := oneM (w := w) (W := W) (wv := fun _ => 0) (pos := 0) (lp := 0) (bad := 0) cap (X := 9) (Y := 4)
    (by unfold NumS; decide) (by unfold NumS; decide) (by decide) hW1 hcap2
  have e2 := pow2M (w := w) (W := W) (pos := 0) (lp := 0) (bad := 0) cap (Function.update (fun _ => 0) 9 1)
    (by omega) hcap2
  set wv2 := Function.update (Function.update (fun _ : Fin 30 => 0) 9 1) 10 (2 ^ L) with hwv2
  -- the six header fields
  have p0 : pfx r 0 = 0 := by simp [pfx]
  have e3 := zreadF r (W := W) (wv := wv2) (lp := 0) (bad := 0) cap (X := 4) (by unfold NumS; decide) (by decide)
    0 (by omega) hLW hW1 hcap
  rw [p0, f0] at e3
  have e4 := zreadF r (W := W) (wv := Function.update wv2 4 r.q) (lp := 0) (bad := 0) cap (X := 5)
    (by unfold NumS; decide) (by decide) 1 (by omega) hLW hW1 hcap
  rw [f1] at e4
  have e5 := zreadF r (W := W) (wv := Function.update (Function.update wv2 4 r.q) 5 r.M) (lp := 0) (bad := 0) cap
    (X := 6) (by unfold NumS; decide) (by decide) 2 (by omega) hLW hW1 hcap
  rw [f2] at e5
  have e6 := zreadF r (W := W) (wv := Function.update (Function.update (Function.update wv2 4 r.q) 5 r.M) 6 r.N)
    (lp := 0) (bad := 0) cap (X := 7) (by unfold NumS; decide) (by decide) 3 (by omega) hLW hW1 hcap
  rw [f3] at e6
  have e7 := zreadF r (W := W)
    (wv := Function.update (Function.update (Function.update (Function.update wv2 4 r.q) 5 r.M) 6 r.N) 7 r.rb)
    (lp := 0) (bad := 0) cap (X := 8) (by unfold NumS; decide) (by decide) 4 (by omega) hLW hW1 hcap
  rw [f4] at e7
  set wv7 := Function.update (Function.update (Function.update (Function.update (Function.update wv2 4 r.q) 5 r.M)
    6 r.N) 7 r.rb) 8 r.cl with hwv7
  have e8 := zreadF r (W := W) (wv := wv7) (lp := 0) (bad := 0) cap (X := 13) (by unfold NumS; decide) (by decide)
    5 (by omega) hLW hW1 hcap
  set wv8 := Function.update wv7 13 ((nats r).getD 5 0) with hwv8
  -- the gadget counter and the loop
  have m4 : wv8 4 = r.q := by simp [hwv8, hwv7]
  have m5 : wv8 5 = r.M := by simp [hwv8, hwv7]
  have m6 : wv8 6 = r.N := by simp [hwv8, hwv7]
  have m7 : wv8 7 = r.rb := by simp [hwv8, hwv7]
  have m8 : wv8 8 = r.cl := by simp [hwv8, hwv7]
  have m9 : wv8 9 = 1 := by simp [hwv8, hwv7, hwv2]
  have m10 : wv8 10 = 2 ^ L := by simp [hwv8, hwv7, hwv2]
  have m11 : wv8 11 = 0 := by simp [hwv8, hwv7, hwv2]
  have m12 : wv8 12 = 0 := by simp [hwv8, hwv7, hwv2]
  have hqW : r.q < 2 ^ W := by have := hfW 0 (by norm_num); rwa [f0] at this
  have hMW : r.M < 2 ^ W := by have := hfW 1 (by norm_num); rwa [f1] at this
  have hNW : r.N < 2 ^ W := by have := hfW 2 (by norm_num); rwa [f2] at this
  have hrbW : r.rb < 2 ^ W := by have := hfW 3 (by norm_num); rwa [f3] at this
  have hclW : r.cl < 2 ^ W := by have := hfW 4 (by norm_num); rwa [f4] at this
  have hNL : r.N < 2 ^ L := by have := hfield 2 (by norm_num); rwa [f2] at this
  have e9 := counterM (w := w) (W := W) (pos := pfx r 6) (bad := 0) cap wv8 m9 (by rw [m5]; exact hMW)
    (by rw [m5]; omega) hcap
  rw [m5] at e9
  have h10W : 2 ^ (10 * L) < 2 ^ W := by
    rw [hP2]; exact lt_mul_of_one_lt_right (by positivity) (Nat.one_lt_two_pow (by omega))
  have hPb : posS (2 ^ L) r.I r.I.length < 2 ^ W := lt_of_le_of_lt (le_trans (posS_le r) (cube_le L)) h10W
  have hNb : negS (2 ^ L) r.I r.I.length < 2 ^ W := lt_of_le_of_lt (le_trans (negS_le r) (cube_le L)) h10W
  have h3L : 3 * L + 2 ≤ W := by omega
  obtain ⟨wv10, e10, p11', n12', keep10⟩ := gloopM r (W := W) 0 cap h3L hPb hNb hcap (by omega)
    (Function.update wv8 22 0) (by rw [Function.update_of_ne (by decide), m10])
    (by rw [Function.update_of_ne (by decide), m11]) (by rw [Function.update_of_ne (by decide), m12])
  have hpos : pfx r (6 + 70 * r.M) = L := by
    rw [show 6 + 70 * r.M = (nats r).length by rw [nats_length]; omega, pfx_all]
  rw [hpos] at e10
  have p11 : wv10 11 = posS (2 ^ L) r.I r.I.length := p11'
  have n12 : wv10 12 = negS (2 ^ L) r.I r.I.length := n12'
  have k10 : ∀ X : Fin 30, X.val < 11 → wv10 X = wv8 X := fun X hX => by
    rw [keep10 X (Or.inl hX)]; simp [show X ≠ 22 by intro e; subst e; simp at hX]
  -- the acceptance test
  have q5 : wv10 5 = r.M := by rw [k10 5 (by decide), m5]
  have q10 : wv10 10 = 2 ^ L := by rw [k10 10 (by decide), m10]
  have hYb : 2 * (max r.M 1 * 2 ^ L) ≤ L * (2 ^ L * 2 ^ L) := by
    have h1 : max r.M 1 ≤ L := by omega
    have h2 : 2 ≤ 2 ^ L := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 * (max r.M 1 * 2 ^ L) ≤ 2 * (L * 2 ^ L) := by gcongr
      _ = L * (2 * 2 ^ L) := by ring
      _ ≤ L * (2 ^ L * 2 ^ L) := by gcongr
  have hT : L * (2 ^ L * 2 ^ L) * 2 ^ K ≤ 2 ^ W := by rw [hP2]; exact Nat.mul_le_mul_right _ (cube_le L)
  have hKs : cA1 γ εT + cE γ εT + cA2 γ εT + cE γ εT + gA γ εT + gB γ εT + gC γ εT + gD γ εT + 4 = K := rfl
  have hY : 2 * (max r.M 1 * 2 ^ L) < 2 ^ W := lt_of_le_of_lt (le_trans hYb (cube_le L)) h10W
  have hpL : posS (2 ^ L) r.I r.I.length ≤ L * (2 ^ L * 2 ^ L) := posS_le r
  have hnL : negS (2 ^ L) r.I r.I.length ≤ L * (2 ^ L * 2 ^ L) := negS_le r
  have hT' : 2 ^ K * (L * (2 ^ L * 2 ^ L)) ≤ 2 ^ W := by rw [mul_comm]; exact hT
  have hLb := lin_bound (cA1 γ εT) (cE γ εT) (2 * (max r.M 1 * 2 ^ L)) (posS (2 ^ L) r.I r.I.length)
    (L * (2 ^ L * 2 ^ L)) (2 ^ K) (2 ^ W) hYb hpL (by omega) hT' (by positivity)
  have hRb := lin_bound (cA2 γ εT) (cE γ εT) (2 * (max r.M 1 * 2 ^ L)) (negS (2 ^ L) r.I r.I.length)
    (L * (2 ^ L * 2 ^ L)) (2 ^ K) (2 ^ W) hYb hnL (by omega) hT' (by positivity)
  have hc1 : cA1 γ εT < 2 ^ W := by omega
  have hc2 : cE γ εT < 2 ^ W := by omega
  have hc3 : cA2 γ εT < 2 ^ W := by omega
  obtain ⟨wv11, e11, keep11⟩ := finM (w := w) (W := W) (pos := L) (lp := 0) cap (cA1 γ εT) (cE γ εT) (cA2 γ εT)
    (cE γ εT) wv10 0 (by rw [q5]; exact hMW) (by rw [q5, q10]; exact hY) (by rw [q5, q10, p11]; exact hLb)
    (by rw [q5, q10, n12]; exact hRb) (by rw [p11]; exact hPb) (by rw [n12]; exact hNb) hc1 hc2 hc3 hc2 hW1
    (by omega) hcap2
  rw [q5, q10, p11, n12] at e11
  set b1 := 0 + (!decide (cA1 γ εT * (2 * (max r.M 1 * 2 ^ L)) + cE γ εT * posS (2 ^ L) r.I r.I.length <
    cA2 γ εT * (2 * (max r.M 1 * 2 ^ L)) + cE γ εT * negS (2 ^ L) r.I r.I.length)).toNat with hb1
  have hb1le : b1 ≤ 1 := by rw [hb1, Nat.zero_add]; exact Bool.toNat_le _
  have k11 : ∀ X : Fin 30, X.val < 11 → X ≠ 5 → wv11 X = wv8 X := fun X hX h5 => by
    rw [keep11 X ⟨by omega, h5⟩ h5, k10 X hX]
  -- the guards
  have e12 := g1M (w := w) (W := W) (pos := L) (lp := 0) cap wv11 b1
    (by rw [k11 7 (by decide) (by decide), m7]; exact hrbW)
    (by rw [k11 8 (by decide) (by decide), m8]; exact hclW) (by omega) hcap2
  rw [k11 7 (by decide) (by decide), k11 8 (by decide) (by decide), m7, m8] at e12
  set b2 := b1 + (decide (r.cl < r.rb)).toNat with hb2
  have e13 := g2M (w := w) (W := W) (pos := L) (lp := 0) cap wv11 b2
    (by rw [k11 4 (by decide) (by decide), m4]; exact hqW) (by omega)
    (by have : (decide (r.cl < r.rb)).toNat ≤ 1 := Bool.toNat_le _
        omega) hcap2
  rw [k11 4 (by decide) (by decide), m4] at e13
  set b3 := b2 + (decide (r.q < 2)).toNat with hb3
  set wv12 := Function.update wv11 29 2 with hwv12
  have k12 : ∀ X : Fin 30, X.val < 11 → X ≠ 5 → wv12 X = wv8 X := fun X hX h5 => by
    rw [hwv12, Function.update_of_ne (show X ≠ 29 by intro e; subst e; simp at hX), k11 X hX h5]
  have e14 := g3M (w := w) (W := W) (pos := L) (lp := 0) cap wv12 b3
    (by rw [k12 6 (by decide) (by decide), m6]; exact hNW)
    (by have : (decide (r.cl < r.rb)).toNat ≤ 1 := Bool.toNat_le _
        have : (decide (r.q < 2)).toNat ≤ 1 := Bool.toNat_le _
        omega) hcap2
  rw [k12 6 (by decide) (by decide), m6] at e14
  set b4 := b3 + (decide (r.N = 0)).toNat with hb4
  have hN10 : r.N ^ 10 < 2 ^ (10 * L) := by
    rw [pow_mul']; exact Nat.pow_lt_pow_left hNL (by norm_num)
  have g9 : wv12 9 = 1 := by rw [k12 9 (by decide) (by decide), m9]
  have g6 : wv12 6 = r.N := by rw [k12 6 (by decide) (by decide), m6]
  obtain ⟨wv13, e15, -⟩ := g4M (w := w) (W := W) (pos := L) (lp := 0) cap (gA γ εT) (gB γ εT) (gC γ εT) (gD γ εT)
    wv12 b4 g9 (by rw [g6]; exact hNW) (by rw [g6]; exact lt_of_lt_of_le hN10 hLWp)
    (by rw [g6]
        have := lin_bound (gA γ εT) (gB γ εT) 1 (r.N ^ 10) (2 ^ (10 * L)) (2 ^ K) (2 ^ W)
          (Nat.one_le_two_pow) hN10.le (by simp only [hK, kC] at hKlt ⊢; omega) (by rw [hP2, mul_comm])
          (by positivity)
        simpa using this)
    (by rw [g6]
        have := lin_bound (gC γ εT) (gD γ εT) 1 (r.N ^ 10) (2 ^ (10 * L)) (2 ^ K) (2 ^ W)
          (Nat.one_le_two_pow) hN10.le (by simp only [hK, kC] at hKlt ⊢; omega) (by rw [hP2, mul_comm])
          (by positivity)
        simpa using this)
    (by have : gB γ εT < 2 ^ K := by simp only [hK, kC] at hKlt ⊢; omega
        omega)
    (by have : gD γ εT < 2 ^ K := by simp only [hK, kC] at hKlt ⊢; omega
        omega) hW1
    (by have : (decide (r.cl < r.rb)).toNat ≤ 1 := Bool.toNat_le _
        have : (decide (r.q < 2)).toNat ≤ 1 := Bool.toNat_le _
        have : (decide (r.N = 0)).toNat ≤ 1 := Bool.toNat_le _
        omega) hcap2
  rw [g6] at e15
  set b5 := b4 + (!decide (gA γ εT + gB γ εT * r.N ^ 10 < gC γ εT + gD γ εT * r.N ^ 10)).toNat with hb5
  have hb5le : b5 ≤ 5 := by
    have : (decide (r.cl < r.rb)).toNat ≤ 1 := Bool.toNat_le _
    have : (decide (r.q < 2)).toNat ≤ 1 := Bool.toNat_le _
    have : (decide (r.N = 0)).toNat ≤ 1 := Bool.toNat_le _
    have : (!decide (gA γ εT + gB γ εT * r.N ^ 10 < gC γ εT + gD γ εT * r.N ^ 10)).toNat ≤ 1 := Bool.toNat_le _
    omega
  obtain ⟨τ, e16, hout, hsh, hval⟩ := outM cap w W wv13 b5 (by omega) hLW hcap2
  refine ⟨τ, ?_, ?_, hsh, hval⟩
  · have E := WXExec.seq e0 (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5
      (WXExec.seq e6 (WXExec.seq e7 (WXExec.seq e8 (WXExec.seq e9 (WXExec.seq e10 (WXExec.seq e11
        (WXExec.seq e12 (WXExec.seq e13 (WXExec.seq e14 (WXExec.seq e15 e16)))))))))))))))
    refine E.mono ?_
    have hs10 : 10 * w.length + K = W := rfl
    rw [hs10]
    have hbud : budgetW γ εT r = 60000 * (W + 1) ^ 3 + 200 * (K * (W + 1) ^ 3) := by
      show (60000 + 200 * kC γ εT) * (widthW γ εT r + 1) ^ 3 = _
      ring
    rw [hbud]
    exact cost_le W K r.M b5 _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) hb5le
  · have hbv := bad_verdict γ εT r
    rw [← hw, ← hL] at hbv
    rw [hout, bitWord_eq, ← hbv]

/-- The budget class: `budget ≤ (60000 + 200K)(K + 11)^3 · (|word| + 1)^3`. -/
theorem budgetW_class (γ εT : ℚ) (r : VerdictReq) :
    budgetW γ εT r ≤ (60000 + 200 * kC γ εT) * (kC γ εT + 11) ^ 3 * ((verdictWord r).length + 1) ^ 3 := by
  unfold budgetW widthW
  rw [mul_assoc, ← mul_pow]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  nlinarith

noncomputable def verdictMachine (γ εT : ℚ) : VerdictMachine γ εT where
  budget := budgetW γ εT
  wf := NearCubicGates.Close.Interfaces.wordFunction_of_wmx (verdictP γ εT) 1 (by decide) (capW γ εT)
    (fun r => verdictRuns γ εT r)
  cls := ⟨(60000 + 200 * kC γ εT) * (kC γ εT + 11) ^ 3, 3, fun r => budgetW_class γ εT r⟩

/-! The program is opaque to consumers: use `verdictMachine`. -/
attribute [irreducible] verdictP

/-- The existence form. -/
theorem verdictMachine_exists (γ εT : ℚ) : Nonempty (VerdictMachine γ εT) := ⟨verdictMachine γ εT⟩

end NearCubicGates.Close.WorkerArith
