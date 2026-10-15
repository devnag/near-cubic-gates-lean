import Proof.Wire_3_5.Gate0
import Proof.Wire_3_5.RecoverySetupTwo

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Split
open NearCubicWires NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Transfer Filter

variable (l : Literals)

/-- The union's call-count exponent at the pinned oracle degree `G = 17·c_STV` (both branches of `S₂`). -/
noncomputable def unionCallDeg : ℕ := gateCallDeg l (recOracleDeg l)

def callDegMargin : ℕ := 8

structure GateFreeOK (F : GateFree l) : Prop where

  callDeg : unionCallDeg l + callDegMargin ≤ F.E.callDeg

/-- The pinned union setup at the concrete gate, for every choice of the free constants. -/
noncomputable abbrev setupF (F : GateFree l) : (gate0 l F).Setup := unionSetupS2 l (gate0 l F)

def PrimitiveLeafF := Σ F : GateFree l, Σ' _ : GateFreeOK l F, PrimitiveLeaf (gate0 l F)

def UnionLeafF := ∀ F : GateFree l, GateFreeOK l F → UnionLeaf (gate0 l F) (setupF l F)

def RecoveryLeafF := ∀ F : GateFree l, GateFreeOK l F → RecoveryLeaf (gate0 l F) (setupF l F)

noncomputable def parts_of_leavesF (p : PrimitiveLeafF l) (u : UnionLeafF l) (r : RecoveryLeafF l) : Parts :=
  parts_of_leaves (gate0 l p.1) (setupF l p.1) p.2.2 (u p.1 p.2.1) (r p.1 p.2.1)

noncomputable def literals_parts_of_leavesF (p : ∀ l, PrimitiveLeafF l) (u : ∀ l, UnionLeafF l)
    (r : ∀ l, RecoveryLeafF l) : Literals → Parts :=
  fun l => parts_of_leavesF l (p l) (u l) (r l)

theorem rowB_of_leavesF (p : ∀ l, PrimitiveLeafF l) (u : ∀ l, UnionLeafF l) (r : ∀ l, RecoveryLeafF l) :
    Literals → rowB :=
  literals_rowB_of_parts (literals_parts_of_leavesF p u r)

/-! ## The union side of the relation -/

theorem calls_absorb (F : GateFree l) (hF : GateFreeOK l F) (K : ℕ) :
    ∀ᶠ q : ℕ in atTop, K * (q + 1) ^ (unionCallDeg l + (callDegMargin - 1)) ≤ q ^ F.E.callDeg := by
  have hc : unionCallDeg l + callDegMargin ≤ F.E.callDeg := hF.callDeg
  filter_upwards [eventually_ge_atTop (K * 2 ^ (unionCallDeg l + (callDegMargin - 1)) + 1)] with q hq
  have hq1 : 1 ≤ q := le_trans (Nat.le_add_left 1 _) hq
  have h2 : (q + 1) ^ (unionCallDeg l + (callDegMargin - 1)) ≤ (2 * q) ^ (unionCallDeg l + (callDegMargin - 1)) :=
    Nat.pow_le_pow_left (by omega) _
  have hK : K * 2 ^ (unionCallDeg l + (callDegMargin - 1)) ≤ q := by omega
  have hexp : unionCallDeg l + (callDegMargin - 1) + 1 ≤ F.E.callDeg := by
    unfold callDegMargin at hc ⊢
    omega
  calc K * (q + 1) ^ (unionCallDeg l + (callDegMargin - 1))
      ≤ K * (2 * q) ^ (unionCallDeg l + (callDegMargin - 1)) := Nat.mul_le_mul_left _ h2
    _ = K * 2 ^ (unionCallDeg l + (callDegMargin - 1)) * q ^ (unionCallDeg l + (callDegMargin - 1)) := by
        rw [mul_pow, mul_assoc]
    _ ≤ q * q ^ (unionCallDeg l + (callDegMargin - 1)) := Nat.mul_le_mul_right _ hK
    _ = q ^ (unionCallDeg l + (callDegMargin - 1) + 1) := by rw [pow_succ, mul_comm]
    _ ≤ q ^ F.E.callDeg := Nat.pow_le_pow_right hq1 hexp

/-- **The margin is sharp for `calls_absorb`**: one power less and it fails already at `K = 1`. -/
theorem calls_absorb_sharp (F : GateFree l)
    (hlt : F.E.callDeg ≤ unionCallDeg l + (callDegMargin - 1)) :
    ¬ ∀ᶠ q : ℕ in atTop, 1 * (q + 1) ^ (unionCallDeg l + (callDegMargin - 1)) ≤ q ^ F.E.callDeg := by
  intro h
  obtain ⟨q, hq⟩ := (h.and (eventually_ge_atTop 1)).exists
  obtain ⟨hle, hq1⟩ := hq
  have hpos : 0 < unionCallDeg l + (callDegMargin - 1) := by unfold callDegMargin; omega
  have h1 : q ^ F.E.callDeg ≤ q ^ (unionCallDeg l + (callDegMargin - 1)) := Nat.pow_le_pow_right hq1 hlt
  have h2 : q ^ (unionCallDeg l + (callDegMargin - 1)) < (q + 1) ^ (unionCallDeg l + (callDegMargin - 1)) :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self q) (Nat.pos_iff_ne_zero.mp hpos)
  omega

/-- A choice violating the relation is rejected: with `callDeg` below `gateCallDeg + c`, `GateFreeOK` fails. -/
theorem not_gateFreeOK (F : GateFree l) (hlt : F.E.callDeg < unionCallDeg l + callDegMargin) :
    ¬ GateFreeOK l F := fun h => absurd h.callDeg (Nat.not_le.mpr hlt)

namespace Free

/-- The envelope with its call exponent raised to at least `c`; every other exponent unchanged. -/
def raiseE (E : Envelope) (c : ℕ) : Envelope := { E with callDeg := max E.callDeg c }

/-- The fit conditions at the raised envelope imply those at the original one (`callDeg` only lower-bounds `k`). -/
theorem fits_of_raiseE {E : Envelope} {c q lg k psi : ℕ} (h : Fits (raiseE E c) q lg k psi) :
    Fits E q lg k psi := by
  have hc : E.callDeg ≤ max E.callDeg c := le_max_left _ _
  obtain ⟨hlog, hmain, htable, hkq, hsel, hpre⟩ := h
  refine ⟨hlog, ?_, ?_, hkq, ?_, ?_⟩
  · exact le_trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.add_le_add_left hc _) _)) hmain
  · exact le_trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.add_le_add_left hc _) _)) htable
  · exact le_trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.add_le_add_left hc _) _)) _) hsel
  · exact le_trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.add_le_add_left hc _) _)) _) hpre

/-- The free constants with the call exponent raised to meet `GateFreeOK`; everything else unchanged. -/
noncomputable def raise (F : GateFree l) : GateFree l :=
  { F with E := raiseE F.E (unionCallDeg l + callDegMargin), hσ := F.hσ }

theorem raise_ok (F : GateFree l) : GateFreeOK l (raise l F) := ⟨le_max_right _ _⟩

/-- A call admissible at the raised constants is admissible at the original ones. -/
theorem call_of_raise (F : GateFree l) {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} (req : PrimRequest)
    (h : ((gate0 l (raise l F)).inputs kclk coef A a ha).Call req) :
    ((gate0 l F).inputs kclk coef A a ha).Call req := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fits_of_raiseE h7⟩

/-- The per-call budget does not read `callDeg`. -/
theorem callBudget_raise (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) :
    ((gate0 l (raise l F)).budget kclk coef A a ha).callBudget n = ((gate0 l F).budget kclk coef A a ha).callBudget n :=
  rfl

/-- A primitive at the original constants is one at the raised constants: same value, same program, same error. -/
noncomputable def primRaise (F : GateFree l) {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}
    (P : FusedPrimitive ((gate0 l F).inputs kclk coef A a ha)) :
    FusedPrimitive ((gate0 l (raise l F)).inputs kclk coef A a ha) where
  value := P.value
  estimator :=
    { program := P.estimator.program
      realizes := fun r => by
        obtain ⟨receipt, hrun, hout⟩ := P.estimator.realizes ⟨r.1, call_of_raise l F r.1 r.2⟩
        refine ⟨receipt, ?_, hout⟩
        rw [callBudget_raise]
        exact hrun }
  error := fun req h => P.error req (call_of_raise l F req h)

theorem callBudget_pos {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
    (P : FusedPrimitive I) (req : PrimRequest) (h : I.Call req) : 0 < B.callBudget req.n := by
  rcases Nat.eq_zero_or_pos (B.callBudget req.n) with h0 | h0
  · exfalso
    obtain ⟨receipt, hrun, hout⟩ := P.estimator.realizes ⟨req, h⟩
    have hrun' : LocalBitMultitape.run P.estimator.program.machine 0
        (P.estimator.program.inputTapes req.word) = some receipt := by
      rw [← h0]; exact hrun
    unfold LocalBitMultitape.run LocalBitMultitape.runFrom at hrun'
    split_ifs at hrun'
    cases hrun'
    have hfresh := P.estimator.program.outputFresh
    have hnil : (P.estimator.program.inputTapes req.word) P.estimator.program.outputTape = [] := by
      unfold RepairOrdinary.Program.inputTapes
      rw [if_neg hfresh]
    have hout' : (P.estimator.program.inputTapes req.word) P.estimator.program.outputTape =
        ratWord (P.value req) := hout
    rw [hnil] at hout'
    unfold ratWord RepairRepresentation.intWord at hout'
    simp at hout'
  · exact h0

/-- **A primitive at the gate with one satisfiable call has a positive coefficient.** -/
theorem coef_pos (F : GateFree l) {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}
    (P : FusedPrimitive ((gate0 l F).inputs kclk coef A a ha)) (req : PrimRequest)
    (h : ((gate0 l F).inputs kclk coef A a ha).Call req) : 1 ≤ coef := by
  have hb := callBudget_pos P req h
  rcases Nat.eq_zero_or_pos coef with h0 | h0
  · subst h0
    exfalso
    have hz : ((gate0 l F).budget kclk 0 A a ha).callBudget req.n = 0 := by
      simp [Gate.budget, rowBNativeBudget, rowBBudget, TimeBudget.callBudget, ComponentCosts.perCall,
        Machine.costsOf]
    omega
  · exact h0

theorem selection_le_mainPass (E₁ E : Envelope) (cr c₁ : ℕ) :
    ∀ᶠ q : ℕ in atTop, ∀ psi psi' : ℕ, c₁ * classBound E₁ .selection q (starWidth (rowBr cr q) q) psi ≤
      classBound E .mainPass q (starWidth (rowBr cr q) q) psi' := by
  filter_upwards [eventually_mul_Lq_pow_le (4 * ((E₁.csel + 1) * (2 * cr + 3) + E₁.Asel + c₁ + 1)) 2,
    eventually_ge_atTop 1] with q hq hq1 psi psi'
  set L := Lq q with hLdef
  set k := starWidth (rowBr cr q) q with hkdef
  set T := (E₁.csel + 1) * (2 * cr + 3) with hT
  have hL : 1 ≤ L := Lq_pos q
  have hk : k ≤ (2 * cr + 3) * L ^ 2 := by
    have h1 : k ≤ rowBr cr q * L := starWidth_le (rowBr cr q) q
    have h2 : rowBr cr q + 1 ≤ (2 * cr + 3) * L := rowBr_succ_le cr q
    calc k ≤ rowBr cr q * L := h1
      _ ≤ ((2 * cr + 3) * L) * L := Nat.mul_le_mul_right _ (by omega)
      _ = (2 * cr + 3) * L ^ 2 := by ring
  have hqL : q ≤ 2 ^ L := le_trans (by omega) (Nat.le_pow_clog (by norm_num) (q + 2))
  have hc1 : c₁ ≤ 2 ^ c₁ := (Nat.lt_two_pow_self).le
  have hLL : L ≤ L ^ 2 := by nlinarith
  have ha : E₁.csel * k + k / 4 ≤ (E₁.csel + 1) * k := by
    have := Nat.div_le_self k 4
    rw [add_mul, one_mul]
    omega
  have hb : (E₁.csel + 1) * k ≤ T * L ^ 2 := by
    calc (E₁.csel + 1) * k ≤ (E₁.csel + 1) * ((2 * cr + 3) * L ^ 2) := Nat.mul_le_mul_left _ hk
      _ = T * L ^ 2 := by rw [hT]; ring
  have hc : E₁.Asel * L ≤ E₁.Asel * L ^ 2 := Nat.mul_le_mul_left _ hLL
  have hd : c₁ ≤ c₁ * L ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have he : 4 * (T * L ^ 2) + 4 * (E₁.Asel * L ^ 2) + 4 * (c₁ * L ^ 2) + 4 * L ^ 2 ≤ q := by
    have e : 4 * (T + E₁.Asel + c₁ + 1) * L ^ 2 =
        4 * (T * L ^ 2) + 4 * (E₁.Asel * L ^ 2) + 4 * (c₁ * L ^ 2) + 4 * L ^ 2 := by ring
    rw [← e]
    exact hq
  have hexp : q / 2 + E₁.csel * k + L * E₁.Asel + c₁ ≤ q - k / 4 := by
    rw [mul_comm L E₁.Asel]
    omega
  show c₁ * (2 ^ (q / 2 + E₁.csel * k) * q ^ E₁.Asel) ≤ 2 ^ (q - k / 4) * q ^ E.Amain
  have hpow : q ^ E₁.Asel ≤ 2 ^ (L * E₁.Asel) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hqL _
  calc c₁ * (2 ^ (q / 2 + E₁.csel * k) * q ^ E₁.Asel)
      ≤ 2 ^ c₁ * (2 ^ (q / 2 + E₁.csel * k) * 2 ^ (L * E₁.Asel)) :=
        Nat.mul_le_mul hc1 (Nat.mul_le_mul_left _ hpow)
    _ = 2 ^ (q / 2 + E₁.csel * k + L * E₁.Asel + c₁) := by rw [← pow_add, ← pow_add]; ring_nf
    _ ≤ 2 ^ (q - k / 4) := Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ 2 ^ (q - k / 4) * q ^ E.Amain := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hq1)

theorem selection_le_callBudget (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (hcoef : 1 ≤ coef)
    (E₁ : Envelope) (c₁ : ℕ) :
    ∀ᶠ q : ℕ in atTop, c₁ * classBound E₁ .selection q (((gate0 l F).budget kclk coef A a ha).kOf q)
        (((gate0 l F).budget kclk coef A a ha).psiOf q) ≤ ((gate0 l F).budget kclk coef A a ha).callBudget q := by
  filter_upwards [selection_le_mainPass E₁ F.E F.cr c₁] with q hq
  have h := hq (((gate0 l F).budget kclk coef A a ha).psiOf q) (((gate0 l F).budget kclk coef A a ha).psiOf q)
  refine le_trans h ?_
  show classBound F.E .mainPass q _ _ ≤
    coef * classBound F.E .selection q _ _ + coef * classBound F.E .preprocessing q _ _ +
      coef * classBound F.E .table q _ _ + coef * classBound F.E .mainPass q _ _
  exact le_trans (Nat.le_mul_of_pos_left _ hcoef) (Nat.le_add_left _ _)

end Free

/-- **Satisfiability witness** of the relations: `σ = A_pad + 1`, `callDeg = gateCallDeg + c`, the class exponents of
`satEnvelope`, `C_D = c_r = 1`, endpoint exponent `3 = D + 2`. -/
noncomputable def freeSat : GateFree l where
  E := { satEnvelope with sigma := gateApad l + 1, callDeg := unionCallDeg l + callDegMargin }
  hσ := le_refl _
  CD := 1
  cr := 1
  cr_pos := le_refl _
  filterErrDeg := 3
  hG7 := le_refl _

theorem freeSat_ok : GateFreeOK l (freeSat l) := ⟨le_refl _⟩

noncomputable def primitiveLeafF_of_leaf (F : GateFree l) (p : PrimitiveLeaf (gate0 l F)) : PrimitiveLeafF l :=
  ⟨Free.raise l F, Free.raise_ok l F, ⟨p.1, fun kclk A a ha => Free.primRaise l F (p.2 kclk A a ha)⟩⟩

end NearCubicWires.WireExponent3_5.Split
