import Proof.MachineModel.RuntimeShapeClasses
import Proof.SourceAssembly.SourceRequestSymOriginal

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.RuntimeShape NearCubicWires.SourceInterfaces NearCubicWires.PolynomialSchedule
open NearCubicWires.RecoveryWitnessPolicy NearCubicWires.SupplierEstimator
open NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary NearCubicWires.SupplierPipeline

/-! ## 1. The table factor beats every fixed polynomial past a live-scale onset -/

/-- **`a·(q+1)^e ≤ 2^(q−K)` past an onset depending on `(a, e, L)` only.** -/
theorem poly_le_twoPow_res (a e L : ℕ) :
    ∃ q0, ∀ q, q0 ≤ q → a * (q+1)^e ≤ 2^(q - normalizedLiveCount q L) := by
  obtain ⟨q1, h1⟩ := SupplierCapacity.coefficient_mul_logScale_eventually_le (a + e + L)
  refine ⟨q1, fun q hq => ?_⟩
  have hl := h1 q hq
  have hlg : 1 ≤ logScale q := by
    have := log_succ_le_logScale q
    omega
  have ha : a < 2^a := Nat.lt_two_pow_self
  have hp : (q+1)^e ≤ 2^(e*logScale q) := succ_pow_le q e
  have hsplit : (a+e+L)*logScale q = a*logScale q + e*logScale q + L*logScale q := by ring
  have hal : a ≤ a*logScale q := Nat.le_mul_of_pos_right _ hlg
  have hK : normalizedLiveCount q L ≤ L*logScale q := min_le_right _ _
  have hexp : a + e*logScale q ≤ q - normalizedLiveCount q L := by omega
  calc a*(q+1)^e ≤ 2^a * 2^(e*logScale q) := Nat.mul_le_mul ha.le hp
    _ = 2^(a + e*logScale q) := (pow_add 2 a _).symm
    _ ≤ 2^(q - normalizedLiveCount q L) := Nat.pow_le_pow_right (by decide) hexp

/-- **Every reserve `C·tableClass L hR q` with `C ≥ 1` dominates a fixed polynomial past one onset** chosen from
`(a, e, L)`; the coefficient `C` and the exponent `hR` are quantified AFTER the onset. -/
theorem poly_le_Rc (a e L : ℕ) :
    ∃ q0, ∀ q, q0 ≤ q → ∀ C hR : ℕ, 1 ≤ C → a * (q+1)^e ≤ C * tableClass L hR q := by
  obtain ⟨q0, h0⟩ := poly_le_twoPow_res a e L
  refine ⟨q0, fun q hq C hR hC => ?_⟩
  have h1 := h0 q hq
  have h2 : 2^(q - normalizedLiveCount q L) ≤ tableClass L hR q :=
    Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (Nat.succ_pos q))
  have h3 : tableClass L hR q ≤ C * tableClass L hR q := Nat.le_mul_of_pos_left _ hC
  omega

/-- The same for any polynomially bounded quantity. -/
theorem polyBounded_le_Rc (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (L : ℕ) :
    ∃ q0, ∀ q, q0 ≤ q → ∀ C hR : ℕ, 1 ≤ C → f q ≤ C * tableClass L hR q := by
  obtain ⟨a, e, _, hae⟩ := hf
  obtain ⟨q0, h0⟩ := poly_le_Rc a e L
  exact ⟨q0, fun q hq C hR hC => (hae q).trans (h0 q hq C hR hC)⟩

/-! ## 2. The two code widths are polynomial in the description cap -/

theorem encNat_poly : PolynomiallyBounded encodeNatBitsBound := by
  unfold encodeNatBitsBound
  exact polynomiallyBounded_add (polynomiallyBounded_constant 1) <|
    polynomiallyBounded_mul
      (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
        (polynomiallyBounded_pow polynomiallyBounded_id 4))
      (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1))

theorem natCode_poly : PolynomiallyBounded canonicalNatCodeBitBound := by
  change PolynomiallyBounded (fun p => canonicalNatCodeBitBound p)
  simpa only [canonicalNatCodeBitBound] using
    polynomiallyBounded_comp encNat_poly (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1))

theorem intCode_poly : PolynomiallyBounded canonicalIntCodeBitBound := by
  change PolynomiallyBounded (fun p => canonicalIntCodeBitBound p)
  simpa only [canonicalIntCodeBitBound] using
    polynomiallyBounded_mul (polynomiallyBounded_constant 2)
      (polynomiallyBounded_add (polynomiallyBounded_constant 1) encNat_poly)

theorem balancedCode_poly {atom : ℕ → ℕ} (h : PolynomiallyBounded atom) :
    PolynomiallyBounded (fun p => canonicalBalancedCodeBitBound p (atom p)) := by
  have hprod := polynomiallyBounded_mul
    (polynomiallyBounded_mul (polynomiallyBounded_constant 2) (polynomiallyBounded_pow polynomiallyBounded_id 4))
    (polynomiallyBounded_add (polynomiallyBounded_mul polynomiallyBounded_id h) (polynomiallyBounded_constant 1))
  simpa only [canonicalBalancedCodeBitBound] using polynomiallyBounded_add (polynomiallyBounded_constant 1) hprod

theorem tagged3_poly {f g h : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) : PolynomiallyBounded (fun p => taggedListBitBound [f p, g p, h p]) := by
  have hone := polynomiallyBounded_constant 1
  have hfour := polynomiallyBounded_constant 4
  have t3 := polynomiallyBounded_mul hfour (polynomiallyBounded_add hh hone)
  have t2 := polynomiallyBounded_mul hfour (polynomiallyBounded_add hg t3)
  simpa only [taggedListBitBound] using polynomiallyBounded_mul hfour (polynomiallyBounded_add hf t2)

theorem tagged4_poly {f g h k : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) (hk : PolynomiallyBounded k) :
    PolynomiallyBounded (fun p => taggedListBitBound [f p, g p, h p, k p]) := by
  have hone := polynomiallyBounded_constant 1
  have hfour := polynomiallyBounded_constant 4
  have t4 := polynomiallyBounded_mul hfour (polynomiallyBounded_add hk hone)
  have t3 := polynomiallyBounded_mul hfour (polynomiallyBounded_add hh t4)
  have t2 := polynomiallyBounded_mul hfour (polynomiallyBounded_add hg t3)
  simpa only [taggedListBitBound] using polynomiallyBounded_mul hfour (polynomiallyBounded_add hf t2)

theorem gateCode_poly : PolynomiallyBounded canonicalSupportedGateCodeBitBound := by
  change PolynomiallyBounded (fun p => canonicalSupportedGateCodeBitBound p)
  simpa only [canonicalSupportedGateCodeBitBound] using
    tagged3_poly (balancedCode_poly intCode_poly) intCode_poly (balancedCode_poly (polynomiallyBounded_constant 1))

/-- The THR admission width `ThrSwitch.codeWidth` is polynomial. -/
theorem thrWidth_poly : PolynomiallyBounded SourceRequest.ThrSwitch.codeWidth := by
  change PolynomiallyBounded (fun p => canonicalThresholdCircuitCodeBitBound p)
  simpa only [canonicalThresholdCircuitCodeBitBound] using
    tagged4_poly natCode_poly natCode_poly (balancedCode_poly gateCode_poly) gateCode_poly

/-- The SYM admission width `SymOriginal.symCodeWidth` is polynomial. -/
theorem symWidth_poly : PolynomiallyBounded SourceRequest.SymOriginal.symCodeWidth := by
  change PolynomiallyBounded (fun p => canonicalSymmetricCircuitCodeBitBound p)
  simpa only [canonicalSymmetricCircuitCodeBitBound] using
    tagged4_poly natCode_poly natCode_poly (balancedCode_poly gateCode_poly)
      (balancedCode_poly (polynomiallyBounded_constant 1))

/-! ## 3. The caps at the intended instantiation, and the window -/

def ldCap (cL eL q : ℕ) : ℕ := cL * (q+1)^eL

def wCap (q : ℕ) : ℕ := (q+1)^3

def pCap (cw : ℕ → ℕ) (cL eL q : ℕ) : ℕ := CloseoutRowsCircuitCapacity.capacity (cw (ldCap cL eL q))

def dCap (cw : ℕ → ℕ) (cL eL q : ℕ) : ℕ :=
  (q + 2) + pCap cw cL eL q + wCap q + ldCap cL eL q + (2 * cw (ldCap cL eL q) + 1)

theorem ldCap_poly (cL eL : ℕ) : PolynomiallyBounded (ldCap cL eL) := by
  change PolynomiallyBounded (fun q => ldCap cL eL q)
  simpa only [ldCap] using polynomiallyBounded_mul (polynomiallyBounded_constant cL)
    (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) eL)

theorem capacity_poly : PolynomiallyBounded CloseoutRowsCircuitCapacity.capacity := by
  change PolynomiallyBounded (fun N => CloseoutRowsCircuitCapacity.capacity N)
  simpa only [CloseoutRowsCircuitCapacity.capacity] using
    polynomiallyBounded_mul (polynomiallyBounded_constant 1000000000000000000000000000000)
      (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 2)) 26)

theorem dCap_poly (cw : ℕ → ℕ) (hcw : PolynomiallyBounded cw) (cL eL : ℕ) :
    PolynomiallyBounded (dCap cw cL eL) := by
  have hld := ldCap_poly cL eL
  have hcwl : PolynomiallyBounded (fun q => cw (ldCap cL eL q)) := polynomiallyBounded_comp hcw hld
  have hP : PolynomiallyBounded (fun q => pCap cw cL eL q) := by
    simpa only [pCap] using polynomiallyBounded_comp capacity_poly hcwl
  have hW : PolynomiallyBounded (fun q => wCap q) := by
    simpa only [wCap] using
      polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) 3
  have hq2 : PolynomiallyBounded (fun q : ℕ => q + 2) :=
    polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 2)
  have hF : PolynomiallyBounded (fun q => 2 * cw (ldCap cL eL q) + 1) :=
    polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hcwl)
      (polynomiallyBounded_constant 1)
  change PolynomiallyBounded (fun q => dCap cw cL eL q)
  simpa only [dCap] using
    polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add hq2 hP) hW) hld) hF

/-- **The descriptor window, generic in the code width.** Past one onset chosen from `(L, cL, eL)`, for EVERY reserve
coefficient `C ≥ 1` and exponent `hR`: `4 ≤ Ld`, `capacity (cw Ld) ≤ P ≤ D`, `q+2, W, Ld, 2·cw Ld+1 ≤ D`,
`D ≤ Rc = C·tableClass L hR q` and `D + 1 ≤ Rc + 2`. -/
theorem window_sat (cw : ℕ → ℕ) (hcw : PolynomiallyBounded cw) (cL eL L : ℕ) (hcL : 4 ≤ cL) :
    ∃ q0, ∀ q, q0 ≤ q → ∀ C hR : ℕ, 1 ≤ C →
      4 ≤ ldCap cL eL q ∧
      CloseoutRowsCircuitCapacity.capacity (cw (ldCap cL eL q)) ≤ pCap cw cL eL q ∧
      pCap cw cL eL q ≤ dCap cw cL eL q ∧
      q + 2 ≤ dCap cw cL eL q ∧
      wCap q ≤ dCap cw cL eL q ∧
      ldCap cL eL q ≤ dCap cw cL eL q ∧
      2 * cw (ldCap cL eL q) + 1 ≤ dCap cw cL eL q ∧
      dCap cw cL eL q ≤ C * tableClass L hR q ∧
      dCap cw cL eL q + 1 ≤ C * tableClass L hR q + 2 := by
  obtain ⟨q0, h0⟩ := polyBounded_le_Rc (dCap cw cL eL) (dCap_poly cw hcw cL eL) L
  refine ⟨q0, fun q hq C hR hC => ?_⟩
  have hD := h0 q hq C hR hC
  have h4 : 4 ≤ ldCap cL eL q := by
    unfold ldCap
    have : 1 ≤ (q+1)^eL := Nat.one_le_pow _ _ (Nat.succ_pos q)
    nlinarith
  unfold dCap at hD ⊢
  exact ⟨h4, le_rfl, by omega, by omega, by omega, by omega, by omega, hD, by omega⟩

/-! ## 4. At the consumers' exact quantities -/

theorem thr_window_sat (cL eL L : ℕ) (hcL : 4 ≤ cL) :
    ∃ q0, ∀ q, q0 ≤ q → ∀ C hR : ℕ, 1 ≤ C →
      4 ≤ ldCap cL eL q ∧
      CloseoutRowsCircuitCapacity.capacity (SourceRequest.ThrSwitch.codeWidth (ldCap cL eL q)) ≤
        pCap SourceRequest.ThrSwitch.codeWidth cL eL q ∧
      pCap SourceRequest.ThrSwitch.codeWidth cL eL q ≤ dCap SourceRequest.ThrSwitch.codeWidth cL eL q ∧
      q + 2 ≤ dCap SourceRequest.ThrSwitch.codeWidth cL eL q ∧
      wCap q ≤ dCap SourceRequest.ThrSwitch.codeWidth cL eL q ∧
      ldCap cL eL q ≤ dCap SourceRequest.ThrSwitch.codeWidth cL eL q ∧
      (∀ {q' : ℕ} (c : NormalizedThresholdThresholdCircuit q'),
        (frame (SourceRequest.ThrSwitch.codeBits (ldCap cL eL q) c)).length ≤
          dCap SourceRequest.ThrSwitch.codeWidth cL eL q) ∧
      dCap SourceRequest.ThrSwitch.codeWidth cL eL q ≤ C * tableClass L hR q ∧
      dCap SourceRequest.ThrSwitch.codeWidth cL eL q + 1 ≤ C * tableClass L hR q + 2 := by
  obtain ⟨q0, h0⟩ := window_sat SourceRequest.ThrSwitch.codeWidth thrWidth_poly cL eL L hcL
  refine ⟨q0, fun q hq C hR hC => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h0 q hq C hR hC
  refine ⟨a1, a2, a3, a4, a5, a6, fun c => ?_, a8, a9⟩
  rw [frame_length, SourceRequest.ThrSwitch.codeBits_length]
  exact a7

theorem sym_window_sat (cL eL L : ℕ) (hcL : 4 ≤ cL) :
    ∃ q0, ∀ q, q0 ≤ q → ∀ C hR : ℕ, 1 ≤ C →
      4 ≤ ldCap cL eL q ∧
      CloseoutRowsCircuitCapacity.capacity (SourceRequest.SymOriginal.symCodeWidth (ldCap cL eL q)) ≤
        pCap SourceRequest.SymOriginal.symCodeWidth cL eL q ∧
      pCap SourceRequest.SymOriginal.symCodeWidth cL eL q ≤ dCap SourceRequest.SymOriginal.symCodeWidth cL eL q ∧
      q + 2 ≤ dCap SourceRequest.SymOriginal.symCodeWidth cL eL q ∧
      wCap q ≤ dCap SourceRequest.SymOriginal.symCodeWidth cL eL q ∧
      ldCap cL eL q ≤ dCap SourceRequest.SymOriginal.symCodeWidth cL eL q ∧
      (∀ {q' : ℕ} (c : NormalizedSymmetricThresholdCircuit q'),
        (frame (SourceRequest.SymOriginal.symCodeBits (ldCap cL eL q) c)).length ≤
          dCap SourceRequest.SymOriginal.symCodeWidth cL eL q) ∧
      dCap SourceRequest.SymOriginal.symCodeWidth cL eL q ≤ C * tableClass L hR q ∧
      dCap SourceRequest.SymOriginal.symCodeWidth cL eL q + 1 ≤ C * tableClass L hR q + 2 := by
  obtain ⟨q0, h0⟩ := window_sat SourceRequest.SymOriginal.symCodeWidth symWidth_poly cL eL L hcL
  refine ⟨q0, fun q hq C hR hC => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h0 q hq C hR hC
  refine ⟨a1, a2, a3, a4, a5, a6, fun c => ?_, a8, a9⟩
  rw [frame_length, SourceRequest.SymOriginal.symCodeBits_length]
  exact a7

end NearCubicWires.SourceBudget

