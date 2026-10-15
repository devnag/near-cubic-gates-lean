import Proof.Packets.PacketFamilyParent
import Proof.MachineModel.OrdinarySignedSortKey
import Proof.Amplification.RecoveryCanonicalValues

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
noncomputable section

/-! ## Key digits -/

/-- The eight digit fields of a key; `none` (after the last row) is the done flag. -/
def keyDigits (a : DecompositionAlgorithm) : ∀ r : Request, Option (rcKey a r) → Fin 8 → ℕ
  | _, none => fun i => if i.val = 7 then 1 else 0
  | .terminal, some k => PEmpty.elim k
  | .sym r _ _ _, some k => fun i =>
      if h : i.val < r.circuits.length then k.offset ⟨i.val, h⟩
      else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val else 0
  | .thr r _ _ _, some k => fun i =>
      if h : i.val < r.circuits.length then (k.selection ⟨i.val, h⟩).val
      else if i.val = 4 then (primeIndexFinEquiv _ k.prime).val
      else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val
      else if i.val = 6 then k.residue.val else 0

/-- A strict bound on every digit of an actual key, from the request's dimensions alone. -/
def digitBound (a : DecompositionAlgorithm) : Request → ℕ
  | .terminal => 2
  | .sym r _ L target =>
      (Packets.seedList (symmetricFourfoldOccurrences r)
        (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target)).length +
      (∑ i : Fin r.circuits.length, ((r.circuits.get i).bottomCount + 1)) + 2
  | .thr r _ L target =>
      (Packets.seedList (thresholdFourfoldOccurrences r)
        (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
        (CloseoutFinalC10ThresholdRows.listDenominator a r target)).length +
      (∑ i : Fin r.circuits.length, (ThresholdRows.children a (r.circuits.get i)).length) +
      Fintype.card (PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target)) +
      CloseoutFinalC10ThresholdRows.primeCutoff a r target + 2

/-- One field width per request: every digit of an actual key fits. -/
def fieldWidth (a : DecompositionAlgorithm) (r : Request) : ℕ := Nat.log 2 (digitBound a r) + 1

/-- The codes the cursor may hold: actual keys and `done`. -/
def CodeValid (a : DecompositionAlgorithm) (r : Request) (c : Option (rcKey a r)) : Prop :=
  c = none ∨ ∃ k ∈ rcKeys a r, c = some k

theorem two_le_bound (a : DecompositionAlgorithm) (r : Request) : 2 ≤ digitBound a r := by
  cases r <;> simp [digitBound]

theorem keyDigits_none (a : DecompositionAlgorithm) (r : Request) (i : Fin 8) :
    keyDigits a r none i = if i.val = 7 then 1 else 0 := by
  cases r <;> rfl

theorem keyDigits_sym (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target) (i : Fin 8) :
    keyDigits a (.sym r four L target) (some k) i =
      if h : i.val < r.circuits.length then k.offset ⟨i.val, h⟩
      else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val else 0 := rfl

theorem keyDigits_thr (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) (i : Fin 8) :
    keyDigits a (.thr r four L target) (some k) i =
      if h : i.val < r.circuits.length then (k.selection ⟨i.val, h⟩).val
      else if i.val = 4 then (primeIndexFinEquiv _ k.prime).val
      else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val
      else if i.val = 6 then k.residue.val else 0 := rfl

theorem sym_digit_lt (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target)
    (hk : k ∈ RCFive.RowKeys.symKeys r L target) (i : Fin 8) :
    keyDigits a (.sym r four L target) (some k) i < digitBound a (.sym r four L target) := by
  rw [keyDigits_sym]
  simp only [digitBound, Packets.seedList, List.length_ofFn]
  split_ifs with h h5
  · obtain ⟨seed, _, hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨offset, ho, rfl⟩ := List.mem_map.mp hk
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp ho
    have hlt : (t ⟨i.val, h⟩).val < (r.circuits.get ⟨i.val, h⟩).bottomCount + 1 := (t ⟨i.val, h⟩).isLt
    have hsum := Finset.single_le_sum (f := fun j : Fin r.circuits.length =>
      (r.circuits.get j).bottomCount + 1) (fun j _ => Nat.zero_le _) (Finset.mem_univ ⟨i.val, h⟩)
    simp only at hsum ⊢
    omega
  · have := (canonicalWalkSampleFinEquiv _ _ k.seed).isLt
    omega
  · omega

theorem thr_digit_lt (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) (i : Fin 8) :
    keyDigits a (.thr r four L target) (some k) i < digitBound a (.thr r four L target) := by
  rw [keyDigits_thr]
  simp only [digitBound, Packets.seedList, List.length_ofFn]
  split_ifs with h h4 h5 h6
  · have hlt := (k.selection ⟨i.val, h⟩).isLt
    have hsum := Finset.single_le_sum (f := fun j : Fin r.circuits.length =>
      (ThresholdRows.children a (r.circuits.get j)).length) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ ⟨i.val, h⟩)
    omega
  · have := (primeIndexFinEquiv _ k.prime).isLt
    omega
  · have := (canonicalWalkSampleFinEquiv _ _ k.seed).isLt
    omega
  · have hres := k.residue.isLt
    have hp := (mem_primesUpTo.mp k.prime.property).2
    omega
  · omega

theorem digit_lt_bound (a : DecompositionAlgorithm) (r : Request) (c : Option (rcKey a r))
    (hc : CodeValid a r c) (i : Fin 8) : keyDigits a r c i < digitBound a r := by
  have h2 := two_le_bound a r
  rcases hc with rfl | ⟨k, hk, rfl⟩
  · rw [keyDigits_none]
    split_ifs <;> omega
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r four L target => exact sym_digit_lt a r four L target k hk i
  | thr r four L target => exact thr_digit_lt a r four L target k i

theorem digit_lt_pow (a : DecompositionAlgorithm) (r : Request) (c : Option (rcKey a r))
    (hc : CodeValid a r c) (i : Fin 8) : keyDigits a r c i < 2 ^ fieldWidth a r :=
  (digit_lt_bound a r c hc i).trans (Nat.lt_pow_succ_log_self (by norm_num) _)

theorem sym_digits_injective (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k k' : RCFive.RowKeys.SymKey r L target)
    (h : keyDigits a (.sym r four L target) (some k) = keyDigits a (.sym r four L target) (some k')) :
    k = k' := by
  have hoff : k.offset = k'.offset := by
    funext j
    have hj := congrFun h ⟨j.val, by have := j.isLt; omega⟩
    rw [keyDigits_sym, keyDigits_sym] at hj
    simp only [dif_pos j.isLt] at hj
    exact hj
  have hseed : k.seed = k'.seed := by
    have h5 := congrFun h ⟨5, by omega⟩
    rw [keyDigits_sym, keyDigits_sym] at h5
    simp only [show ¬ (5 < r.circuits.length) by omega, dite_false, if_true] at h5
    exact (canonicalWalkSampleFinEquiv _ _).injective (Fin.ext h5)
  cases k
  cases k'
  simp only at hoff hseed
  subst hoff hseed
  rfl

theorem thr_digits_injective (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k k' : RCFive.RowKeys.ThrKey a r L target)
    (h : keyDigits a (.thr r four L target) (some k) = keyDigits a (.thr r four L target) (some k')) :
    k = k' := by
  have hsel : k.selection = k'.selection := by
    funext j
    have hj := congrFun h ⟨j.val, by have := j.isLt; omega⟩
    rw [keyDigits_thr, keyDigits_thr] at hj
    simp only [dif_pos j.isLt] at hj
    exact Fin.ext hj
  have hprime : k.prime = k'.prime := by
    have h4 := congrFun h ⟨4, by omega⟩
    rw [keyDigits_thr, keyDigits_thr] at h4
    simp only [show ¬ (4 < r.circuits.length) by omega, dite_false, if_true] at h4
    exact (primeIndexFinEquiv _).injective (Fin.ext h4)
  have hseed : k.seed = k'.seed := by
    have h5 := congrFun h ⟨5, by omega⟩
    rw [keyDigits_thr, keyDigits_thr] at h5
    simp only [show ¬ (5 < r.circuits.length) by omega, dite_false,
      show ¬ ((5 : ℕ) = 4) by omega, if_false, if_true] at h5
    exact (canonicalWalkSampleFinEquiv _ _).injective (Fin.ext h5)
  have h6 := congrFun h ⟨6, by omega⟩
  rw [keyDigits_thr, keyDigits_thr] at h6
  simp only [show ¬ (6 < r.circuits.length) by omega, dite_false,
    show ¬ ((6 : ℕ) = 4) by omega, show ¬ ((6 : ℕ) = 5) by omega, if_false, if_true] at h6
  cases k with
  | mk sel p seed res =>
    cases k' with
    | mk sel' p' seed' res' =>
      simp only at hsel hprime hseed h6
      subst hsel hprime hseed
      have hres : res = res' := Fin.ext h6
      subst hres
      rfl

/-- The digits determine the key (and `done`). -/
theorem keyDigits_injective (a : DecompositionAlgorithm) (r : Request) (c c' : Option (rcKey a r))
    (h : keyDigits a r c = keyDigits a r c') : c = c' := by
  have h7 := congrFun h ⟨7, by omega⟩
  cases c with
  | none =>
    cases c' with
    | none => rfl
    | some k' =>
      rw [keyDigits_none] at h7
      cases r with
      | terminal => exact PEmpty.elim k'
      | sym r four L target =>
        rw [keyDigits_sym] at h7
        simp only [show ¬ (7 < r.circuits.length) by omega, dite_false,
          show ¬ ((7 : ℕ) = 5) by omega, if_false, if_true] at h7
        omega
      | thr r four L target =>
        rw [keyDigits_thr] at h7
        simp only [show ¬ (7 < r.circuits.length) by omega, dite_false,
          show ¬ ((7 : ℕ) = 4) by omega, show ¬ ((7 : ℕ) = 5) by omega,
          show ¬ ((7 : ℕ) = 6) by omega, if_false, if_true] at h7
        omega
  | some k =>
    cases c' with
    | none =>
      rw [keyDigits_none] at h7
      cases r with
      | terminal => exact PEmpty.elim k
      | sym r four L target =>
        rw [keyDigits_sym] at h7
        simp only [show ¬ (7 < r.circuits.length) by omega, dite_false,
          show ¬ ((7 : ℕ) = 5) by omega, if_false, if_true] at h7
        omega
      | thr r four L target =>
        rw [keyDigits_thr] at h7
        simp only [show ¬ (7 < r.circuits.length) by omega, dite_false,
          show ¬ ((7 : ℕ) = 4) by omega, show ¬ ((7 : ℕ) = 5) by omega,
          show ¬ ((7 : ℕ) = 6) by omega, if_false, if_true] at h7
        omega
    | some k' =>
      cases r with
      | terminal => exact PEmpty.elim k
      | sym r four L target => exact congrArg some (sym_digits_injective a r four L target k k' h)
      | thr r four L target => exact congrArg some (thr_digits_injective a r four L target k k' h)

/-! ## The layout -/

/-- The fixed row bank, given the writer's private scratch count `w` and scrub width `R`. -/
def digitLayout (a : DecompositionAlgorithm) (w : ℕ) (R : Request → ℕ) (cR dR : ℕ)
    (hR : ∀ r, R r ≤ cR * (r.smallSize a)^dR) : Layout a (rcFiveKeys a) where
  tapes := 10 + w
  output := ⟨1, by omega⟩
  outputFresh := by simp
  scratch := fun i => decide (10 ≤ i.val)
  scratchOutput := by simp
  cursorPort := fun i => decide (2 ≤ i.val ∧ i.val < 10)
  resident := fun r i => if i.val = 0 then RepairOrdinary.frame (Request.input a r) else []
  cursor := fun r c i =>
    if h : 2 ≤ i.val ∧ i.val < 10 then
      RepairOrdinary.frame (binary (fieldWidth a r) (keyDigits a r c ⟨i.val - 2, by omega⟩))
    else []
  inputResident := by
    intro r i hi
    refine ⟨by simp [hi], by simp [hi], by simp [hi]⟩
  width := R
  widthCoefficient := cR
  widthDegree := dR
  width_le := hR

variable {a : DecompositionAlgorithm} {w : ℕ} {R : Request → ℕ} {cR dR : ℕ}
  {hR : ∀ r, R r ≤ cR * (r.smallSize a)^dR}

/-- Fixed width: every cursor port has the same length for every code. -/
theorem cursor_length (r : Request) (c : Option (rcKey a r)) (i : Fin (10 + w))
    (hi : (digitLayout a w R cR dR hR).cursorPort i = true) :
    ((digitLayout a w R cR dR hR).cursor r c i).length = 2 * fieldWidth a r + 1 := by
  have h : 2 ≤ i.val ∧ i.val < 10 := by simpa [digitLayout] using hi
  simp [digitLayout, h]

/-- The code is injective on actual keys and `done`. -/
theorem code_injective (r : Request) (c c' : Option (rcKey a r)) (hc : CodeValid a r c) (hc' : CodeValid a r c')
    (h : ∀ i, (digitLayout a w R cR dR hR).cursor r c i = (digitLayout a w R cR dR hR).cursor r c' i) :
    c = c' := by
  apply keyDigits_injective
  funext j
  have hj := h (⟨j.val + 2, by omega⟩ : Fin (10 + w))
  have hp : 2 ≤ j.val + 2 ∧ j.val + 2 < 10 := by omega
  simp only [digitLayout, dif_pos hp] at hj
  have hb := RecoveryColdCanonical.frame_injective hj
  have hv := (binary_value _ _ (digit_lt_pow a r c hc _)).symm.trans
    ((congrArg RadixSemantics.value hb).trans (binary_value _ _ (digit_lt_pow a r c' hc' _)))
  have hfin : (⟨j.val + 2 - 2, by omega⟩ : Fin 8) = j := Fin.ext (by simp)
  rw [hfin] at hv
  exact hv

/-- Different cursor states give different row banks. -/
theorem bank_injective (r : Request) (c c' : Option (rcKey a r)) (hc : CodeValid a r c) (hc' : CodeValid a r c')
    (out : List Bool)
    (h : (digitLayout a w R cR dR hR).bank r c out = (digitLayout a w R cR dR hR).bank r c' out) :
    c = c' := by
  apply code_injective r c c' hc hc'
  intro i
  by_cases hi : 2 ≤ i.val ∧ i.val < 10
  · have he := congrFun h i
    have hne : i ≠ (digitLayout a w R cR dR hR).output := by
      intro hi'
      have := congrArg Fin.val hi'
      simp [digitLayout] at this
      omega
    have hs : (digitLayout a w R cR dR hR).scratch i = false := by simp [digitLayout]; omega
    have hcp : (digitLayout a w R cR dR hR).cursorPort i = true := by simp [digitLayout, hi]
    simp only [Layout.bank, hne, hs, hcp, if_false, if_true] at he
    exact he
  · simp [digitLayout, hi]

/-- A machine halted at its start cannot move the cursor between different codes. -/
theorem halted_cannot_advance {s : ℕ} (M : Machine (10 + w) s) (hM : M.halted M.start = true)
    (n : ℕ) (r : Request) (c c' : Option (rcKey a r)) (hc : CodeValid a r c) (hc' : CodeValid a r c')
    (hne : c ≠ c') (out : List Bool) (H H' : Fin (10 + w) → ℕ)
    (h : Step M n H ((digitLayout a w R cR dR hR).bank r c out) H'
      ((digitLayout a w R cR dR hR).bank r c' out)) : False := by
  obtain ⟨res, hres, _, ht, _⟩ := h
  have hz : runFrom M 0 ⟨M.start, H, (digitLayout a w R cR dR hR).bank r c out⟩ =
      some ⟨⟨M.start, H, (digitLayout a w R cR dR hR).bank r c out⟩, 0, _⟩ :=
    runFrom_zero_of_halted M _ hM
  have hmore := runFrom_moreFuel M 0 n _ _ hz
  rw [Nat.zero_add, hres] at hmore
  have hf := congrArg (fun x => Option.map (fun y => y.final.tapes) x) hmore
  simp only [Option.map_some] at hf
  have hb := (Option.some.inj hf).symm.trans ht
  exact hne (bank_injective r c c' hc hc' out hb)

end
end NearCubicWires.PacketsConstruction
