import Proof.Wire_3_5.PrimTCarLayout
import Proof.Wire_3_5.PrimTTabSym
import Proof.SourceAssembly.SourceRequestTermBridge

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.CarTable
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.CarWM
open NearCubicWires.WireExponent3_5.PrimT.CarStages NearCubicWires.WireExponent3_5.PrimT.CarFold
open NearCubicWires.WireExponent3_5.PrimT.CarBounds NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## Facts at a call -/

theorem rawAtoms_len {n : ℕ} (W : ℕ) (X : List (NormalizedThresholdGate n)) :
    ((CarRound.rawAtoms W X).flatMap frame).length = X.length * (2 * W + 1) := by
  induction X with
  | nil => simp [CarRound.rawAtoms]
  | cons g X ih =>
    simp only [CarRound.rawAtoms, List.map_cons, List.flatMap_cons, List.length_append, frame_length,
      binary_length] at ih ⊢
    rw [ih, List.length_cons]; ring

theorem stream_eq {n : ℕ} (W : ℕ) (X : Stars.Carrier n) :
    PCPPNativeCanonicalWalk.atomStream W (PCPPNativeCanonicalTree.tree X.code).atoms =
      (CarRound.rawAtoms W X).flatMap frame := by
  rw [CarrierFormat.atomStream_code]; simp [CarRound.rawAtoms, List.flatMap_map]

/-- **Every atom's framed native word is bounded by base's per-atom budget.** -/
theorem gate_len_le {n : ℕ} (W : ℕ) (g : NormalizedThresholdGate n) (hg : CarrierFormat.gateCode g < 2 ^ W) :
    (frame (tabGW g)).length ≤ gateB W := by
  obtain ⟨o, r, t⟩ := CarGate.gate_run g (binary W (CarrierFormat.gateCode g)) (binary_value _ _ hg)
  have hl := ready_lengths r (2 * W + 1) (fun i => by
    rw [CarRound.gcIn_val]; split_ifs
    · rw [frame_length, binary_length]
    · simp) 1033
  rw [t] at hl
  have hb := CarGate.budget_bound (binary W (CarrierFormat.gateCode g))
  rw [binary_length] at hb
  unfold gateB
  rcases le_max_iff.mp hl with h | h <;> omega

theorem tabSeg_len_le {n : ℕ} (W : ℕ) (X : List (NormalizedThresholdGate n))
    (hX : ∀ g ∈ X, CarrierFormat.gateCode g < 2 ^ W) : (tabSeg X).length ≤ X.length * gateB W := by
  induction X with
  | nil => simp [tabSeg]
  | cons g X ih =>
    rw [tabSeg_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := gate_len_le W g (hX g (by simp))
    have := ih (fun g' hg' => hX g' (by simp [hg']))
    omega

/-- **Every atom is within the table's bounds** at width `tabH X` and register capacity `n + L`. -/
theorem carGateOk {n : ℕ} (X : List (NormalizedThresholdGate n)) (L : ℕ) (hL : ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ n + L) : ∀ g ∈ X, GateOk (n + L) (tabH X) g := by
  intro g hg
  obtain ⟨hw, hθ, hn⟩ := tab_nbl_le X g hg
  have hgL := hL g hg
  have ht := SymTab.thr_nbl_le g
  have hnb := PolynomialClock.natBitLength_le_succ n
  refine ⟨fun j => ⟨by have := hw j; omega, by have := SymTab.weight_nbl_le g j; omega⟩, by omega, by omega,
    by omega, by omega, by omega, h2⟩

theorem value_eq (W : ℕ) : BlockPlatform.UnaryCalc.value 50 cC2 (W + 1) = cC2 * (W + 2) ^ 50 := rfl

/-- The atom loop's entry, from the bank's values at the loop's tapes. -/
theorem fold_entry {n : ℕ} (W T : ℕ) (X : List (NormalizedThresholdGate n)) (B : Fin 1357 → List Bool)
    (hS : B 45 = (CarRound.rawAtoms W X).flatMap frame) (hK : B 303 = List.replicate T false)
    (hA : B 304 = accHdr) (hscr : ∀ t : Fin 1357, 305 ≤ t.val → t.val ≤ 1342 → B t = List.replicate T false)
    (hD : B 291 = List.replicate T true) (hC : B 1343 = List.replicate (T + 1) false)
    (hN : B 56 = RepairSource.VerifierDecoding.CompareMachine.word X.length) :
    ∀ j, B (foldSl j) = Fin.addCases (m := 1041 + 2) (n := 1) (motive := fun _ => List Bool)
      (roundTapes (padScratch CarFold.scr T (Qc W T X 0)) T (T + 1))
      (fun _ => RepairSource.VerifierDecoding.CompareMachine.word X.length) j := by
  intro j; rw [foldBank_val]
  have hjl := j.isLt
  have hv : (foldSl j).val = if j.val = 0 then 45 else if j.val = 1041 then 291 else if j.val = 1042 then 1343
      else if j.val = 1043 then 56 else 302 + j.val := rfl
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show foldSl j = 45 from Fin.ext (by rw [hv, if_pos h0]; rfl), hS]
  rw [if_neg h0]
  by_cases h1 : j.val = 1
  · rw [if_pos h1, show foldSl j = 303 from Fin.ext (by rw [hv]; simp [h1]), hK]
    simp [ZeroPadding.pad]
  rw [if_neg h1]
  by_cases h2' : j.val = 2
  · rw [if_pos h2', show foldSl j = 304 from Fin.ext (by rw [hv]; simp [h2']), hA]
    simp [tabSeg]
  rw [if_neg h2']
  by_cases h3 : j.val < 1041
  · rw [if_pos h3, hscr _ (by rw [hv]; split_ifs <;> omega) (by rw [hv]; split_ifs <;> omega)]
  rw [if_neg h3]
  by_cases h4 : j.val = 1041
  · rw [if_pos h4, show foldSl j = 291 from Fin.ext (by rw [hv]; simp [h4]), hD]
  rw [if_neg h4]
  by_cases h5 : j.val = 1042
  · rw [if_pos h5, show foldSl j = 1343 from Fin.ext (by rw [hv]; simp [h5]), hC]
  rw [if_neg h5]
  have h6 : j.val = 1043 := by omega
  rw [show foldSl j = 56 from Fin.ext (by rw [hv]; simp [h6]), hN]

/-! ## The machine's fuel -/

/-- **The carrier table's fuel.** -/
noncomputable def carTableCost {n : ℕ} (X : Stars.Carrier n) (L : ℕ) : ℕ :=
  let W := natBitLength X.code
  let T := BlockPlatform.UnaryCalc.value 50 cC2 (W + 1)
  let h := tabH X
  1 + 1 + ((2 * prepCost W n L + 2) + 1 + (CloseoutWitness.CanonicalTest.budget (binary W X.code) + 1 +
    (PCPSerializerCapacity.Power.budget 50 cC2 (W + 1) + 1 + ((2 * 15 + 2) + 1 + ((2 * T + 4) + 1 +
    ((1 + 1 + (X.length * (foldCw W X.length (tabSeg X).length + 1 + (2 * T + 4 + 1 + 0) + 2) + X.length + 3 + 1 +
      1)) + 1 + ((2 * (scanCost 0 [] h + 4) + 2) + 1 + ((2 * (scanCost 0 [] h + 4) + 2) + 1 +
    (2 * mskCost n h X.length + 2)))))))))

/-! ## The table -/

/-- **The carrier table**: from `frame (natWord (Carrier.code X))`, `1^n`, `1^L` (every atom's description `< L`,
`2 ≤ n + L`), the machine writes `gatesW h (maskGates X)`, `1^h` and `1^|X|` with `h = tabH X`; the inputs are kept,
every head returns to `0`. -/
theorem carTable_step {n : ℕ} (X : Stars.Carrier n) (L : ℕ) (hL : ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ n + L) :
    ∃ tout : Fin 1357 → List Bool,
      Step carTableM (carTableCost X L) (fun _ => 0) (carIn X.code n L) (fun _ => 0) tout ∧
      tout 0 = frame (natWord X.code) ∧ tout 1 = List.replicate n true ∧ tout 2 = List.replicate L true ∧
      tout 3 = gatesW (tabH X) (maskGates X) ∧ tout 4 = List.replicate (tabH X) true ∧
      tout 5 = List.replicate X.length true := by
  set code := X.code with hcode
  set W := natBitLength code with hWdef
  set bits := binary W code with hbits
  set T := BlockPlatform.UnaryCalc.value 50 cC2 (W + 1) with hT
  set c := X.length with hc
  have hcodeW : code < 2 ^ W := CompilerMachine.Pool.lt_pow_natBitLength code
  have hval : RadixSemantics.value bits = code := binary_value _ _ hcodeW
  have hatoms : (PCPPNativeCanonicalTree.tree code).atoms = X.map CarrierFormat.gateCode :=
    CarrierFormat.tree_atoms_code X
  have hW : ∀ g ∈ X, CarrierFormat.gateCode g < 2 ^ W := fun g hg =>
    SourceRequest.TermBridge.atom_lt W code _ hcodeW (by rw [hatoms]; exact List.mem_map_of_mem hg)
  have zH : ∀ {t : ℕ} (sl : Fin t → Fin 1357), dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
    fun sl => dockH_existing sl _ _ (fun _ => rfl)
  set B0 := carIn code n L with hB0
  have b0 : ∀ t : Fin 1357, 3 ≤ t.val → B0 t = [] := fun t ht => carIn_blank code n L t ht
  -- 1: the cell
  have d1 := cell_step.dock cellSl cellSl_inj (fun _ => 0) B0 (fun _ => rfl) (fun _ => b0 6 (by decide))
  rw [zH] at d1
  set B1 := install cellSl B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 1357, t.val ≠ 6 → B1 t = B0 t := fun t h => miss_cell B0 t h _
  -- 2: the preparation
  obtain ⟨o2, s2, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := SymTab.prepStage code n L
  have d2 := s2.dock prepSl prepSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [SymTab.prepIn_val]
    fin_cases j
    · show B1 0 = _; rw [b1 _ (by decide)]; rfl
    · show B1 6 = _; exact install_slot cellSl cellSl_inj B0 _ 0
    · show B1 1 = _; rw [b1 _ (by decide)]; rfl
    · show B1 2 = _; rw [b1 _ (by decide)]; rfl
    all_goals (show B1 _ = _; rw [b1 _ (by decide), b0 _ (by decide)]; rfl))
  rw [zH] at d2
  set B2 := install prepSl B1 o2 with hB2
  have b2 : ∀ t : Fin 1357, (16 ≤ t.val ∨ (3 ≤ t.val ∧ t.val ≤ 5)) → B2 t = B1 t := fun t h => miss_prep B1 t h _
  have b2h : ∀ j, B2 (prepSl j) = o2 j := fun j => install_slot prepSl prepSl_inj B1 o2 j
  -- 3: the traversal
  obtain ⟨o3, r3, t30, t41, -⟩ := CloseoutWitness.CanonicalTest.fields_run bits
  have d3 := (CarRound.step_of_ready r3).dock ctSl ctSl_inj (fun _ => 0) B2 (fun _ => rfl) (by
    intro j
    show B2 (ctSl j) = (if j.val = 0 then frame bits else [])
    by_cases hj : j.val = 0
    · rw [if_pos hj, show ctSl j = prepSl 4 from Fin.ext (by simp [ctSl, hj]; rfl), b2h, p4]
    · rw [if_neg hj, b2 _ (by simp [ctSl, hj]; omega), b1 _ (by simp [ctSl, hj]; omega),
        b0 _ (by simp [ctSl, hj]; omega)])
  rw [zH] at d3
  set B3 := install ctSl B2 o3 with hB3
  have b3 : ∀ t : Fin 1357, (t.val ≠ 7 ∧ (t.val < 16 ∨ 189 ≤ t.val)) → B3 t = B2 t := fun t h => miss_ct B2 t h _
  have b3h : ∀ j, B3 (ctSl j) = o3 j := fun j => install_slot ctSl ctSl_inj B2 o3 j
  -- 4: the capacity
  obtain ⟨o4, s4, -, q103⟩ := BlockPlatform.UnaryCalc.poly_step 50 cC2 (W + 1)
  have d4 := s4.dock powSl powSl_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro j
    show B3 (powSl j) = (if j.val = 0 then List.replicate (W + 1) true else [])
    by_cases hj : j.val = 0
    · rw [if_pos hj, b3 _ (by simp [powSl, hj]), show powSl j = prepSl 5 from Fin.ext (by simp [powSl, hj]; rfl),
        b2h, p5]
    · rw [if_neg hj, b3 _ (by simp [powSl, hj]; omega), b2 _ (by simp [powSl, hj]; omega),
        b1 _ (by simp [powSl, hj]; omega), b0 _ (by simp [powSl, hj]; omega)])
  rw [zH] at d4
  set B4 := install powSl B3 o4 with hB4
  have b4 : ∀ t : Fin 1357, (t.val ≠ 8 ∧ (t.val < 189 ∨ 302 ≤ t.val)) → B4 t = B3 t := fun t h => miss_pow B3 t h _
  have b4T : B4 291 = List.replicate T true := (install_slot powSl powSl_inj B3 o4 103).trans q103
  -- 5: the accumulator's header
  obtain ⟨o5, s5, e50, e51⟩ := initStage
  have d5 := s5.dock initSl initSl_inj (fun _ => 0) B4 (fun _ => rfl) (by
    intro j; rw [initIn_val]
    fin_cases j
    · show B4 304 = _; rw [b4 _ (by decide), b3 _ (by decide), b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B4 6 = _; rw [b4 _ (by decide), b3 _ (by decide), show (6 : Fin 1357) = prepSl 1 from rfl, b2h, p1]; rfl
    · show B4 1344 = _; rw [b4 _ (by decide), b3 _ (by decide), b2 _ (by decide), b1 _ (by decide),
        b0 _ (by decide)]; rfl)
  rw [zH] at d5
  set B5 := install initSl B4 o5 with hB5
  have b5 : ∀ t : Fin 1357, (t.val ≠ 304 ∧ t.val ≠ 6 ∧ t.val ≠ 1344) → B5 t = B4 t := fun t h => miss_init B4 t h _
  have b5h : ∀ j, B5 (initSl j) = o5 j := fun j => install_slot initSl initSl_inj B4 o5 j
  -- 6: the erase
  have er := RecoveryScratchErase.erase_ready T 0 (fun _ : Fin 1039 => ([] : List Bool)) (fun _ => Nat.zero_le _)
  obtain ⟨re, hre, hte, hhe, hse⟩ := er
  have er' : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 1039) (2 * T + 4) (erIn T) (erOut T) :=
    ⟨re, hre, hte, hhe, hse.le⟩
  have d6 := (CarRound.step_of_ready er').dock eraseSl eraseSl_inj (fun _ => 0) B5 (fun _ => rfl) (by
    intro j; rw [erIn_val]
    have hjl := j.isLt
    by_cases hj : j.val = 1039
    · rw [if_pos hj, show eraseSl j = (291 : Fin 1357) from Fin.ext (by simp [eraseSl, hj]),
        b5 _ (by decide), b4T]
    · rw [if_neg hj]
      have hv : (eraseSl j).val = 303 ∨ (eraseSl j).val = 1343 ∨ (305 ≤ (eraseSl j).val ∧ (eraseSl j).val ≤ 1342) := by
        simp only [eraseSl]; split_ifs <;> omega
      rw [b5 _ (by omega), b4 _ (by omega), b3 _ (by omega), b2 _ (by omega), b1 _ (by omega), b0 _ (by omega)])
  rw [zH] at d6
  set B6 := install eraseSl B5 (erOut T) with hB6
  have b6 : ∀ t : Fin 1357, (t.val ≠ 303 ∧ t.val ≠ 291 ∧ t.val ≠ 1343 ∧ (t.val < 305 ∨ 1343 ≤ t.val)) → B6 t = B5 t :=
    fun t h => miss_erase B5 t h _
  have b6h : ∀ j, B6 (eraseSl j) = erOut T j := fun j => install_slot eraseSl eraseSl_inj B5 _ j
  -- the loop's capacity
  have hcount : c * (2 * W + 1) ≤ max (2 * W + 1) (16 * 1000000000000000000 * (W + 1) ^ 24 + 1) := by
    have hl := ready_lengths r3 (2 * W + 1) (fun i => by
      show (if i.val = 0 then frame bits else []).length ≤ _
      split_ifs
      · rw [frame_length, hbits, binary_length]
      · simp) 30
    rw [t30, binary_length, hval, stream_eq W X, rawAtoms_len] at hl
    have hb : CloseoutWitness.CanonicalTest.budget bits = 16 * 1000000000000000000 * (W + 1) ^ 24 := by
      simp only [CloseoutWitness.CanonicalTest.budget, CloseoutWitness.Reencode.polynomialBudget, hbits, binary_length]
      ring
    rw [hb] at hl
    exact hl
  obtain ⟨cap1, cap2, cap3, cap4⟩ := capacity_ok W c (tabSeg X).length hcount (tabSeg_len_le W X hW)
  rw [← value_eq] at cap1 cap2 cap3 cap4
  -- 7: the atom loop
  have fr := fold_run W X hW T (T + 1) (le_refl _) cap1 (by rw [rawAtoms_len]; exact cap2)
    (by rw [show accHdr.length = 4 from rfl]; exact cap3) cap4
  have f45 : B6 45 = (CarRound.rawAtoms W X).flatMap frame := by
    rw [b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), show (45 : Fin 1357) = ctSl 30 from rfl, b3h, t30,
      binary_length, hval, stream_eq]
  have f303 : B6 303 = List.replicate T false := by
    rw [show (303 : Fin 1357) = eraseSl 0 from rfl, b6h, erOut_val]; simp
  have f304 : B6 304 = accHdr := by
    rw [b6 _ (by decide), show (304 : Fin 1357) = initSl 0 from rfl, b5h, e50]
  have fscr : ∀ t : Fin 1357, 305 ≤ t.val → t.val ≤ 1342 → B6 t = List.replicate T false := by
    intro t h1 h2
    rw [show t = eraseSl ⟨t.val - 304, by omega⟩ from Fin.ext (by simp only [eraseSl]; split_ifs <;> omega), b6h,
      erOut_val, if_pos (by simp; omega)]
  have f291 : B6 291 = List.replicate T true := by
    rw [show (291 : Fin 1357) = eraseSl 1039 from rfl, b6h, erOut_val]; simp
  have f1343 : B6 1343 = List.replicate (T + 1) false := by
    rw [show (1343 : Fin 1357) = eraseSl 1040 from rfl, b6h, erOut_val]; simp
  have f56 : B6 56 = RepairSource.VerifierDecoding.CompareMachine.word X.length := by
    rw [b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), show (56 : Fin 1357) = ctSl 41 from rfl, b3h, t41, hval,
      hatoms, List.length_map]
  have d7 := (CarRound.step_of_ready fr).dock foldSl foldSl_inj (fun _ => 0) B6 (fun _ => rfl)
    (fold_entry W T X B6 f45 f303 f304 fscr f291 f1343 f56)
  rw [zH] at d7
  set B7 := install foldSl B6 (Fin.addCases (m := 1041 + 2) (n := 1) (motive := fun _ => List Bool)
    (roundTapes (padScratch CarFold.scr T (Qc W T X c)) T (T + 1))
    (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c)) with hB7
  have b7 : ∀ t : Fin 1357, (t.val ≠ 45 ∧ t.val ≠ 56 ∧ t.val ≠ 291 ∧ t.val ≠ 1343 ∧ (t.val < 303 ∨ 1343 ≤ t.val)) →
      B7 t = B6 t := fun t h => miss_fold B6 t h _
  have b7A : B7 304 = accHdr ++ tabSeg X := by
    have := install_slot foldSl foldSl_inj B6 (Fin.addCases (m := 1041 + 2) (n := 1) (motive := fun _ => List Bool)
      (roundTapes (padScratch CarFold.scr T (Qc W T X c)) T (T + 1))
      (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c)) 2
    rw [foldBank_val] at this
    simp [hc] at this
    exact this
  -- 8, 9: the scans
  have hwd : accHdr ++ tabSeg X = natWord 0 ++ (frame [] ++ tabSeg X) := by rw [hdr_eq]; simp
  have hk0 : natBitLength 0 ≤ n + L := by have := PolynomialClock.natBitLength_le_succ 0; omega
  obtain ⟨o8, s8, t80, t81, t82, t83, t84, t85, t86, t87⟩ := SymTab.scanStage (n + L) 0 [] X (accHdr ++ tabSeg X)
    hwd hk0
  have d8 := s8.dock scan1Sl scan1Sl_inj (fun _ => 0) B7 (fun _ => rfl) (by
    intro j; rw [SymTab.scanIn_val]
    fin_cases j
    · show B7 304 = _; rw [b7A]; rfl
    · show B7 6 = _; rw [b7 _ (by decide), b6 _ (by decide), show (6 : Fin 1357) = initSl 1 from rfl, b5h, e51]; rfl
    · show B7 1345 = _; rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B7 1346 = _; rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B7 1347 = _; rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B7 5 = _; rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B7 1348 = _; rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B7 12 = _; rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        show (12 : Fin 1357) = prepSl 9 from rfl, b2h, p9]; rfl
    · show B7 1349 = _; rw [b7 _ (by decide), b6 _ (by decide), b5 _ (by decide), b4 _ (by decide), b3 _ (by decide),
        b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl)
  rw [zH] at d8
  set B8 := install scan1Sl B7 o8 with hB8
  have b8 : ∀ t : Fin 1357, (∀ j, (scan1Sl j).val ≠ t.val) → B8 t = B7 t := fun t h => miss_scan1 B7 t h _
  have b8h : ∀ j, B8 (scan1Sl j) = o8 j := fun j => install_slot scan1Sl scan1Sl_inj B7 o8 j
  obtain ⟨o9, s9, t90, t91, t92, t93, t94, t95, t96, t97⟩ := SymTab.scanStage (n + L) 0 [] X (accHdr ++ tabSeg X)
    hwd hk0
  have fresh8 : ∀ t : Fin 1357, 1350 ≤ t.val → t.val ≤ 1356 → B8 t = [] := by
    intro t h1 h2
    rw [b8 _ (by intro j; rw [scan1Sl_val]; fin_cases j <;> simp <;> omega), b7 _ (by omega), b6 _ (by omega),
      b5 _ (by omega), b4 _ (by omega), b3 _ (by omega), b2 _ (by omega), b1 _ (by omega), b0 _ (by omega)]
  have d9 := s9.dock scan2Sl scan2Sl_inj (fun _ => 0) B8 (fun _ => rfl) (by
    intro j; rw [SymTab.scanIn_val]
    fin_cases j
    · show B8 304 = _; rw [show (304 : Fin 1357) = scan1Sl 0 from rfl, b8h, t80]; rfl
    · show B8 6 = _; rw [show (6 : Fin 1357) = scan1Sl 1 from rfl, b8h, t81]; rfl
    · show B8 1350 = _; rw [fresh8 _ (by decide) (by decide)]; rfl
    · show B8 1351 = _; rw [fresh8 _ (by decide) (by decide)]; rfl
    · show B8 1352 = _; rw [fresh8 _ (by decide) (by decide)]; rfl
    · show B8 1353 = _; rw [fresh8 _ (by decide) (by decide)]; rfl
    · show B8 1354 = _; rw [fresh8 _ (by decide) (by decide)]; rfl
    · show B8 12 = _; rw [show (12 : Fin 1357) = scan1Sl 7 from rfl, b8h, t87]; rfl
    · show B8 1355 = _; rw [fresh8 _ (by decide) (by decide)]; rfl)
  rw [zH] at d9
  set B9 := install scan2Sl B8 o9 with hB9
  have b9 : ∀ t : Fin 1357, (∀ j, (scan2Sl j).val ≠ t.val) → B9 t = B8 t := fun t h => miss_scan2 B8 t h _
  have b9h : ∀ j, B9 (scan2Sl j) = o9 j := fun j => install_slot scan2Sl scan2Sl_inj B8 o9 j
  -- 10: the mask table
  obtain ⟨o10, s10, u3, u5, u6⟩ := maskStage (n + L) (tabH X) X (carGateOk X L hL h2)
  have d10 := s10.dock maskSl maskSl_inj (fun _ => 0) B9 (fun _ => rfl) (by
    intro j; rw [mskIn_val]
    fin_cases j
    · show B9 1345 = _; rw [b9 _ (by decide), show (1345 : Fin 1357) = scan1Sl 2 from rfl, b8h, t82]; rfl
    · show B9 6 = _; rw [show (6 : Fin 1357) = scan2Sl 1 from rfl, b9h, t91]; rfl
    · show B9 1346 = _; rw [b9 _ (by decide), show (1346 : Fin 1357) = scan1Sl 3 from rfl, b8h, t83]; rfl
    · show B9 1 = _; rw [b9 _ (by decide), b8 _ (by decide), b7 _ (by decide), b6 _ (by decide), b5 _ (by decide),
        b4 _ (by decide), b3 _ (by decide), show (1 : Fin 1357) = prepSl 2 from rfl, b2h, p2]; rfl
    · show B9 1347 = _; rw [b9 _ (by decide), show (1347 : Fin 1357) = scan1Sl 4 from rfl, b8h, t84]; rfl
    · show B9 3 = _; rw [b9 _ (by decide), b8 _ (by decide), b7 _ (by decide), b6 _ (by decide), b5 _ (by decide),
        b4 _ (by decide), b3 _ (by decide), b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B9 4 = _; rw [b9 _ (by decide), b8 _ (by decide), b7 _ (by decide), b6 _ (by decide), b5 _ (by decide),
        b4 _ (by decide), b3 _ (by decide), b2 _ (by decide), b1 _ (by decide), b0 _ (by decide)]; rfl
    · show B9 1350 = _; rw [show (1350 : Fin 1357) = scan2Sl 2 from rfl, b9h, t92]; rfl
    · show B9 1351 = _; rw [show (1351 : Fin 1357) = scan2Sl 3 from rfl, b9h, t93]; rfl
    · show B9 12 = _; rw [show (12 : Fin 1357) = scan2Sl 7 from rfl, b9h, t97]; rfl
    · show B9 13 = _; rw [b9 _ (by decide), b8 _ (by decide), b7 _ (by decide), b6 _ (by decide), b5 _ (by decide),
        b4 _ (by decide), b3 _ (by decide), show (13 : Fin 1357) = prepSl 10 from rfl, b2h, p10]; rfl
    · show B9 14 = _; rw [b9 _ (by decide), b8 _ (by decide), b7 _ (by decide), b6 _ (by decide), b5 _ (by decide),
        b4 _ (by decide), b3 _ (by decide), show (14 : Fin 1357) = prepSl 11 from rfl, b2h, p11]; rfl
    · show B9 1356 = _; rw [b9 _ (by decide), fresh8 _ (by decide) (by decide)]; rfl)
  rw [zH] at d10
  set B10 := install maskSl B9 o10 with hB10
  have b10 : ∀ t : Fin 1357, (∀ j, (maskSl j).val ≠ t.val) → B10 t = B9 t := fun t h => miss_mask B9 t h _
  have b10h : ∀ j, B10 (maskSl j) = o10 j := fun j => install_slot maskSl maskSl_inj B9 o10 j
  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq (d6.seq (d7.seq (d8.seq (d9.seq d10))))))))
  have run' : Step carTableM _ (fun _ => 0) B0 (fun _ => 0) B10 := run
  refine ⟨B10, run'.enlarge (by unfold carTableCost; exact le_refl _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b10 _ (by decide), b9 _ (by decide), b8 _ (by decide), b7 _ (by decide), b6 _ (by decide), b5 _ (by decide),
      b4 _ (by decide), b3 _ (by decide), show (0 : Fin 1357) = prepSl 0 from rfl, b2h, p0]
  · rw [show (1 : Fin 1357) = maskSl 3 from rfl, b10h, u3]
  · rw [b10 _ (by decide), b9 _ (by decide), b8 _ (by decide), b7 _ (by decide), b6 _ (by decide), b5 _ (by decide),
      b4 _ (by decide), b3 _ (by decide), show (2 : Fin 1357) = prepSl 3 from rfl, b2h, p3]
  · rw [show (3 : Fin 1357) = maskSl 5 from rfl, b10h, u5]
  · rw [show (4 : Fin 1357) = maskSl 6 from rfl, b10h, u6]
  · rw [b10 _ (by decide), b9 _ (by decide), show (5 : Fin 1357) = scan1Sl 5 from rfl, b8h, t85]

end NearCubicWires.WireExponent3_5.PrimT.CarTable
