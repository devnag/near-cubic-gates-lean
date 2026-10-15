import Proof.Wire_3_5.PrimTTabSymStages

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.SymTab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.SupplierPipeline

/-- The global entry: the framed `natWord` of the code, `1^n`, `1^L`. -/
def symIn (code n L : ℕ) : Fin 1789 → List Bool := fun i =>
  if i.val = 0 then frame (natWord code) else if i.val = 1 then List.replicate n true
  else if i.val = 2 then List.replicate L true else []

/-! ## The ambient tapes after each stage -/

noncomputable def A1 (code n L : ℕ) : Fin 1789 → List Bool := install cellSl (symIn code n L) (fun _ => [false])
noncomputable def A2 (code n L : ℕ) (o2 : Fin 13 → List Bool) := install prepSl (A1 code n L) o2
noncomputable def A3 (code n L : ℕ) (o2 : Fin 13 → List Bool) (o3 : Fin 66 → List Bool) := install polySl (A2 code n L o2) o3
noncomputable def A4 (code n L : ℕ) (o2 : Fin 13 → List Bool) (o3 : Fin 66 → List Bool) (o4 : Fin 1708 → List Bool) :=
  install chainSl (A3 code n L o2 o3) o4
noncomputable def A5 (code n L : ℕ) (o2 : Fin 13 → List Bool) (o3 : Fin 66 → List Bool) (o4 : Fin 1708 → List Bool)
    (o5 : Fin 9 → List Bool) := install scanSl (A4 code n L o2 o3 o4) o5
noncomputable def A6 (code n L : ℕ) (o2 : Fin 13 → List Bool) (o3 : Fin 66 → List Bool) (o4 : Fin 1708 → List Bool)
    (o5 : Fin 9 → List Bool) (o6 : Fin 11 → List Bool) := install tabSl (A5 code n L o2 o3 o4 o5) o6

/-! ## Missing a stage -/

theorem miss_cell (i : Fin 1789) (h : i.val ≠ 1721) (A : Fin 1789 → List Bool) (o : Fin 1 → List Bool) :
    install cellSl A o i = A i :=
  install_other _ _ _ _ (fun j e => h (by rw [← e]; rfl))

theorem miss_prep (i : Fin 1789) (h : ∀ j : Fin 13, (prepSl j).val ≠ i.val) (A : Fin 1789 → List Bool)
    (o : Fin 13 → List Bool) : install prepSl A o i = A i :=
  install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))

theorem miss_poly (i : Fin 1789) (h1 : i.val ≠ 1714) (h2 : i.val ≠ 1700) (h3 : i.val < 1725)
    (A : Fin 1789 → List Bool) (o : Fin 66 → List Bool) : install polySl A o i = A i := by
  refine install_other _ _ _ _ (fun j e => ?_)
  have hv : polyV j.val = i.val := congrArg Fin.val e
  unfold polyV at hv; split_ifs at hv <;> omega

theorem miss_chain (i : Fin 1789) (h : i.val < 6 ∨ 1714 ≤ i.val) (A : Fin 1789 → List Bool) (o : Fin 1708 → List Bool) :
    install chainSl A o i = A i := by
  refine install_other _ _ _ _ (fun j e => ?_)
  have hv : j.val + 6 = i.val := congrArg Fin.val e
  have := j.isLt; omega

theorem miss_scan (i : Fin 1789) (h : ∀ j : Fin 9, (scanSl j).val ≠ i.val) (A : Fin 1789 → List Bool)
    (o : Fin 9 → List Bool) : install scanSl A o i = A i :=
  install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))

theorem miss_tab (i : Fin 1789) (h : ∀ j : Fin 11, (tabSl j).val ≠ i.val) (A : Fin 1789 → List Bool)
    (o : Fin 11 → List Bool) : install tabSl A o i = A i :=
  install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))

theorem hit_prep (j : Fin 13) (A : Fin 1789 → List Bool) (o : Fin 13 → List Bool) : install prepSl A o (prepSl j) = o j :=
  install_slot _ prepSl_inj _ _ _
theorem hit_poly (j : Fin 66) (A : Fin 1789 → List Bool) (o : Fin 66 → List Bool) : install polySl A o (polySl j) = o j :=
  install_slot _ polySl_inj _ _ _
theorem hit_chain (j : Fin 1708) (A : Fin 1789 → List Bool) (o : Fin 1708 → List Bool) :
    install chainSl A o (chainSl j) = o j := install_slot _ chainSl_inj _ _ _
theorem hit_scan (j : Fin 9) (A : Fin 1789 → List Bool) (o : Fin 9 → List Bool) : install scanSl A o (scanSl j) = o j :=
  install_slot _ scanSl_inj _ _ _
theorem hit_tab (j : Fin 11) (A : Fin 1789 → List Bool) (o : Fin 11 → List Bool) : install tabSl A o (tabSl j) = o j :=
  install_slot _ tabSl_inj _ _ _

theorem symIn_blank (code n L : ℕ) (i : Fin 1789) (h : 3 ≤ i.val) : symIn code n L i = [] := by
  unfold symIn; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ## The stages' entries -/

theorem prepSl_val (j : Fin 13) : (prepSl j).val =
    [0, 1721, 1, 2, 7, 1714, 1680, 1704, 1705, 1715, 1716, 1717, 1722].getD j.val 0 := by
  fin_cases j <;> rfl

theorem entry_cell (code n L : ℕ) : ∀ j, symIn code n L (cellSl j) = (fun _ => ([] : List Bool)) j :=
  fun _ => symIn_blank code n L _ (by show 3 ≤ 1721; omega)

theorem entry_prep (code n L : ℕ) : ∀ j, A1 code n L (prepSl j) = prepIn code n L j := by
  intro j
  rw [prepIn_val]
  unfold A1
  fin_cases j
  · rw [miss_cell _ (by decide)]; rfl
  · rw [show prepSl ⟨1, by decide⟩ = cellSl 0 from rfl, install_slot _ cellSl_inj]; rfl
  · rw [miss_cell _ (by decide)]; rfl
  · rw [miss_cell _ (by decide)]; rfl
  all_goals (rw [miss_cell _ (by decide)]; exact symIn_blank code n L _ (by decide))

theorem entry_poly (code n L k : ℕ) (o2 : Fin 13 → List Bool) (h5 : o2 5 = List.replicate (k + 1) true) :
    ∀ j, A2 code n L o2 (polySl j) = RepairSource.ProjectionNormalization.DimensionPolynomial.input 26 (k + 1) j := by
  intro j
  unfold RepairSource.ProjectionNormalization.DimensionPolynomial.input A2
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show polySl j = prepSl 5 from Fin.ext (by simp [polySl, polyV, h0]; rfl), hit_prep, h5]
  · rw [if_neg h0]
    have hv : 1725 ≤ (polySl j).val ∨ (polySl j).val = 1700 := by
      have := j.isLt; simp only [polySl, polyV]; split_ifs <;> omega
    rw [miss_prep _ (fun k e => by
      have := prepSl_val k; fin_cases k <;> simp_all <;> omega)]
    unfold A1; rw [miss_cell _ (by omega)]
    exact symIn_blank code n L _ (by omega)

theorem entry_chain (code n L P : ℕ) (bits : List Bool) (o2 : Fin 13 → List Bool) (o3 : Fin 66 → List Bool)
    (h4 : o2 4 = frame bits) (h6 : o2 6 = UnaryTemplate.tape n) (h7 : o2 7 = List.replicate L true)
    (h8 : o2 8 = List.replicate L true) (h55 : o3 55 = List.replicate P true) :
    ∀ j, A3 code n L o2 o3 (chainSl j) = AppendOutputFrame.input (SourceRequest.ThrOriginal.input P n L L bits) j := by
  intro j
  rw [SourceRequest.ThrOriginal.input_at]
  unfold SourceRequest.ThrOriginal.thrAt A3 A2
  have hj := j.isLt
  have cv : (chainSl j).val = j.val + 6 := rfl
  by_cases e1 : j.val = 1
  · rw [if_pos e1, miss_poly _ (by omega) (by omega) (by omega),
      show chainSl j = prepSl 4 from Fin.ext (by rw [cv, e1]; rfl), hit_prep, h4]
  rw [if_neg e1]
  by_cases e2 : j.val = 1674
  · rw [if_pos e2, miss_poly _ (by omega) (by omega) (by omega),
      show chainSl j = prepSl 6 from Fin.ext (by rw [cv, e2]; rfl), hit_prep, h6]
  rw [if_neg e2]
  by_cases e3 : j.val = 1694
  · rw [if_pos e3, show chainSl j = polySl 55 from Fin.ext (by rw [cv, e3]; rfl), hit_poly, h55]
  rw [if_neg e3]
  by_cases e4 : j.val = 1698
  · rw [if_pos e4, miss_poly _ (by omega) (by omega) (by omega),
      show chainSl j = prepSl 7 from Fin.ext (by rw [cv, e4]; rfl), hit_prep, h7]
  rw [if_neg e4]
  by_cases e5 : j.val = 1699
  · rw [if_pos e5, miss_poly _ (by omega) (by omega) (by omega),
      show chainSl j = prepSl 8 from Fin.ext (by rw [cv, e5]; rfl), hit_prep, h8]
  rw [if_neg e5, miss_poly _ (by omega) (by omega) (by omega)]
  rw [miss_prep _ (fun k e => by have := prepSl_val k; fin_cases k <;> simp_all <;> omega)]
  unfold A1; rw [miss_cell _ (by omega)]
  exact symIn_blank code n L _ (by omega)

theorem entry_scan (code n L cap : ℕ) (w : List Bool) (o2 : Fin 13 → List Bool) (o3 : Fin 66 → List Bool)
    (o4 : Fin 1708 → List Bool) (h1 : o2 1 = [false]) (h9 : o2 9 = List.replicate (cap + 1) false)
    (hw : o4 1688 = w) : ∀ j, A4 code n L o2 o3 o4 (scanSl j) = scanIn cap w j := by
  intro j
  rw [scanIn_val]
  unfold A4
  fin_cases j
  · rw [show scanSl ⟨0, by decide⟩ = chainSl 1688 from rfl, hit_chain, hw]; rfl
  · rw [miss_chain _ (by decide)]; unfold A3
    rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
    rw [show scanSl ⟨1, by decide⟩ = prepSl 1 from rfl, hit_prep, h1]; rfl
  all_goals first
    | (rw [miss_chain _ (by decide)]; unfold A3; rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
       rw [show scanSl ⟨7, by decide⟩ = prepSl 9 from rfl, hit_prep, h9]; rfl)
    | (rw [miss_chain _ (by decide)]; unfold A3; rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
       rw [miss_prep _ (by decide)]; unfold A1
       rw [miss_cell _ (by decide)]; exact symIn_blank code n L _ (by decide))

theorem entry_tab (code n L cap h : ℕ) (seg : List Bool) (o2 : Fin 13 → List Bool) (o3 : Fin 66 → List Bool)
    (o4 : Fin 1708 → List Bool) (o5 : Fin 9 → List Bool) (h2 : o2 2 = List.replicate n true)
    (h10 : o2 10 = List.replicate (cap + 1) false) (h11 : o2 11 = List.replicate (cap + 1) false)
    (s1 : o5 1 = [false]) (s2 : o5 2 = seg) (s3 : o5 3 = seg) (s4 : o5 4 = false :: List.replicate h true)
    (s6 : o5 6 = []) (s7 : o5 7 = List.replicate (cap + 1) false) :
    ∀ j, A5 code n L o2 o3 o4 o5 (tabSl j) = tabIn cap seg n h j := by
  intro j
  rw [tabIn_val]
  unfold A5
  fin_cases j
  · rw [show tabSl ⟨0, by decide⟩ = scanSl 2 from rfl, hit_scan, s2]; rfl
  · rw [show tabSl ⟨1, by decide⟩ = scanSl 1 from rfl, hit_scan, s1]; rfl
  · rw [show tabSl ⟨2, by decide⟩ = scanSl 3 from rfl, hit_scan, s3]; rfl
  · rw [miss_scan _ (by decide)]; unfold A4; rw [miss_chain _ (by decide)]; unfold A3
    rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
    rw [show tabSl ⟨3, by decide⟩ = prepSl 2 from rfl, hit_prep, h2]; rfl
  · rw [show tabSl ⟨4, by decide⟩ = scanSl 4 from rfl, hit_scan, s4]; rfl
  · rw [miss_scan _ (by decide)]; unfold A4; rw [miss_chain _ (by decide)]; unfold A3
    rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
    rw [miss_prep _ (by decide)]; unfold A1
    rw [miss_cell _ (by decide)]; exact symIn_blank code n L _ (by decide)
  · rw [show tabSl ⟨6, by decide⟩ = scanSl 6 from rfl, hit_scan, s6]; rfl
  · rw [show tabSl ⟨7, by decide⟩ = scanSl 7 from rfl, hit_scan, s7]; rfl
  · rw [miss_scan _ (by decide)]; unfold A4; rw [miss_chain _ (by decide)]; unfold A3
    rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
    rw [show tabSl ⟨8, by decide⟩ = prepSl 10 from rfl, hit_prep, h10]; rfl
  · rw [miss_scan _ (by decide)]; unfold A4; rw [miss_chain _ (by decide)]; unfold A3
    rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
    rw [show tabSl ⟨9, by decide⟩ = prepSl 11 from rfl, hit_prep, h11]; rfl
  · rw [miss_scan _ (by decide)]; unfold A4; rw [miss_chain _ (by decide)]; unfold A3
    rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
    rw [miss_prep _ (by decide)]; unfold A1
    rw [miss_cell _ (by decide)]; exact symIn_blank code n L _ (by decide)

/-! ## The bounds at a call -/

theorem gate_desc_le {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (i : Fin C.bottomCount) :
    (C.bottom i).descriptionBits + 1 ≤ C.descriptionBits := by
  unfold NormalizedSymmetricThresholdCircuit.descriptionBits
  have := Finset.single_le_sum (f := fun j => (C.bottom j).descriptionBits) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  omega

theorem weight_nbl_le {n : ℕ} (g : NormalizedThresholdGate n) (j : Fin n) :
    natBitLength (g.weight j).natAbs ≤ g.encodingBits := by
  unfold NormalizedThresholdGate.encodingBits
  have := Finset.single_le_sum (f := fun j => intBitLength (g.weight j)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)
  simp only [intBitLength] at this ⊢
  unfold natBitLength
  omega

theorem thr_nbl_le {n : ℕ} (g : NormalizedThresholdGate n) :
    natBitLength (g.threshold - 1).natAbs ≤ g.encodingBits + 1 := by
  have h1 := RepairSource.CloseoutRawRows.strict_gate_bits g
  have h2 : intBitLength (CompilerSemantics.nonStrictAsStrict g).threshold ≤
      (CompilerSemantics.nonStrictAsStrict g).encodingBits := by
    unfold NormalizedThresholdGate.encodingBits; omega
  have h3 : natBitLength (g.threshold - 1).natAbs = intBitLength (CompilerSemantics.nonStrictAsStrict g).threshold := rfl
  omega

/-- **Every gate of `symGates C` is within the table's bounds** at width `tabH` and register capacity `n + L`. -/
theorem symGateOk {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (L : ℕ) (hL : C.descriptionBits ≤ L)
    (h2 : 2 ≤ n + L) : ∀ g ∈ Stars.symGates C, GateOk (n + L) (tabH (Stars.symGates C)) g := by
  intro g hg
  obtain ⟨hw, hθ, hn⟩ := tab_nbl_le (Stars.symGates C) g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  have hd := gate_desc_le C i
  have he : (C.bottom i).descriptionBits = (C.bottom i).gate.encodingBits + n := rfl
  have ht := thr_nbl_le (C.bottom i).gate
  have hnb := PolynomialClock.natBitLength_le_succ n
  refine ⟨fun j => ⟨by have := hw j; omega, by have := weight_nbl_le (C.bottom i).gate j; omega⟩, hθ, by omega,
    by omega, by omega, by omega, h2⟩

theorem symScan_le {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (L : ℕ) (hL : C.descriptionBits ≤ L) :
    natBitLength C.bottomCount ≤ n + L := by
  have := PolynomialClock.natBitLength_le_succ C.bottomCount
  unfold NormalizedSymmetricThresholdCircuit.descriptionBits at hL
  omega

theorem capacity_eq (k : ℕ) : RepairOrdinary.CloseoutRowsCircuitCapacity.capacity k = cC * (k + 1 + 1) ^ 26 := by
  unfold RepairOrdinary.CloseoutRowsCircuitCapacity.capacity; rfl

/-! ## The table machine -/

open PacketProduction in
/-- The machine's fuel. -/
noncomputable def symTableCost {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (L : ℕ) : ℕ :=
  let code := encodeNormalizedSymmetricThresholdCircuit C
  let k := natBitLength code
  let G := Stars.symGates C
  1 + 1 + ((2 * prepCost k n L + 2) + 1 + (PCPSerializerCapacity.Power.budget 26 cC (k + 1) + 1 +
    ((2 * SourceRequest.ThrOriginal.wFuel (cC * (k + 1 + 1) ^ 26) n (binary k code) + 4 * (symWord C).length + 7) + 1 +
    ((2 * (scanCost C.bottomCount (List.ofFn C.top) (tabH G) + 4) + 2) + 1 + (2 * tabCost n (tabH G) G.length + 2)))))

open PacketProduction in
/-- **The SYM gate table**: from `frame (natWord code)`, `1^n`, `1^L` (`C.descriptionBits ≤ L`), the machine writes
`gatesW h (symGates C)`, `1^h` and `1^|symGates C|` with `h = tabH (symGates C)`; the inputs are kept, every head
returns to `0`. -/
theorem symTable_step {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (L : ℕ) (hL : C.descriptionBits ≤ L)
    (h2 : 2 ≤ n + L) :
    ∃ tout : Fin 1789 → List Bool,
      Step symTableM (symTableCost C L) (fun _ => 0) (symIn (encodeNormalizedSymmetricThresholdCircuit C) n L)
        (fun _ => 0) tout ∧
      tout 0 = frame (natWord (encodeNormalizedSymmetricThresholdCircuit C)) ∧ tout 1 = List.replicate n true ∧
      tout 2 = List.replicate L true ∧ tout 3 = gatesW (tabH (Stars.symGates C)) (Stars.symGates C) ∧
      tout 4 = List.replicate (tabH (Stars.symGates C)) true ∧
      tout 5 = List.replicate (Stars.symGates C).length true := by
  set code := encodeNormalizedSymmetricThresholdCircuit C with hcode
  set k := natBitLength code with hk
  set G := Stars.symGates C with hG
  set h := tabH G with hh
  set P := cC * (k + 1 + 1) ^ 26 with hP
  have zH : ∀ {t : ℕ} (sl : Fin t → Fin 1789), dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
    fun sl => dockH_existing sl _ _ (fun _ => rfl)
  -- 1: the cell
  have d1 := cell_step.dock cellSl cellSl_inj (fun _ => 0) (symIn code n L) (fun _ => rfl) (entry_cell code n L)
  rw [zH] at d1
  -- 2: the preparation
  obtain ⟨o2, s2, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := prepStage code n L
  have d2 := s2.dock prepSl prepSl_inj (fun _ => 0) (A1 code n L) (fun _ => rfl) (entry_prep code n L)
  rw [zH] at d2
  -- 3: the capacity
  obtain ⟨o3, s3, q0, q55⟩ := BlockPlatform.UnaryCalc.poly_step 26 cC (k + 1)
  have d3 := s3.dock polySl polySl_inj (fun _ => 0) (A2 code n L o2) (fun _ => rfl) (entry_poly code n L k o2 p5)
  rw [zH] at d3
  -- 4: the decoder chain
  obtain ⟨o4, s4, -, r1688⟩ := symChain_run C P L L (binary k code) (by rw [binary_length, capacity_eq])
    (symBits_decode C) ((sym_wire_le_desc C).trans hL) hL
  have d4 := s4.dock chainSl chainSl_inj (fun _ => 0) (A3 code n L o2 o3) (fun _ => rfl)
    (entry_chain code n L P (binary k code) o2 o3 p4 p6 p7 p8 q55)
  rw [zH] at d4
  -- 5: the scan
  obtain ⟨o5, s5, t0, t1, t2, t3, t4, t5, t6, t7⟩ := scanStage (n + L) C.bottomCount (List.ofFn C.top) G (symWord C)
    (symWord_eq C) (symScan_le C L hL)
  have d5 := s5.dock scanSl scanSl_inj (fun _ => 0) (A4 code n L o2 o3 o4) (fun _ => rfl)
    (entry_scan code n L (n + L) (symWord C) o2 o3 o4 p1 (by rw [p9]) r1688)
  rw [zH] at d5
  -- 6: the unary width and the table
  obtain ⟨o6, s6, u3, u5, u6⟩ := tabStage (n + L) h G (symGateOk C L hL h2)
  have d6 := s6.dock tabSl tabSl_inj (fun _ => 0) (A5 code n L o2 o3 o4 o5) (fun _ => rfl)
    (entry_tab code n L (n + L) h (tabSeg G) o2 o3 o4 o5 p2 (by rw [p10]) (by rw [p11]) t1 t2 t3 t4 t6 t7)
  rw [zH] at d6
  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq d6))))
  have run' : Step symTableM _ (fun _ => 0) (symIn code n L) (fun _ => 0) (A6 code n L o2 o3 o4 o5 o6) := run
  refine ⟨A6 code n L o2 o3 o4 o5 o6, run'.enlarge (by unfold symTableCost; exact le_refl _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold A6; rw [miss_tab _ (by decide)]; unfold A5; rw [miss_scan _ (by decide)]; unfold A4
    rw [miss_chain _ (by decide)]; unfold A3; rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
    rw [show (0 : Fin 1789) = prepSl 0 from rfl, hit_prep, p0]
  · unfold A6; rw [show (1 : Fin 1789) = tabSl 3 from rfl, hit_tab, u3]
  · unfold A6; rw [miss_tab _ (by decide)]; unfold A5; rw [miss_scan _ (by decide)]; unfold A4
    rw [miss_chain _ (by decide)]; unfold A3; rw [miss_poly _ (by decide) (by decide) (by decide)]; unfold A2
    rw [show (2 : Fin 1789) = prepSl 3 from rfl, hit_prep, p3]
  · unfold A6; rw [show (3 : Fin 1789) = tabSl 5 from rfl, hit_tab, u5]
  · unfold A6; rw [show (4 : Fin 1789) = tabSl 6 from rfl, hit_tab, u6]
  · unfold A6; rw [miss_tab _ (by decide)]; unfold A5; rw [show (5 : Fin 1789) = scanSl 5 from rfl, hit_scan, t5]

end NearCubicWires.WireExponent3_5.PrimT.SymTab
