import Proof.Wire_3_5.PrimTTabMany

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.SymTab
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.SupplierPipeline

/-! ## The block's slots -/

def prepSlB : Fin 13 → Fin 1781 := ![0, 3, 1, 2, 5, 1712, 1678, 1702, 1703, 1713, 1714, 1715, 1716]
def polyVB (j : ℕ) : ℕ := if j = 0 then 1712 else if j = 55 then 1698 else if j < 55 then 1716 + j else 1715 + j
def polySlB (j : Fin 66) : Fin 1781 := ⟨polyVB j.val, by have := j.isLt; unfold polyVB; split_ifs <;> omega⟩
def chainSlB (j : Fin 1708) : Fin 1781 := ⟨j.val + 4, by have := j.isLt; omega⟩

theorem prepSlB_inj : Function.Injective prepSlB := by decide
theorem polySlB_inj : Function.Injective polySlB := by
  intro a b h
  have hv : polyVB a.val = polyVB b.val := congrArg Fin.val h
  have := a.isLt; have := b.isLt
  apply Fin.ext; unfold polyVB at hv; split_ifs at hv <;> omega
theorem chainSlB_inj : Function.Injective chainSlB := by
  intro a b h
  have hv : a.val + 4 = b.val + 4 := congrArg Fin.val h
  exact Fin.ext (by omega)

noncomputable def prepDB := RecoveryFocus.machine prepSlB (Rewind.machine (prepW (nr := 0) spP).toProg.compile)
noncomputable def polyDB := RecoveryFocus.machine polySlB (PCPSerializerCapacity.Power.machine 26 cC)
noncomputable def chainDB := RecoveryFocus.machine chainSlB SourceRequest.ThrOriginal.chainA

/-- **The THR decode block.** -/
noncomputable def thrBlockM := Composition.machine prepDB (Composition.machine polyDB chainDB)

/-- The block's entry: the framed `natWord`, `1^n`, `1^L`, the result cell. -/
def blockIn (code n L : ℕ) : Fin 1781 → List Bool := fun i =>
  if i.val = 0 then frame (natWord code) else if i.val = 1 then List.replicate n true
  else if i.val = 2 then List.replicate L true else if i.val = 3 then [false] else []

theorem blockIn_blank (code n L : ℕ) (i : Fin 1781) (h : 4 ≤ i.val) : blockIn code n L i = [] := by
  unfold blockIn; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

noncomputable def B2 (code n L : ℕ) (o2 : Fin 13 → List Bool) := install prepSlB (blockIn code n L) o2
noncomputable def B3 (code n L : ℕ) (o2 : Fin 13 → List Bool) (o3 : Fin 66 → List Bool) := install polySlB (B2 code n L o2) o3
noncomputable def B4 (code n L : ℕ) (o2 : Fin 13 → List Bool) (o3 : Fin 66 → List Bool) (o4 : Fin 1708 → List Bool) :=
  install chainSlB (B3 code n L o2 o3) o4

theorem missB_prep (i : Fin 1781) (h : ∀ j : Fin 13, (prepSlB j).val ≠ i.val) (A : Fin 1781 → List Bool)
    (o : Fin 13 → List Bool) : install prepSlB A o i = A i :=
  install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))

theorem missB_poly (i : Fin 1781) (h1 : i.val ≠ 1712) (h2 : i.val ≠ 1698) (h3 : i.val < 1717)
    (A : Fin 1781 → List Bool) (o : Fin 66 → List Bool) : install polySlB A o i = A i := by
  refine install_other _ _ _ _ (fun j e => ?_)
  have hv : polyVB j.val = i.val := congrArg Fin.val e
  unfold polyVB at hv; split_ifs at hv <;> omega

theorem missB_chain (i : Fin 1781) (h : i.val < 4 ∨ 1712 ≤ i.val) (A : Fin 1781 → List Bool) (o : Fin 1708 → List Bool) :
    install chainSlB A o i = A i := by
  refine install_other _ _ _ _ (fun j e => ?_)
  have hv : j.val + 4 = i.val := congrArg Fin.val e
  have := j.isLt; omega

theorem prepSlB_val (j : Fin 13) : (prepSlB j).val =
    [0, 3, 1, 2, 5, 1712, 1678, 1702, 1703, 1713, 1714, 1715, 1716].getD j.val 0 := by
  fin_cases j <;> rfl

theorem entryB_prep (code n L : ℕ) : ∀ j, blockIn code n L (prepSlB j) = prepIn code n L j := by
  intro j
  rw [prepIn_val]
  fin_cases j <;> first | rfl | exact blockIn_blank code n L _ (by decide)

theorem entryB_poly (code n L k : ℕ) (o2 : Fin 13 → List Bool) (h5 : o2 5 = List.replicate (k + 1) true) :
    ∀ j, B2 code n L o2 (polySlB j) = RepairSource.ProjectionNormalization.DimensionPolynomial.input 26 (k + 1) j := by
  intro j
  unfold RepairSource.ProjectionNormalization.DimensionPolynomial.input B2
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show polySlB j = prepSlB 5 from Fin.ext (by simp [polySlB, polyVB, h0]; rfl),
      install_slot _ prepSlB_inj, h5]
  · rw [if_neg h0]
    have hv : 1717 ≤ (polySlB j).val ∨ (polySlB j).val = 1698 := by
      have := j.isLt; simp only [polySlB, polyVB]; split_ifs <;> omega
    rw [missB_prep _ (fun k e => by
      have := prepSlB_val k; fin_cases k <;> simp_all <;> omega)]
    exact blockIn_blank code n L _ (by omega)

theorem entryB_chain (code n L P : ℕ) (bits : List Bool) (o2 : Fin 13 → List Bool) (o3 : Fin 66 → List Bool)
    (h4 : o2 4 = frame bits) (h6 : o2 6 = UnaryTemplate.tape n) (h7 : o2 7 = List.replicate L true)
    (h8 : o2 8 = List.replicate L true) (h55 : o3 55 = List.replicate P true) :
    ∀ j, B3 code n L o2 o3 (chainSlB j) = AppendOutputFrame.input (SourceRequest.ThrOriginal.input P n L L bits) j := by
  intro j
  rw [SourceRequest.ThrOriginal.input_at]
  unfold SourceRequest.ThrOriginal.thrAt B3 B2
  have hj := j.isLt
  have cv : (chainSlB j).val = j.val + 4 := rfl
  by_cases e1 : j.val = 1
  · rw [if_pos e1, missB_poly _ (by omega) (by omega) (by omega),
      show chainSlB j = prepSlB 4 from Fin.ext (by rw [cv, e1]; rfl), install_slot _ prepSlB_inj, h4]
  rw [if_neg e1]
  by_cases e2 : j.val = 1674
  · rw [if_pos e2, missB_poly _ (by omega) (by omega) (by omega),
      show chainSlB j = prepSlB 6 from Fin.ext (by rw [cv, e2]; rfl), install_slot _ prepSlB_inj, h6]
  rw [if_neg e2]
  by_cases e3 : j.val = 1694
  · rw [if_pos e3, show chainSlB j = polySlB 55 from Fin.ext (by rw [cv, e3]; rfl), install_slot _ polySlB_inj, h55]
  rw [if_neg e3]
  by_cases e4 : j.val = 1698
  · rw [if_pos e4, missB_poly _ (by omega) (by omega) (by omega),
      show chainSlB j = prepSlB 7 from Fin.ext (by rw [cv, e4]; rfl), install_slot _ prepSlB_inj, h7]
  rw [if_neg e4]
  by_cases e5 : j.val = 1699
  · rw [if_pos e5, missB_poly _ (by omega) (by omega) (by omega),
      show chainSlB j = prepSlB 8 from Fin.ext (by rw [cv, e5]; rfl), install_slot _ prepSlB_inj, h8]
  rw [if_neg e5, missB_poly _ (by omega) (by omega) (by omega)]
  rw [missB_prep _ (fun k e => by have := prepSlB_val k; fin_cases k <;> simp_all <;> omega)]
  exact blockIn_blank code n L _ (by omega)

open PacketProduction in
/-- The block's fuel. -/
noncomputable def thrBlockCost {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) (L : ℕ) : ℕ :=
  let code := encodeNormalizedThresholdThresholdCircuit c
  let k := natBitLength code
  (2 * prepCost k n L + 2) + 1 + (PCPSerializerCapacity.Power.budget 26 cC (k + 1) + 1 +
    (2 * SourceRequest.ThrOriginal.wFuel (cC * (k + 1 + 1) ^ 26) n (binary k code) + 4 * (thrWord c).length + 7))

open PacketProduction in
/-- **The THR decode block**: from the framed `natWord` of `c`'s code, `1^n`, `1^L` (`c.descriptionBits ≤ L`) and the
result cell, the native word `thrWord c` on tape `1692`, three blank register tapes of `n + L + 1` cells on
`1713`-`1715`; the inputs and the cell are kept, every head returns to `0`. -/
theorem thrBlock_step {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) (L : ℕ) (hL : c.descriptionBits ≤ L) :
    ∃ out : Fin 1781 → List Bool,
      Step thrBlockM (thrBlockCost c L) (fun _ => 0) (blockIn (encodeNormalizedThresholdThresholdCircuit c) n L)
        (fun _ => 0) out ∧
      out 0 = frame (natWord (encodeNormalizedThresholdThresholdCircuit c)) ∧ out 1 = List.replicate n true ∧
      out 2 = List.replicate L true ∧ out 3 = [false] ∧ out 1692 = thrWord c ∧
      out 1713 = List.replicate (n + L + 1) false ∧ out 1714 = List.replicate (n + L + 1) false ∧
      out 1715 = List.replicate (n + L + 1) false := by
  set code := encodeNormalizedThresholdThresholdCircuit c with hcode
  set k := natBitLength code with hk
  set P := cC * (k + 1 + 1) ^ 26 with hP
  have zH : ∀ {t : ℕ} (sl : Fin t → Fin 1781), dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
    fun sl => dockH_existing sl _ _ (fun _ => rfl)
  obtain ⟨o2, s2, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := prepStage code n L
  have d2 := s2.dock prepSlB prepSlB_inj (fun _ => 0) (blockIn code n L) (fun _ => rfl) (entryB_prep code n L)
  rw [zH] at d2
  obtain ⟨o3, s3, q0, q55⟩ := BlockPlatform.UnaryCalc.poly_step 26 cC (k + 1)
  have d3 := s3.dock polySlB polySlB_inj (fun _ => 0) (B2 code n L o2) (fun _ => rfl) (entryB_poly code n L k o2 p5)
  rw [zH] at d3
  obtain ⟨o4, s4, -, r1688⟩ := SourceRequest.ThrOriginal.chainA_run c P L L (binary k code)
    (by rw [binary_length, capacity_eq]) (thrBits_decode c) ((thr_wire_le_desc c).trans hL) hL
  have d4 := s4.dock chainSlB chainSlB_inj (fun _ => 0) (B3 code n L o2 o3) (fun _ => rfl)
    (entryB_chain code n L P (binary k code) o2 o3 p4 p6 p7 p8 q55)
  rw [zH] at d4
  have run := d2.seq (d3.seq d4)
  have run' : Step thrBlockM _ (fun _ => 0) (blockIn code n L) (fun _ => 0) (B4 code n L o2 o3 o4) := run
  refine ⟨B4 code n L o2 o3 o4, run'.enlarge (by unfold thrBlockCost; exact le_refl _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold B4; rw [missB_chain _ (by decide)]; unfold B3; rw [missB_poly _ (by decide) (by decide) (by decide)]
    unfold B2; rw [show (0 : Fin 1781) = prepSlB 0 from rfl, install_slot _ prepSlB_inj, p0]
  · unfold B4; rw [missB_chain _ (by decide)]; unfold B3; rw [missB_poly _ (by decide) (by decide) (by decide)]
    unfold B2; rw [show (1 : Fin 1781) = prepSlB 2 from rfl, install_slot _ prepSlB_inj, p2]
  · unfold B4; rw [missB_chain _ (by decide)]; unfold B3; rw [missB_poly _ (by decide) (by decide) (by decide)]
    unfold B2; rw [show (2 : Fin 1781) = prepSlB 3 from rfl, install_slot _ prepSlB_inj, p3]
  · unfold B4; rw [missB_chain _ (by decide)]; unfold B3; rw [missB_poly _ (by decide) (by decide) (by decide)]
    unfold B2; rw [show (3 : Fin 1781) = prepSlB 1 from rfl, install_slot _ prepSlB_inj, p1]
  · unfold B4; rw [show (1692 : Fin 1781) = chainSlB 1688 from rfl, install_slot _ chainSlB_inj, r1688]
  · unfold B4; rw [missB_chain _ (by decide)]; unfold B3; rw [missB_poly _ (by decide) (by decide) (by decide)]
    unfold B2; rw [show (1713 : Fin 1781) = prepSlB 9 from rfl, install_slot _ prepSlB_inj, p9]
  · unfold B4; rw [missB_chain _ (by decide)]; unfold B3; rw [missB_poly _ (by decide) (by decide) (by decide)]
    unfold B2; rw [show (1714 : Fin 1781) = prepSlB 10 from rfl, install_slot _ prepSlB_inj, p10]
  · unfold B4; rw [missB_chain _ (by decide)]; unfold B3; rw [missB_poly _ (by decide) (by decide) (by decide)]
    unfold B2; rw [show (1715 : Fin 1781) = prepSlB 11 from rfl, install_slot _ prepSlB_inj, p11]

end NearCubicWires.WireExponent3_5.PrimT.ThrTab
