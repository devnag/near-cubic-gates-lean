import Proof.Wire_3_5.PrimTTabThrBlock
import Proof.Wire_3_5.PrimitiveThr

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.SymTab
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.SupplierPipeline

/-! ## Slots -/

/-- The first tape of circuit `j`'s region. -/
def RB (j : ℕ) : ℕ := 15 + j * 1777

def blockV (j k : ℕ) : ℕ := if k = 0 then j else if k = 1 then 4 else if k = 2 then 5 else if k = 3 then 9 else RB j + (k - 4)

/-- Circuit `j`'s decode block. -/
def blockSl (j : ℕ) (hj : j < 4) (k : Fin 1781) : Fin 7123 :=
  ⟨blockV j k.val, by have := k.isLt; unfold blockV RB; split_ifs <;> omega⟩

theorem blockSl_inj (j : ℕ) (hj : j < 4) : Function.Injective (blockSl j hj) := by
  intro a b h
  have hv : blockV j a.val = blockV j b.val := congrArg Fin.val h
  have := a.isLt; have := b.isLt
  apply Fin.ext; unfold blockV RB at hv; split_ifs at hv <;> omega

def cellSlT : Fin 1 → Fin 7123 := fun _ => 9
def tabSlT : Fin 11 → Fin 7123 := ![10, 9, 11, 4, 12, 6, 7, 1724, 1725, 1726, 14]

theorem cellSlT_inj : Function.Injective cellSlT := fun a b _ => Subsingleton.elim a b
theorem tabSlT_inj : Function.Injective tabSlT := by decide

noncomputable def cellDT := RecoveryFocus.machine cellSlT cellM
noncomputable def blockD (j : ℕ) (hj : j < 4) := RecoveryFocus.machine (blockSl j hj) thrBlockM
noncomputable def tabDT := RecoveryFocus.machine tabSlT (Rewind.machine tabW2.toProg.compile)

/-- The call's entry: circuit `j`'s framed `natWord` on slot `j < a`, `1^n`, `1^L`. -/
def thrIn (codes : List ℕ) (n L : ℕ) : Fin 7123 → List Bool := fun i =>
  if h : i.val < codes.length ∧ i.val < 4 then frame (natWord (codes.get ⟨i.val, h.1⟩))
  else if i.val = 4 then List.replicate n true else if i.val = 5 then List.replicate L true else []

theorem thrIn_blank (codes : List ℕ) (n L : ℕ) (i : Fin 7123) (h : 6 ≤ i.val) : thrIn codes n L i = [] := by
  unfold thrIn; rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ## Missing and hitting a block -/

theorem miss_block (j : ℕ) (hj : j < 4) (i : Fin 7123) (h1 : i.val ≠ j) (h2 : i.val ≠ 4) (h3 : i.val ≠ 5)
    (h4 : i.val ≠ 9) (h5 : i.val < RB j ∨ RB j + 1777 ≤ i.val) (A : Fin 7123 → List Bool) (o : Fin 1781 → List Bool) :
    install (blockSl j hj) A o i = A i := by
  refine install_other _ _ _ _ (fun k e => ?_)
  have hv : blockV j k.val = i.val := congrArg Fin.val e
  have := k.isLt
  unfold blockV at hv; split_ifs at hv <;> omega

theorem hit_block (j : ℕ) (hj : j < 4) (k : Fin 1781) (A : Fin 7123 → List Bool) (o : Fin 1781 → List Bool) :
    install (blockSl j hj) A o (blockSl j hj k) = o k := install_slot _ (blockSl_inj j hj) _ _ _

/-- A block's entry, from an ambient that holds its circuit's word, the shared inputs, and a blank region. -/
theorem entry_block (j : ℕ) (hj : j < 4) (code n L : ℕ) (A : Fin 7123 → List Bool)
    (h0 : A ⟨j, by omega⟩ = frame (natWord code)) (h4 : A 4 = List.replicate n true) (h5 : A 5 = List.replicate L true)
    (h9 : A 9 = [false]) (hr : ∀ i : Fin 7123, RB j ≤ i.val → i.val < RB j + 1777 → A i = []) :
    ∀ k, A (blockSl j hj k) = blockIn code n L k := by
  intro k
  unfold blockIn
  by_cases k0 : k.val = 0
  · rw [if_pos k0, show blockSl j hj k = ⟨j, by omega⟩ from Fin.ext (by simp [blockSl, blockV, k0]), h0]
  rw [if_neg k0]
  by_cases k1 : k.val = 1
  · rw [if_pos k1, show blockSl j hj k = 4 from Fin.ext (by simp [blockSl, blockV, k1]), h4]
  rw [if_neg k1]
  by_cases k2 : k.val = 2
  · rw [if_pos k2, show blockSl j hj k = 5 from Fin.ext (by simp [blockSl, blockV, k2]), h5]
  rw [if_neg k2]
  by_cases k3 : k.val = 3
  · rw [if_pos k3, show blockSl j hj k = 9 from Fin.ext (by simp [blockSl, blockV, k3]), h9]
  rw [if_neg k3]
  have := k.isLt
  exact hr _ (by simp [blockSl, blockV, k0, k1, k2, k3]) (by simp [blockSl, blockV, k0, k1, k2, k3]; omega)

/-! ## The call's facts -/

/-- The tuple's gate list is the concatenation of the circuits' retained bottoms. -/
theorem thrOccs_gates (P : Shared.StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) :
    (Primitive.thrOccs P Cs).map (·.gate) =
      (List.ofFn fun j => (SupplierEstimator.thresholdCircuitOccurrences (Cs j)).map (·.gate)).flatten := by
  simp [Primitive.thrOccs, SupplierEstimator.thresholdFourfoldOccurrences, List.map_flatMap, List.flatMap,
    List.ofFn_eq_map, List.map_map]
  rfl

theorem thr_gate_desc_le {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) (i : Fin C.bottomCount) :
    (C.bottom i).descriptionBits + 1 ≤ C.descriptionBits := by
  unfold NormalizedThresholdThresholdCircuit.descriptionBits
  have := Finset.single_le_sum (f := fun j => (C.bottom j).descriptionBits) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  have ht : 1 ≤ C.top.descriptionBits := by
    unfold SupportedNormalizedGate.descriptionBits NormalizedThresholdGate.encodingBits intBitLength; omega
  omega

/-- **Every gate of the tuple is within the table's bounds** at register capacity `n + L`. -/
theorem thrGateOk {n : ℕ} {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (L : ℕ)
    (hL : ∀ j, (Cs j).descriptionBits ≤ L) (h2 : 2 ≤ n + L) (G : List (NormalizedThresholdGate n))
    (hG : G = (List.ofFn fun j => (SupplierEstimator.thresholdCircuitOccurrences (Cs j)).map (·.gate)).flatten) :
    ∀ g ∈ G, GateOk (n + L) (tabH G) g := by
  intro g hg
  obtain ⟨hw, hθ, hn⟩ := tab_nbl_le G g hg
  have hg' := hg
  rw [hG] at hg'
  obtain ⟨l, hl, hgl⟩ := List.mem_flatten.mp hg'
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hgl
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ho
  have hd := thr_gate_desc_le (Cs j) (retainedTopIndex (Cs j) i)
  have he : ((Cs j).bottom (retainedTopIndex (Cs j) i)).descriptionBits =
      ((Cs j).bottom (retainedTopIndex (Cs j) i)).gate.encodingBits + n := rfl
  have ht := thr_nbl_le ((Cs j).bottom (retainedTopIndex (Cs j) i)).gate
  have hnb := PolynomialClock.natBitLength_le_succ n
  have hLj := hL j
  refine ⟨fun k => ⟨by have := hw k; omega, by
    have := weight_nbl_le ((Cs j).bottom (retainedTopIndex (Cs j) i)).gate k; omega⟩, hθ, by omega,
    by omega, by omega, by omega, h2⟩

theorem thrScan_le {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) (L : ℕ) (hL : C.descriptionBits ≤ L) :
    natBitLength C.top.wireCount ≤ n + L := by
  have h1 := PolynomialClock.natBitLength_le_succ C.top.wireCount
  have h2 : C.top.wireCount ≤ C.bottomCount := by
    unfold SupportedNormalizedGate.wireCount; simpa using Finset.card_le_univ C.top.support
  have h3 : C.bottomCount + 1 ≤ C.top.descriptionBits := by
    unfold SupportedNormalizedGate.descriptionBits NormalizedThresholdGate.encodingBits intBitLength; omega
  unfold NormalizedThresholdThresholdCircuit.descriptionBits at hL
  omega

end NearCubicWires.WireExponent3_5.PrimT.ThrTab
