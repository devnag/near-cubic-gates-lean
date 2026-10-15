import Proof.Wire_3_5.PrimTTabThrScan

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.SymTab
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.FinalPass.Corner

/-! ## The ambient between the blocks -/

section Pre
variable {n : ℕ} (a : ℕ) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (L : ℕ)

def codesOf : List ℕ := List.ofFn fun j => encodeNormalizedThresholdThresholdCircuit (Cs j)

/-- After the cell and the blocks before `j`: the codes and the shared inputs kept, the cell `[false]`, the regions
from `j` on blank, the shared outputs blank, the finished words in place, and region `0`'s registers. -/
structure Pre (j : ℕ) (A : Fin 7123 → List Bool) : Prop where
  code : ∀ i : Fin 7123, i.val < 4 → A i = thrIn (codesOf a Cs) n L i
  hn : A 4 = List.replicate n true
  hL : A 5 = List.replicate L true
  cell : A 9 = [false]
  blank : ∀ i : Fin 7123, RB j ≤ i.val → A i = []
  shared : ∀ i : Fin 7123, 6 ≤ i.val → i.val < RB 0 → i.val ≠ 9 → A i = []
  word : ∀ i, i < j → ∀ (ha : i < a) (h4 : i < 4), A ⟨RB i + 1688, by unfold RB; omega⟩ =
    PacketProduction.thrWord (Cs ⟨i, ha⟩)
  regs : 0 < j → A 1724 = List.replicate (n + L + 1) false ∧ A 1725 = List.replicate (n + L + 1) false ∧
    A 1726 = List.replicate (n + L + 1) false

theorem pre_zero : Pre a Cs L 0 (install cellSlT (thrIn (codesOf a Cs) n L) (fun _ => [false])) := by
  have miss : ∀ i : Fin 7123, i.val ≠ 9 → install cellSlT (thrIn (codesOf a Cs) n L) (fun _ => [false]) i =
      thrIn (codesOf a Cs) n L i := fun i h => install_other _ _ _ _ (fun j e => h (by rw [← e]; rfl))
  refine ⟨fun i hi => miss i (by omega), ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun h => absurd h (lt_irrefl 0)⟩
  · rw [miss 4 (by decide)]; unfold thrIn; rw [dif_neg (by simp)]; rfl
  · rw [miss 5 (by decide)]; unfold thrIn; rw [dif_neg (by simp)]; rfl
  · rw [show (9 : Fin 7123) = cellSlT 0 from rfl, install_slot _ cellSlT_inj]
  · intro i hi; unfold RB at hi; rw [miss i (by omega)]; exact thrIn_blank _ _ _ i (by omega)
  · intro i h6 h0 h9; rw [miss i h9]; exact thrIn_blank _ _ _ i h6

theorem RB_le (i j : ℕ) (h : i + 1 ≤ j) : RB i + 1777 ≤ RB j := by
  unfold RB; have := Nat.mul_le_mul_right 1777 h; rw [Nat.add_mul] at this; omega

theorem thrIn_code (j : ℕ) (hja : j < a) (hj4 : j < 4) (i : Fin 7123) (hi : i.val = j) :
    thrIn (codesOf a Cs) n L i = frame (natWord (encodeNormalizedThresholdThresholdCircuit (Cs ⟨j, hja⟩))) := by
  unfold thrIn
  rw [dif_pos ⟨by simp [codesOf]; omega, by omega⟩]
  simp [codesOf, hi]

/-- **One decode block keeps the invariant.** -/
theorem pre_step (j : ℕ) (hj : j < 4) (hja : j < a) (A : Fin 7123 → List Bool) (hA : Pre a Cs L j A)
    (out : Fin 1781 → List Bool) (h0 : out 0 = frame (natWord (encodeNormalizedThresholdThresholdCircuit (Cs ⟨j, hja⟩))))
    (h1 : out 1 = List.replicate n true) (h2 : out 2 = List.replicate L true) (h3 : out 3 = [false])
    (hw : out 1692 = PacketProduction.thrWord (Cs ⟨j, hja⟩))
    (r1 : out 1713 = List.replicate (n + L + 1) false) (r2 : out 1714 = List.replicate (n + L + 1) false)
    (r3 : out 1715 = List.replicate (n + L + 1) false) :
    Pre a Cs L (j + 1) (install (blockSl j hj) A out) := by
  have rb : RB (j + 1) = RB j + 1777 := by unfold RB; ring
  have rbj : 15 ≤ RB j := by unfold RB; omega
  have rb0 : RB 0 = 15 := rfl
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, fun i hi => ?_, fun i h6 h0 h9 => ?_, fun i hi hia hi4 => ?_, fun _ => ?_⟩
  · by_cases hij : i.val = j
    · rw [show i = blockSl j hj 0 from Fin.ext (by simp [blockSl, blockV, hij]), hit_block, h0]
      exact (thrIn_code a Cs L j hja hj _ (by simp [blockSl, blockV])).symm
    · rw [miss_block j hj i hij (by omega) (by omega) (by omega) (by omega)]; exact hA.code i hi
  · rw [show (4 : Fin 7123) = blockSl j hj 1 from rfl, hit_block, h1]
  · rw [show (5 : Fin 7123) = blockSl j hj 2 from rfl, hit_block, h2]
  · rw [show (9 : Fin 7123) = blockSl j hj 3 from rfl, hit_block, h3]
  · rw [miss_block j hj i (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hA.blank i (by omega)
  · rw [miss_block j hj i (by omega) (by omega) (by omega) h9 (by omega)]; exact hA.shared i h6 h0 h9
  · by_cases hij : i = j
    · subst hij
      rw [show (⟨RB i + 1688, _⟩ : Fin 7123) = blockSl i hj 1692 from Fin.ext (by simp [blockSl, blockV]), hit_block, hw]
    · have hi' : i < j := by omega
      have hle := RB_le i j (by omega)
      have hri : 15 ≤ RB i := by unfold RB; omega
      rw [miss_block j hj _ (by show RB i + 1688 ≠ j; omega) (by show RB i + 1688 ≠ 4; omega)
        (by show RB i + 1688 ≠ 5; omega) (by show RB i + 1688 ≠ 9; omega) (by show RB i + 1688 < RB j ∨ _; omega)]
      exact hA.word i hi' hia hi4
  · by_cases hj0 : j = 0
    · subst hj0
      refine ⟨?_, ?_, ?_⟩
      · rw [show (1724 : Fin 7123) = blockSl 0 hj 1713 from rfl, hit_block, r1]
      · rw [show (1725 : Fin 7123) = blockSl 0 hj 1714 from rfl, hit_block, r2]
      · rw [show (1726 : Fin 7123) = blockSl 0 hj 1715 from rfl, hit_block, r3]
    · obtain ⟨g1, g2, g3⟩ := hA.regs (by omega)
      have hle := RB_le 0 j (by omega)
      rw [rb0] at hle
      refine ⟨?_, ?_, ?_⟩
      · rw [miss_block j hj _ (by show 1724 ≠ j; omega) (by decide) (by decide) (by decide)
          (by show 1724 < RB j ∨ _; omega), g1]
      · rw [miss_block j hj _ (by show 1725 ≠ j; omega) (by decide) (by decide) (by decide)
          (by show 1725 < RB j ∨ _; omega), g2]
      · rw [miss_block j hj _ (by show 1726 ≠ j; omega) (by decide) (by decide) (by decide)
          (by show 1726 < RB j ∨ _; omega), g3]

end Pre

/-! ## The stages on the call's tapes -/

section Stages
variable {n : ℕ} (a : ℕ) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (L : ℕ)

theorem zeroHT {t : ℕ} (sl : Fin t → Fin 7123) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-- **One decode block on the call's tapes**, keeping the invariant. -/
theorem blockStage (j : ℕ) (hj : j < 4) (hja : j < a) (A : Fin 7123 → List Bool) (hA : Pre a Cs L j A)
    (hL : (Cs ⟨j, hja⟩).descriptionBits ≤ L) :
    ∃ out : Fin 1781 → List Bool, Step (blockD j hj) (thrBlockCost (Cs ⟨j, hja⟩) L) (fun _ => 0) A (fun _ => 0)
      (install (blockSl j hj) A out) ∧ Pre a Cs L (j + 1) (install (blockSl j hj) A out) := by
  obtain ⟨out, st, h0, h1, h2, h3, hw, r1, r2, r3⟩ := thrBlock_step (Cs ⟨j, hja⟩) L hL
  have d := st.dock (blockSl j hj) (blockSl_inj j hj) (fun _ => 0) A (fun _ => rfl)
    (entry_block j hj _ n L A (by rw [hA.code _ (by simp; omega)]; exact thrIn_code a Cs L j hja hj _ rfl)
      hA.hn hA.hL hA.cell (fun i h1 _ => hA.blank i h1))
  rw [zeroHT] at d
  exact ⟨out, d, pre_step a Cs L j hj hja A hA out h0 h1 h2 h3 hw r1 r2 r3⟩

/-- The tuple's native words, slot by slot. -/
def wordsT : ℕ → List Bool := fun j => if h : j < a then PacketProduction.thrWord (Cs ⟨j, h⟩) else []

theorem entry_scanT (ha : a ≤ 4) (ha1 : 1 ≤ a) (A : Fin 7123 → List Bool) (hA : Pre a Cs L a A) :
    ∀ k, A (scanSlT k) = thrScanIn (n + L) a (wordsT a Cs) k := by
  intro k
  have rbw : ∀ i, i < 4 → a ≤ i → ∀ t : Fin 7123, t.val = RB i + 1688 → A t = [] := by
    intro i hi hai t ht
    refine hA.blank t ?_
    have e : RB a ≤ RB i := by
      rcases Nat.eq_or_lt_of_le hai with e | e
      · rw [e]
      · have := RB_le a i (by omega); omega
    omega
  have wd : ∀ i (hi : i < a) (h4 : i < 4), A ⟨RB i + 1688, by unfold RB; omega⟩ = wordsT a Cs i := by
    intro i hi h4; rw [hA.word i hi hi h4]; simp [wordsT, hi]
  fin_cases k
  · show A 1703 = (if 0 < 4 ∧ 0 < a then wordsT a Cs 0 else [])
    rw [if_pos ⟨by decide, by omega⟩, ← wd 0 (by omega) (by decide)]; rfl
  · show A 9 = [false]; exact hA.cell
  · show A 3480 = (if 1 < 4 ∧ 1 < a then wordsT a Cs 1 else [])
    by_cases h : 1 < a
    · rw [if_pos ⟨by decide, h⟩, ← wd 1 h (by decide)]; rfl
    · rw [if_neg (fun e => h e.2)]; exact rbw 1 (by decide) (by omega) _ rfl
  · show A 5257 = (if 2 < 4 ∧ 2 < a then wordsT a Cs 2 else [])
    by_cases h : 2 < a
    · rw [if_pos ⟨by decide, h⟩, ← wd 2 h (by decide)]; rfl
    · rw [if_neg (fun e => h e.2)]; exact rbw 2 (by decide) (by omega) _ rfl
  · show A 7034 = (if 3 < 4 ∧ 3 < a then wordsT a Cs 3 else [])
    by_cases h : 3 < a
    · rw [if_pos ⟨by decide, h⟩, ← wd 3 h (by decide)]; rfl
    · rw [if_neg (fun e => h e.2)]; exact rbw 3 (by decide) (by omega) _ rfl
  · show A 10 = []; exact hA.shared _ (by decide) (by decide) (by decide)
  · show A 11 = []; exact hA.shared _ (by decide) (by decide) (by decide)
  · show A 12 = []; exact hA.shared _ (by decide) (by decide) (by decide)
  · show A 8 = []; exact hA.shared _ (by decide) (by decide) (by decide)
  · show A 7 = []; exact hA.shared _ (by decide) (by decide) (by decide)
  · show A 1724 = List.replicate (n + L + 1) false; exact (hA.regs (by omega)).1
  · show A 13 = []; exact hA.shared _ (by decide) (by decide) (by decide)

theorem entry_tabT (h : ℕ) (seg : List Bool) (A : Fin 7123 → List Bool) (hA : Pre a Cs L a A) (ha1 : 1 ≤ a)
    (os : Fin 12 → List Bool) (s1 : os 1 = [false]) (s5 : os 5 = seg) (s6 : os 6 = seg)
    (s7 : os 7 = false :: List.replicate h true) (s9 : os 9 = []) (s10 : os 10 = List.replicate (n + L + 1) false) :
    ∀ k, install scanSlT A os (tabSlT k) = tabIn (n + L) seg n h k := by
  intro k
  rw [tabIn_val]
  have ms : ∀ i : Fin 7123, (∀ j : Fin 12, (scanSlT j).val ≠ i.val) → install scanSlT A os i = A i :=
    fun i h => install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))
  have hs : ∀ j : Fin 12, install scanSlT A os (scanSlT j) = os j := fun j => install_slot _ scanSlT_inj _ _ _
  fin_cases k
  · rw [show tabSlT ⟨0, by decide⟩ = scanSlT 5 from rfl, hs, s5]; rfl
  · rw [show tabSlT ⟨1, by decide⟩ = scanSlT 1 from rfl, hs, s1]; rfl
  · rw [show tabSlT ⟨2, by decide⟩ = scanSlT 6 from rfl, hs, s6]; rfl
  · rw [ms _ (by decide)]; exact hA.hn
  · rw [show tabSlT ⟨4, by decide⟩ = scanSlT 7 from rfl, hs, s7]; rfl
  · rw [ms _ (by decide)]; exact hA.shared _ (by decide) (by decide) (by decide)
  · rw [show tabSlT ⟨6, by decide⟩ = scanSlT 9 from rfl, hs, s9]; rfl
  · rw [show tabSlT ⟨7, by decide⟩ = scanSlT 10 from rfl, hs, s10]; rfl
  · rw [ms _ (by decide)]; exact (hA.regs (by omega)).2.1
  · rw [ms _ (by decide)]; exact (hA.regs (by omega)).2.2
  · rw [ms _ (by decide)]; exact hA.shared _ (by decide) (by decide) (by decide)

/-- **The last two stages on the call's tapes**: the tuple's scan and the table, from the invariant after the blocks. -/
theorem tailStage (ha : a ≤ 4) (ha1 : 1 ≤ a) (hL : ∀ j, (Cs j).descriptionBits ≤ L) (h2 : 2 ≤ n + L)
    (A : Fin 7123 → List Bool) (hA : Pre a Cs L a A) :
    ∃ T : Fin 7123 → List Bool,
      Step (Composition.machine (scanDT a ha) tabDT)
        (thrScanCost ha Cs + 1 + (2 * tabCost n (tabH (tupleG Cs)) (tupleG Cs).length + 2)) (fun _ => 0) A
        (fun _ => 0) T ∧
      (∀ i : Fin 7123, i.val < 4 → T i = A i) ∧ T 4 = List.replicate n true ∧ T 5 = List.replicate L true ∧
      T 6 = gatesW (tabH (tupleG Cs)) (tupleG Cs) ∧ T 7 = List.replicate (tabH (tupleG Cs)) true ∧
      T 8 = List.replicate (tupleG Cs).length true := by
  obtain ⟨os, ss, s1, s5, s6, s7, s8, s9, s10⟩ := thrScanStage (n + L) a ha ha1 Cs (fun j => thrScan_le (Cs j) L (hL j))
  have dS := ss.dock scanSlT scanSlT_inj (fun _ => 0) A (fun _ => rfl) (entry_scanT a Cs L ha ha1 A hA)
  rw [zeroHT] at dS
  obtain ⟨ot, st, t3, t5, t6⟩ := tabStage (n + L) (tabH (tupleG Cs)) (tupleG Cs)
    (thrGateOk Cs L hL h2 (tupleG Cs) rfl)
  have dT := st.dock tabSlT tabSlT_inj (fun _ => 0) (install scanSlT A os) (fun _ => rfl)
    (entry_tabT a Cs L (tabH (tupleG Cs)) (tabSeg (tupleG Cs)) A hA ha1 os s1 s5 s6 s7 s9 s10)
  rw [zeroHT] at dT
  have ms : ∀ i : Fin 7123, (∀ j : Fin 12, (scanSlT j).val ≠ i.val) → install scanSlT A os i = A i :=
    fun i h => install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))
  have mt : ∀ i : Fin 7123, (∀ j : Fin 11, (tabSlT j).val ≠ i.val) →
      install tabSlT (install scanSlT A os) ot i = install scanSlT A os i :=
    fun i h => install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))
  have ht : ∀ j : Fin 11, install tabSlT (install scanSlT A os) ot (tabSlT j) = ot j :=
    fun j => install_slot _ tabSlT_inj _ _ _
  refine ⟨_, dS.seq dT, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mt i (fun j => by fin_cases j <;> simp [tabSlT] <;> omega), ms i (fun j => by fin_cases j <;> simp [scanSlT] <;> omega)]
  · rw [show (4 : Fin 7123) = tabSlT 3 from rfl, ht, t3]
  · rw [mt _ (by decide), ms _ (by decide)]; exact hA.hL
  · rw [show (6 : Fin 7123) = tabSlT 5 from rfl, ht, t5]
  · rw [show (7 : Fin 7123) = tabSlT 6 from rfl, ht, t6]
  · rw [mt _ (by decide), show (8 : Fin 7123) = scanSlT 8 from rfl, install_slot _ scanSlT_inj, s8]

end Stages

/-! ## The machines and their runs -/

theorem thrIn_nine (codes : List ℕ) (n L : ℕ) : ∀ j : Fin 1, thrIn codes n L (cellSlT j) = (fun _ => ([] : List Bool)) j :=
  fun _ => thrIn_blank codes n L 9 (by decide)

theorem lt4_0 : 0 < 4 := by decide
theorem lt4_1 : 1 < 4 := by decide
theorem lt4_2 : 2 < 4 := by decide
theorem lt4_3 : 3 < 4 := by decide
theorem le4_1 : 1 ≤ 4 := by decide
theorem le4_2 : 2 ≤ 4 := by decide
theorem le4_3 : 3 ≤ 4 := by decide
theorem le4_4 : 4 ≤ 4 := by decide

noncomputable def bk0 := blockD 0 lt4_0
noncomputable def bk1 := blockD 1 lt4_1
noncomputable def bk2 := blockD 2 lt4_2
noncomputable def bk3 := blockD 3 lt4_3
noncomputable def tail1 := Composition.machine (scanDT 1 le4_1) tabDT
noncomputable def tail2 := Composition.machine (scanDT 2 le4_2) tabDT
noncomputable def tail3 := Composition.machine (scanDT 3 le4_3) tabDT
noncomputable def tail4 := Composition.machine (scanDT 4 le4_4) tabDT

noncomputable def ch1_0 := Composition.machine bk0 tail1

/-- **The THR table machine for 1 circuit.** -/
noncomputable def thrTableM1 := Composition.machine cellDT ch1_0

/-- Its fuel. -/
noncomputable def thrTableCost1 {n : ℕ} (Cs : Fin 1 → NormalizedThresholdThresholdCircuit n) (L : ℕ) : ℕ :=
  1 + 1 + (thrBlockCost (Cs 0) L + 1 + (thrScanCost (show 1 ≤ 4 by decide) Cs + 1 + (2 * tabCost n (tabH (tupleG Cs)) (tupleG Cs).length + 2)))

/-- **The THR gate table for 1 circuit.** -/
theorem thrTable1_step {n : ℕ} (Cs : Fin 1 → NormalizedThresholdThresholdCircuit n) (L : ℕ)
    (hL : ∀ j, (Cs j).descriptionBits ≤ L) (h2 : 2 ≤ n + L) :
    ∃ tout : Fin 7123 → List Bool,
      Step thrTableM1 (thrTableCost1 Cs L) (fun _ => 0) (thrIn (codesOf 1 Cs) n L) (fun _ => 0) tout ∧
      (∀ i : Fin 7123, i.val < 4 → tout i = thrIn (codesOf 1 Cs) n L i) ∧ tout 4 = List.replicate n true ∧
      tout 5 = List.replicate L true ∧ tout 6 = gatesW (tabH (tupleG Cs)) (tupleG Cs) ∧
      tout 7 = List.replicate (tabH (tupleG Cs)) true ∧ tout 8 = List.replicate (tupleG Cs).length true := by
  have c1 := cell_step.dock cellSlT cellSlT_inj (fun _ => 0) (thrIn (codesOf 1 Cs) n L) (fun _ => rfl)
    (thrIn_nine (codesOf 1 Cs) n L)
  rw [zeroHT] at c1
  have P0 := pre_zero 1 Cs L (n := n)
  obtain ⟨o0, b0, P1⟩ := blockStage 1 Cs L 0 lt4_0 (by decide) _ P0 (hL _)
  obtain ⟨T, tl, e03, e4, e5, e6, e7, e8⟩ := tailStage 1 Cs L le4_1 (by decide) hL h2 _ P1
  have run := c1.seq (b0.seq tl)
  have run' : Step thrTableM1 _ (fun _ => 0) (thrIn (codesOf 1 Cs) n L) (fun _ => 0) T := run
  refine ⟨T, run'.enlarge (by unfold thrTableCost1; exact le_refl _), fun i hi => by rw [e03 i hi]; exact P1.code i hi,
    e4, e5, e6, e7, e8⟩

noncomputable def ch2_1 := Composition.machine bk1 tail2
noncomputable def ch2_0 := Composition.machine bk0 ch2_1

/-- **The THR table machine for 2 circuits.** -/
noncomputable def thrTableM2 := Composition.machine cellDT ch2_0

/-- Its fuel. -/
noncomputable def thrTableCost2 {n : ℕ} (Cs : Fin 2 → NormalizedThresholdThresholdCircuit n) (L : ℕ) : ℕ :=
  1 + 1 + (thrBlockCost (Cs 0) L + 1 + (thrBlockCost (Cs 1) L + 1 + (thrScanCost (show 2 ≤ 4 by decide) Cs + 1 + (2 * tabCost n (tabH (tupleG Cs)) (tupleG Cs).length + 2))))

/-- **The THR gate table for 2 circuits.** -/
theorem thrTable2_step {n : ℕ} (Cs : Fin 2 → NormalizedThresholdThresholdCircuit n) (L : ℕ)
    (hL : ∀ j, (Cs j).descriptionBits ≤ L) (h2 : 2 ≤ n + L) :
    ∃ tout : Fin 7123 → List Bool,
      Step thrTableM2 (thrTableCost2 Cs L) (fun _ => 0) (thrIn (codesOf 2 Cs) n L) (fun _ => 0) tout ∧
      (∀ i : Fin 7123, i.val < 4 → tout i = thrIn (codesOf 2 Cs) n L i) ∧ tout 4 = List.replicate n true ∧
      tout 5 = List.replicate L true ∧ tout 6 = gatesW (tabH (tupleG Cs)) (tupleG Cs) ∧
      tout 7 = List.replicate (tabH (tupleG Cs)) true ∧ tout 8 = List.replicate (tupleG Cs).length true := by
  have c1 := cell_step.dock cellSlT cellSlT_inj (fun _ => 0) (thrIn (codesOf 2 Cs) n L) (fun _ => rfl)
    (thrIn_nine (codesOf 2 Cs) n L)
  rw [zeroHT] at c1
  have P0 := pre_zero 2 Cs L (n := n)
  obtain ⟨o0, b0, P1⟩ := blockStage 2 Cs L 0 lt4_0 (by decide) _ P0 (hL _)
  obtain ⟨o1, b1, P2⟩ := blockStage 2 Cs L 1 lt4_1 (by decide) _ P1 (hL _)
  obtain ⟨T, tl, e03, e4, e5, e6, e7, e8⟩ := tailStage 2 Cs L le4_2 (by decide) hL h2 _ P2
  have run := c1.seq (b0.seq (b1.seq tl))
  have run' : Step thrTableM2 _ (fun _ => 0) (thrIn (codesOf 2 Cs) n L) (fun _ => 0) T := run
  refine ⟨T, run'.enlarge (by unfold thrTableCost2; exact le_refl _), fun i hi => by rw [e03 i hi]; exact P2.code i hi,
    e4, e5, e6, e7, e8⟩

noncomputable def ch3_2 := Composition.machine bk2 tail3
noncomputable def ch3_1 := Composition.machine bk1 ch3_2
noncomputable def ch3_0 := Composition.machine bk0 ch3_1

/-- **The THR table machine for 3 circuits.** -/
noncomputable def thrTableM3 := Composition.machine cellDT ch3_0

/-- Its fuel. -/
noncomputable def thrTableCost3 {n : ℕ} (Cs : Fin 3 → NormalizedThresholdThresholdCircuit n) (L : ℕ) : ℕ :=
  1 + 1 + (thrBlockCost (Cs 0) L + 1 + (thrBlockCost (Cs 1) L + 1 + (thrBlockCost (Cs 2) L + 1 + (thrScanCost (show 3 ≤ 4 by decide) Cs + 1 + (2 * tabCost n (tabH (tupleG Cs)) (tupleG Cs).length + 2)))))

/-- **The THR gate table for 3 circuits.** -/
theorem thrTable3_step {n : ℕ} (Cs : Fin 3 → NormalizedThresholdThresholdCircuit n) (L : ℕ)
    (hL : ∀ j, (Cs j).descriptionBits ≤ L) (h2 : 2 ≤ n + L) :
    ∃ tout : Fin 7123 → List Bool,
      Step thrTableM3 (thrTableCost3 Cs L) (fun _ => 0) (thrIn (codesOf 3 Cs) n L) (fun _ => 0) tout ∧
      (∀ i : Fin 7123, i.val < 4 → tout i = thrIn (codesOf 3 Cs) n L i) ∧ tout 4 = List.replicate n true ∧
      tout 5 = List.replicate L true ∧ tout 6 = gatesW (tabH (tupleG Cs)) (tupleG Cs) ∧
      tout 7 = List.replicate (tabH (tupleG Cs)) true ∧ tout 8 = List.replicate (tupleG Cs).length true := by
  have c1 := cell_step.dock cellSlT cellSlT_inj (fun _ => 0) (thrIn (codesOf 3 Cs) n L) (fun _ => rfl)
    (thrIn_nine (codesOf 3 Cs) n L)
  rw [zeroHT] at c1
  have P0 := pre_zero 3 Cs L (n := n)
  obtain ⟨o0, b0, P1⟩ := blockStage 3 Cs L 0 lt4_0 (by decide) _ P0 (hL _)
  obtain ⟨o1, b1, P2⟩ := blockStage 3 Cs L 1 lt4_1 (by decide) _ P1 (hL _)
  obtain ⟨o2, b2, P3⟩ := blockStage 3 Cs L 2 lt4_2 (by decide) _ P2 (hL _)
  obtain ⟨T, tl, e03, e4, e5, e6, e7, e8⟩ := tailStage 3 Cs L le4_3 (by decide) hL h2 _ P3
  have run := c1.seq (b0.seq (b1.seq (b2.seq tl)))
  have run' : Step thrTableM3 _ (fun _ => 0) (thrIn (codesOf 3 Cs) n L) (fun _ => 0) T := run
  refine ⟨T, run'.enlarge (by unfold thrTableCost3; exact le_refl _), fun i hi => by rw [e03 i hi]; exact P3.code i hi,
    e4, e5, e6, e7, e8⟩

noncomputable def ch4_3 := Composition.machine bk3 tail4
noncomputable def ch4_2 := Composition.machine bk2 ch4_3
noncomputable def ch4_1 := Composition.machine bk1 ch4_2
noncomputable def ch4_0 := Composition.machine bk0 ch4_1

/-- **The THR table machine for 4 circuits.** -/
noncomputable def thrTableM4 := Composition.machine cellDT ch4_0

/-- Its fuel. -/
noncomputable def thrTableCost4 {n : ℕ} (Cs : Fin 4 → NormalizedThresholdThresholdCircuit n) (L : ℕ) : ℕ :=
  1 + 1 + (thrBlockCost (Cs 0) L + 1 + (thrBlockCost (Cs 1) L + 1 + (thrBlockCost (Cs 2) L + 1 + (thrBlockCost (Cs 3) L + 1 + (thrScanCost (show 4 ≤ 4 by decide) Cs + 1 + (2 * tabCost n (tabH (tupleG Cs)) (tupleG Cs).length + 2))))))

/-- **The THR gate table for 4 circuits.** -/
theorem thrTable4_step {n : ℕ} (Cs : Fin 4 → NormalizedThresholdThresholdCircuit n) (L : ℕ)
    (hL : ∀ j, (Cs j).descriptionBits ≤ L) (h2 : 2 ≤ n + L) :
    ∃ tout : Fin 7123 → List Bool,
      Step thrTableM4 (thrTableCost4 Cs L) (fun _ => 0) (thrIn (codesOf 4 Cs) n L) (fun _ => 0) tout ∧
      (∀ i : Fin 7123, i.val < 4 → tout i = thrIn (codesOf 4 Cs) n L i) ∧ tout 4 = List.replicate n true ∧
      tout 5 = List.replicate L true ∧ tout 6 = gatesW (tabH (tupleG Cs)) (tupleG Cs) ∧
      tout 7 = List.replicate (tabH (tupleG Cs)) true ∧ tout 8 = List.replicate (tupleG Cs).length true := by
  have c1 := cell_step.dock cellSlT cellSlT_inj (fun _ => 0) (thrIn (codesOf 4 Cs) n L) (fun _ => rfl)
    (thrIn_nine (codesOf 4 Cs) n L)
  rw [zeroHT] at c1
  have P0 := pre_zero 4 Cs L (n := n)
  obtain ⟨o0, b0, P1⟩ := blockStage 4 Cs L 0 lt4_0 (by decide) _ P0 (hL _)
  obtain ⟨o1, b1, P2⟩ := blockStage 4 Cs L 1 lt4_1 (by decide) _ P1 (hL _)
  obtain ⟨o2, b2, P3⟩ := blockStage 4 Cs L 2 lt4_2 (by decide) _ P2 (hL _)
  obtain ⟨o3, b3, P4⟩ := blockStage 4 Cs L 3 lt4_3 (by decide) _ P3 (hL _)
  obtain ⟨T, tl, e03, e4, e5, e6, e7, e8⟩ := tailStage 4 Cs L le4_4 (by decide) hL h2 _ P4
  have run := c1.seq (b0.seq (b1.seq (b2.seq (b3.seq tl))))
  have run' : Step thrTableM4 _ (fun _ => 0) (thrIn (codesOf 4 Cs) n L) (fun _ => 0) T := run
  refine ⟨T, run'.enlarge (by unfold thrTableCost4; exact le_refl _), fun i hi => by rw [e03 i hi]; exact P4.code i hi,
    e4, e5, e6, e7, e8⟩

end NearCubicWires.WireExponent3_5.PrimT.ThrTab
