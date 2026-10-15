import Proof.Wire_3_5.PrimTTabThrLayout

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.SymTab
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.SupplierPipeline

/-- The roles of word `j`'s scan: the word, the copies, the ruler, the gate count, the width. -/
def scE (j : Fin 4) : Fin 6 ↪ Fin 9 :=
  ⟨![Fin.castLE (by decide) j, 4, 5, 6, 7, 8], by fin_cases j <;> decide⟩

theorem scE_zero (j : Fin 4) : (scE j 0).val = j.val := rfl

theorem scE_other (j j' : Fin 4) (i : Fin 6) (hi : i ≠ 0) : scE j i = scE j' i := by
  fin_cases i <;> first | exact absurd rfl hi | rfl

theorem scE_ne (j : Fin 4) (i : Fin 6) (hi : i ≠ 0) : scE j 0 ≠ scE 0 i := by
  intro e
  have hv := congrArg Fin.val e
  rw [scE_zero] at hv
  fin_cases i <;> simp at hi <;> (have := j.isLt; simp [scE] at hv; omega)

/-- **The tuple's scan**: the ruler's sentinel, then the first `a` words. -/
def thrScanW (a : ℕ) (ha : a ≤ 4) : WM 8 1 :=
  .seq (emitW 6 false) (scanSeqW 0 (List.ofFn fun j : Fin a => scE ⟨j.val, by omega⟩))

/-- The scan's entry: the first `a` native words, blank otherwise. -/
def σST (a : ℕ) (words : ℕ → List Bool) : WState 8 1 :=
  ⟨fun _ => 0, fun i => if i.val < 4 ∧ i.val < a then words i.val else [], fun _ => 0, false⟩

def thrScanIn (cap a : ℕ) (words : ℕ → List Bool) : Fin 12 → List Bool :=
  Fin.addCases (m := 8 + 2 + 1) (n := 1) (motive := fun _ => List Bool) (wenc cap (σST a words)).A (fun _ => [])

def scanSlT : Fin 12 → Fin 7123 := ![1703, 9, 3480, 5257, 7034, 10, 11, 12, 8, 7, 1724, 13]
theorem scanSlT_inj : Function.Injective scanSlT := by decide
noncomputable def scanDT (a : ℕ) (ha : a ≤ 4) := RecoveryFocus.machine scanSlT (Rewind.machine (thrScanW a ha).toProg.compile)

theorem thrScanIn_val (cap a : ℕ) (words : ℕ → List Bool) (k : Fin 12) :
    thrScanIn cap a words k = if k.val = 0 then (if 0 < 4 ∧ 0 < a then words 0 else [])
      else if k.val = 1 then [false]
      else if k.val = 2 then (if 1 < 4 ∧ 1 < a then words 1 else [])
      else if k.val = 3 then (if 2 < 4 ∧ 2 < a then words 2 else [])
      else if k.val = 4 then (if 3 < 4 ∧ 3 < a then words 3 else [])
      else if k.val = 10 then List.replicate (cap + 1) false else [] := by
  fin_cases k <;> rfl

def scanItem {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) (j : Fin 4) : ScanItem 8 n :=
  ⟨scE j, C.top.wireCount, thresholdWord (CompilerSemantics.nonStrictAsStrict (retainedTopGate C)),
    (SupplierEstimator.thresholdCircuitOccurrences C).map (·.gate)⟩

/-- The tuple's gate list, circuit by circuit. -/
def tupleG {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) : List (NormalizedThresholdGate n) :=
  (List.ofFn fun j => (SupplierEstimator.thresholdCircuitOccurrences (Cs j)).map (·.gate)).flatten

/-- The scan stage's fuel. -/
def thrScanCost {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) : ℕ :=
  2 * (3 + 1 + scanCosts (List.ofFn fun j : Fin a => scanItem (Cs j) ⟨j.val, by omega⟩)) + 2

/-- **The tuple's scan stage**: the copies gain the tuple's framed region, the ruler its width, the gate count its
length; the words are kept and the count register returns to `0`. -/
theorem thrScanStage {n : ℕ} (cap a : ℕ) (ha : a ≤ 4) (ha1 : 1 ≤ a) (Cs : Fin a → NormalizedThresholdThresholdCircuit n)
    (hk : ∀ j, natBitLength (Cs j).top.wireCount ≤ cap) :
    ∃ o : Fin 12 → List Bool,
    Step (Rewind.machine (thrScanW a ha).toProg.compile) (thrScanCost ha Cs) (fun _ => 0)
      (thrScanIn cap a (fun j => if h : j < a then PacketProduction.thrWord (Cs ⟨j, h⟩) else []))
      (fun _ => 0) o ∧
    o 1 = [false] ∧ o 5 = tabSeg (tupleG Cs) ∧ o 6 = tabSeg (tupleG Cs) ∧
    o 7 = false :: List.replicate (tabH (tupleG Cs)) true ∧ o 8 = List.replicate (tupleG Cs).length true ∧
    o 9 = [] ∧ o 10 = List.replicate (cap + 1) false := by
  set words : ℕ → List Bool := fun j => if h : j < a then PacketProduction.thrWord (Cs ⟨j, h⟩) else []
    with hwords
  set σ := σST a words with hσ
  obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap (6 : Fin 9) false σ (by simp [hσ, σST])
  have d06 : ∀ i : Fin 9, i ≠ 6 → Same σ σ1 i := fun i h => o1 i h
  have hs1 : ScanSt (scE 0) σ1 [] 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ1.st 4 = []; rw [(o1 4 (by decide)).1]; rfl
    · show σ1.sh 4 = 0; rw [(o1 4 (by decide)).2]; rfl
    · show σ1.st 5 = []; rw [(o1 5 (by decide)).1]; rfl
    · show σ1.sh 5 = 0; rw [(o1 5 (by decide)).2]; rfl
    · show σ1.st 6 = [false]; rw [e1]; rfl
    · show σ1.sh 6 = 0 + 1; rw [e1h, e1]; rfl
    · show σ1.st 7 = []; rw [(o1 7 (by decide)).1]; rfl
    · show σ1.sh 7 = 0; rw [(o1 7 (by decide)).2]; rfl
  set its := List.ofFn fun j : Fin a => scanItem (Cs j) ⟨j.val, by omega⟩ with hits
  have hmap : its.map (·.S) = List.ofFn fun j : Fin a => scE ⟨j.val, by omega⟩ := by
    simp [hits, List.map_ofFn, Function.comp_def, scanItem]
  have hG : (its.map (·.G)).flatten = tupleG Cs := by
    simp [hits, List.map_ofFn, Function.comp_def, scanItem, tupleG]
  obtain ⟨τ, s2, hs2, c2, cl2, w2, o2, v2⟩ := scanSeq_spec cap (0 : Fin 1) (scE 0) its [] 0 0 σ1 hs1 (by rw [v1]; rfl)
    (fun it hit i hi => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hit
      exact scE_other _ _ i hi)
    (fun it hit => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hit
      have hj6 : (scE ⟨j.val, by omega⟩ 0) ≠ (6 : Fin 9) := by
        intro e; have hv := congrArg Fin.val e; rw [scE_zero] at hv; simp at hv; omega
      refine ⟨?_, ?_, hk j⟩
      · change σ1.st (scE ⟨j.val, by omega⟩ 0) = _
        rw [(o1 _ hj6).1]
        show (σST a words).st (scE ⟨j.val, by omega⟩ 0) = _
        simp only [σST, scE_zero]
        rw [if_pos ⟨by omega, j.isLt⟩, hwords]
        simp only [dif_pos j.isLt]
        exact thrWord_eq (Cs j)
      · change σ1.sh (scE ⟨j.val, by omega⟩ 0) = _; rw [(o1 _ hj6).2]; rfl)
    (by
      have e : (its.map fun it => it.S 0) = List.ofFn fun j : Fin a => scE ⟨j.val, by omega⟩ 0 := by
        simp [hits, List.map_ofFn, Function.comp_def, scanItem]
      rw [e]
      apply List.nodup_ofFn.mpr
      intro x y h
      have hv := congrArg Fin.val h
      rw [scE_zero, scE_zero] at hv
      exact Fin.ext hv)
    (fun it hit i hi => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hit
      intro e
      have := scE_ne ⟨j.val, by omega⟩ i hi
      exact this e)
  rw [hmap] at s2
  obtain ⟨o, st, ho⟩ := wm_step cap (thrScanW a ha) σ τ _ (WExec.seq s1 s2)
    (wenc_H_zero cap _ (fun _ => rfl) (fun _ => rfl))
  obtain ⟨hA, -, hB, -, hH, -, hGc, -⟩ := hs2
  rw [hG] at hA hB hH hGc
  refine ⟨o, st, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (1 : Fin 12) = Fin.castAdd 1 (1 : Fin 11) from rfl, ho]; show [τ.cell] = [false]; rw [cl2, c1]; rfl
  · rw [show (5 : Fin 12) = Fin.castAdd 1 (5 : Fin 11) from rfl, ho]; show τ.st 4 = _; exact hA
  · rw [show (6 : Fin 12) = Fin.castAdd 1 (6 : Fin 11) from rfl, ho]; show τ.st 5 = _; exact hB
  · rw [show (7 : Fin 12) = Fin.castAdd 1 (7 : Fin 11) from rfl, ho]; show τ.st 6 = _; rw [Nat.zero_add] at hH; exact hH
  · rw [show (8 : Fin 12) = Fin.castAdd 1 (8 : Fin 11) from rfl, ho]; show τ.st 7 = _; rw [Nat.zero_add] at hGc; exact hGc
  · rw [show (9 : Fin 12) = Fin.castAdd 1 (9 : Fin 11) from rfl, ho]; show τ.st 8 = _
    have h8 := o2 8 (fun it hit => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hit
      intro e; have hv := congrArg Fin.val e; simp only [scanItem] at hv; rw [scE_zero] at hv; simp at hv; omega)
      (by decide) (by decide) (by decide) (by decide)
    rw [h8.1, (o1 8 (by decide)).1]; rfl
  · rw [show (10 : Fin 12) = Fin.castAdd 1 (10 : Fin 11) from rfl, ho]
    show regTape cap (τ.val 0) = _; rw [c2]; simp [regTape, List.replicate_succ]

end NearCubicWires.WireExponent3_5.PrimT.ThrTab
