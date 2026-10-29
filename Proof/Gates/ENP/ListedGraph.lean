import Proof.Gates.ENP.ListedSupply
import Proof.CaseAnalysis.RecoveryGraphOriginal
import Proof.CaseAnalysis.RecoverySourceGraphMeaning
import Proof.Amplification.RecoveryFocusDock

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.ENP.UGraph

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.BoundedOracleStructuralCircuit NearCubicWires.BalancedCNFSATEncoding
open NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open NearCubicGates.Close.ENP.USupply (uTapes)

/-- The number of tapes. -/
def gTapes (d : ℕ) : ℕ := 1664 + uTapes d

def graphSlot (d : ℕ) (i : Fin 1664) : Fin (gTapes d) := i.castAdd (uTapes d)

def supplierSlot (d : ℕ) (i : Fin (uTapes d)) : Fin (gTapes d) :=
  if h : i.val < 158 then graphSlot d (RecoveryBoundedColdGraph.slots ⟨i.val, h⟩) else i.natAdd 1664

theorem graphSlot_injective (d : ℕ) : Function.Injective (graphSlot d) := Fin.castAdd_injective _ _

theorem graph_fresh (d : ℕ) (i : Fin 1664) (j : Fin (uTapes d)) : graphSlot d i ≠ j.natAdd 1664 := by
  intro he
  have hi := i.isLt
  have hv := congrArg Fin.val he
  change i.val = 1664 + j.val at hv
  omega

theorem supplierSlot_injective (d : ℕ) : Function.Injective (supplierSlot d) := by
  intro i j he
  dsimp only [supplierSlot] at he
  split_ifs at he with hi hj
  · exact Fin.ext (congrArg (fun z : Fin 158 => z.val)
      (RecoveryBoundedColdGraph.injective (graphSlot_injective d he)))
  · exact False.elim (graph_fresh d _ _ he)
  · exact False.elim (graph_fresh d _ _ he.symm)
  · exact Fin.ext (by have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv; omega)

theorem supplier_old (d : ℕ) (i : Fin 158) :
    supplierSlot d (USupply.old d i) = graphSlot d (RecoveryBoundedColdGraph.slots i) := by
  simp only [supplierSlot, USupply.old, show i.val < 158 from i.isLt, dif_pos]

theorem supplier_fresh (d : ℕ) (i : Fin (uTapes d)) (hi : 158 ≤ i.val) : supplierSlot d i = i.natAdd 1664 := by
  simp only [supplierSlot, dif_neg (by omega : ¬ i.val < 158)]

/-- The entry: the listed table, `R` and `W` on the supplier's three input tapes. -/
def input (d : ℕ) (table : List Bool) (R W : ℕ) (i : Fin (gTapes d)) : List Bool :=
  if i.val = 1664 + 158 then table else if i.val = 1664 + 159 then List.replicate R true
  else if i.val = 1664 + 179 then List.replicate W true else []

theorem input_supplier (d : ℕ) (table : List Bool) (R W : ℕ) (i : Fin (uTapes d)) :
    input d table R W (supplierSlot d i) = USupply.input d table R W i := by
  by_cases hi : i.val < 158
  · have hs : supplierSlot d i = graphSlot d (RecoveryBoundedColdGraph.slots ⟨i.val, hi⟩) := by
      simp only [supplierSlot, dif_pos hi]
    have hv := (RecoveryBoundedColdGraph.slots ⟨i.val, hi⟩).isLt
    rw [hs]
    simp only [input, USupply.input, graphSlot, Fin.val_castAdd]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  · rw [supplier_fresh d i (by omega)]
    simp only [input, USupply.input, Fin.val_natAdd]
    by_cases h1 : i.val = 158
    · rw [if_pos (by omega), if_pos h1]
    rw [if_neg (by omega), if_neg h1]
    by_cases h2 : i.val = 159
    · rw [if_pos (by omega), if_pos h2]
    rw [if_neg (by omega), if_neg h2]
    by_cases h3 : i.val = 179
    · rw [if_pos (by omega), if_pos h3]
    rw [if_neg (by omega), if_neg h3]

theorem input_graph (d : ℕ) (table : List Bool) (R W : ℕ) (i : Fin 1664) :
    input d table R W (graphSlot d i) = [] := by
  have hi := i.isLt
  simp only [input, graphSlot, Fin.val_castAdd]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

noncomputable def machine (d : ℕ) :=
  Composition.machine (RecoveryFocus.machine (supplierSlot d) (USupply.machine d))
    (RecoveryFocus.machine (graphSlot d) RecoveryBoundedColdGraph.machine)

/-- The listed-pairs formula's verifier circuit (`sec:all-lengths` stages 1 and 3). -/
noncomputable def circuit (d w R : ℕ) (vals : List Bool) (hw : w ≤ R) {n : ℕ} (x : BitInput n) :=
  boundedOracleVerifierCircuit (unitOuter w R vals hw) x (oracleSizeBound d R)

/-- The builder's budget. -/
noncomputable def budget (d w R W : ℕ) (vals : List Bool) (hw : w ≤ R) {n : ℕ} (x : BitInput n) : ℕ :=
  USupply.budget d R vals.length W + 1 +
    RecoveryBoundedColdGraph.budget (RecoveryBoundedGraphBudget.scalarBacking W) W R (oracleSizeBound d R)
      (circuit d w R vals hw x)

set_option maxHeartbeats 3000000 in
/-- **The listed-pairs formula** (`sec:all-lengths`, stages 1 and 3): the builder halts with the balanced CNF payload of the
recovery formula of `unitOuter w R vals hw` and the unary arity of its description variables. -/
theorem first_run (d : ℕ) (vals post : List Bool) (w R W : ℕ) (hlen : vals.length = 2 ^ w) (hw : w ≤ R)
    {n : ℕ} (x : BitInput n) (hb : 0 < oracleSizeBound d R)
    (hW : originalWorkspace R (oracleSizeBound d R) vals.length vals.length ≤ W)
    (hsource : (DedupBytes.fields (unitPCP w vals)).length ≤ W) (htwo : 2 ^ R ≤ W) :
    ∃ r, run (machine d) (budget d w R W vals hw x) (input d (RepairOrdinary.frame vals ++ post) R W) = some r ∧
      r.steps ≤ budget d w R W vals hw x ∧
      r.final.tapes (graphSlot d 1657) = RepairOrdinary.frame (balancedCNFPayload (CircuitInputCNF.circuitInputFormula
        (circuit d w R vals hw x))).bits ∧
      r.final.heads (graphSlot d 1657) = 0 ∧
      r.final.tapes (graphSlot d 144) = ZeroPadding.pad (RecoveryBoundedGraphBudget.scalarBacking W)
        (List.replicate (descriptionWidth R (oracleSizeBound d R)) true) ∧
      r.final.heads (graphSlot d 144) = 0 := by
  obtain ⟨out, hrun, hold, -⟩ := USupply.supply_ready d vals post w R W hlen hw
  have hfoc := hrun.focus (supplierSlot d) (supplierSlot_injective d) (input d (RepairOrdinary.frame vals ++ post) R W)
    (input_supplier d (RepairOrdinary.frame vals ++ post) R W)
  obtain ⟨r0, h0, ht0, hh0, hs0⟩ := hfoc
  have hcl := USupply.unit_clauses_length w vals
  have hg := RecoveryBoundedColdGraph.original_run (unitPCP w vals) R vals.length hw (le_refl _) x W hb
    (by rw [hcl]; exact hW) hsource htwo
  obtain ⟨rg, hgrun, hgs, hgt, hgh, hga, hgah, _⟩ := hg
  have hprep : ∀ i : Fin 158, out (USupply.old d i) =
      RecoveryBoundedColdPrepared.input R (oracleSizeBound d R) (RecoveryBoundedSelectorLoop.capacity W)
        vals.length (Codec.clauses (unitPCP w vals)).length (RecoveryBoundedGraphBudget.scalarBacking W)
        (RecoveryBoundedRowProjection.bank (unitPCP w vals) R vals.length (bitInputOfCode R 0)
          (RecoveryBoundedGraphBudget.scalarBacking W)) (DedupBytes.fields (unitPCP w vals)) i := by
    intro i
    rw [hold i, hcl, ← RecoveryBoundedColdSourceGraph.backing_eq, ← RecoveryBoundedColdSourceGraph.capacity_eq]
    unfold USupply.prepared
    rfl
  have hH : ∀ j, r0.final.heads (graphSlot d j) = 0 := fun j => hh0 _
  have hT : ∀ j, r0.final.tapes (graphSlot d j) = RecoveryBoundedColdGraph.insert []
      (RecoveryBoundedColdPrepared.input R (oracleSizeBound d R) (RecoveryBoundedSelectorLoop.capacity W)
        vals.length (Codec.clauses (unitPCP w vals)).length (RecoveryBoundedGraphBudget.scalarBacking W)
        (RecoveryBoundedRowProjection.bank (unitPCP w vals) R vals.length (bitInputOfCode R 0)
          (RecoveryBoundedGraphBudget.scalarBacking W)) (DedupBytes.fields (unitPCP w vals))) j := by
    intro j
    rw [ht0]
    by_cases he : ∃ k, RecoveryBoundedColdGraph.slots k = j
    · obtain ⟨k, rfl⟩ := he
      rw [← supplier_old, install_slot _ (supplierSlot_injective d), hprep k,
        RecoveryBoundedColdGraph.projection]
    · have hn : ∀ k, RecoveryBoundedColdGraph.slots k ≠ j := by simpa only [not_exists] using he
      rw [install_other _ _ _ _ (by
        intro k hk
        dsimp only [supplierSlot] at hk
        split_ifs at hk with hk1
        · exact hn _ (graphSlot_injective d hk)
        · exact graph_fresh d j k hk.symm), input_graph]
      have hz := RecoveryBoundedColdGraph.other [] (fun _ => []) (RecoveryBoundedColdPrepared.input R
        (oracleSizeBound d R) (RecoveryBoundedSelectorLoop.capacity W) vals.length
        (Codec.clauses (unitPCP w vals)).length (RecoveryBoundedGraphBudget.scalarBacking W)
        (RecoveryBoundedRowProjection.bank (unitPCP w vals) R vals.length (bitInputOfCode R 0)
          (RecoveryBoundedGraphBudget.scalarBacking W)) (DedupBytes.fields (unitPCP w vals))) j hn
      rw [RecoveryBoundedColdGraph.constant] at hz
      exact hz
  generalize hv : RecoveryBoundedColdGraph.budget (RecoveryBoundedGraphBudget.scalarBacking W) W R
    (oracleSizeBound d R) (boundedOracleVerifierCircuit (compactProjectionPCP ((unitPCP w vals).normalized R
      vals.length hw (le_refl _))) x (oracleSizeBound d R)) = v at hgrun hgs
  generalize hA : RecoveryBoundedColdGraph.insert []
      (RecoveryBoundedColdPrepared.input R (oracleSizeBound d R) (RecoveryBoundedSelectorLoop.capacity W)
        vals.length (Codec.clauses (unitPCP w vals)).length (RecoveryBoundedGraphBudget.scalarBacking W)
        (RecoveryBoundedRowProjection.bank (unitPCP w vals) R vals.length (bitInputOfCode R 0)
          (RecoveryBoundedGraphBudget.scalarBacking W)) (DedupBytes.fields (unitPCP w vals))) = A at hgrun hT
  have hgrun' : runFrom RecoveryBoundedColdGraph.machine v
      (initialConfiguration RecoveryBoundedColdGraph.machine A) = some rg := hgrun
  obtain ⟨r1, h1, _hc1, hs1, hhead, htape, _hkeep⟩ := RecoveryFocus.dock (graphSlot d) (graphSlot_injective d)
    RecoveryBoundedColdGraph.machine v r0.final.heads r0.final.tapes
    (initialConfiguration RecoveryBoundedColdGraph.machine A) hH hT rg hgrun'
  have whole := Composition.run_join (RecoveryFocus.machine (supplierSlot d) (USupply.machine d))
    (RecoveryFocus.machine (graphSlot d) RecoveryBoundedColdGraph.machine) _ _ _ r0 r1 h0 h1
  have hbud : budget d w R W vals hw x = USupply.budget d R vals.length W + 1 + v := by
    unfold budget circuit unitOuter
    rw [← hv]
  rw [hbud]
  refine ⟨Composition.joinedReceipt r0 r1, whole, ?_, ?_, ?_, ?_, ?_⟩
  · change r0.steps + 1 + r1.steps ≤ _
    omega
  · exact (htape 1657).trans hgt
  · exact (hhead 1657).trans hgh
  · exact (htape 144).trans hga
  · exact (hhead 144).trans hgah

end NearCubicGates.Close.ENP.UGraph
