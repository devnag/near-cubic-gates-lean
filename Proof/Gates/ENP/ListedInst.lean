import Proof.Gates.ENP.ListedStage
import Proof.Gates.Interfaces.Transfer

set_option autoImplicit false

namespace NearCubicGates.Close.ENP.UInst

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.RecoveryChoice NearCubicWires.OuterPCPRecovery NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicGates.Close.Transfer NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces

/-- The cap of stages 1 and 3 is the gadget transfer's `q^G` cap. -/
theorem bound_eq (s : GateSources) (g : GateParams) (ν : ℕ) :
    oracleSizeBound g.degree (g.width s ν) = g.bound s ν := rfl

/-- **Stage 1** (`sec:all-lengths`): the flag is `SrcExists`, the description is that of `B*_src = firstSrc`. -/
theorem stage1_run (s : GateSources) (g : GateParams) (ν : ℕ) (z : BitInput (2 ^ ν)) (post : List Bool) (W : ℕ)
    (hb : 0 < g.bound s ν)
    (hW : originalWorkspace (g.width s ν) (g.bound s ν) (List.ofFn z).length (List.ofFn z).length ≤ W)
    (hsource : (DedupBytes.fields (unitPCP ν (List.ofFn z))).length ≤ W) (htwo : 2 ^ g.width s ν ≤ W) :
    ∃ c ≤ UStage.cost g.degree ν (g.width s ν) W (List.ofFn z) (g.nu_lt_width s ν).le z, ∃ final,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (UStage.program g.degree) c
        (initialConfiguration (UStage.program g.degree).base.machine
          (UStage.input g.degree (RepairOrdinary.frame (List.ofFn z) ++ post) (g.width s ν) W)) final ∧
      (UStage.program g.degree).base.machine.halted final.control = true ∧
      (readTapeBit (final.tapes (UStage.flagPort g.degree)) 0 = true ↔ g.SrcExists s ν z) ∧
      (∀ h : g.SrcExists s ν z, final.tapes (UStage.descPort g.degree) =
        RepairOrdinary.frame (canonicalBoundedCircuitDescription (g.bound s ν) (g.firstSrc s ν z h))) ∧
      (final.tapes (UStage.queryPort g.degree)).length ≤ c ∧ final.heads (UStage.queryPort g.degree) = 0 := by
  obtain ⟨c, hc, final, tr, hal, hflag, hdesc, hq, hqh⟩ := UStage.stage_run g.degree (List.ofFn z) post ν
    (g.width s ν) W (by simp) (g.nu_lt_width s ν).le z hb hW hsource htwo
  refine ⟨c, hc, final, tr, hal, ?_, fun h => hdesc h, hq, hqh⟩
  rw [hflag, caseTwo_true]
  rfl

/-- **Stage 3** (`sec:all-lengths`): on the first honest table `t`, the flag is the small-oracle condition of the match PCP
(Case 2 given stages 1–2), the description is that of its canonical oracle. -/
theorem stage3_run (s : GateSources) (g : GateParams) (ν : ℕ) (z : BitInput (2 ^ ν)) {ℓ : ℕ}
    (hℓ : ℓ ≤ g.width s ν) (t : BitInput (2 ^ ℓ)) (post : List Bool) (W : ℕ)
    (hb : 0 < g.bound s ν)
    (hW : originalWorkspace (g.width s ν) (g.bound s ν) (List.ofFn t).length (List.ofFn t).length ≤ W)
    (hsource : (DedupBytes.fields (unitPCP ℓ (boolFunctionTable (tableOracle t)))).length ≤ W)
    (htwo : 2 ^ g.width s ν ≤ W) :
    ∃ c ≤ UStage.cost g.degree ℓ (g.width s ν) W (boolFunctionTable (tableOracle t)) hℓ z, ∃ final,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (UStage.program g.degree) c
        (initialConfiguration (UStage.program g.degree).base.machine
          (UStage.input g.degree (RepairOrdinary.frame (List.ofFn t) ++ post) (g.width s ν) W)) final ∧
      (UStage.program g.degree).base.machine.halted final.control = true ∧
      (readTapeBit (final.tapes (UStage.flagPort g.degree)) 0 = true ↔
        SmallOracle (g.matchPCP s ν hℓ t) g.degree z) ∧
      (∀ small : SmallOracle (g.matchPCP s ν hℓ t) g.degree z, final.tapes (UStage.descPort g.degree) =
        RepairOrdinary.frame (canonicalBoundedCircuitDescription (g.bound s ν)
          (oracleSelector (g.matchPCP s ν hℓ t) g.degree z small).circuit)) ∧
      (final.tapes (UStage.queryPort g.degree)).length ≤ c ∧ final.heads (UStage.queryPort g.degree) = 0 := by
  have hv := boolFunctionTable_tableOracle t
  obtain ⟨c, hc, final, tr, hal, hflag, hdesc, hq, hqh⟩ := UStage.stage_run g.degree
    (boolFunctionTable (tableOracle t)) post ℓ (g.width s ν) W (by rw [hv]; simp) hℓ z hb (by rw [hv]; exact hW)
    hsource htwo
  rw [hv] at tr
  refine ⟨c, hc, final, tr, hal, ?_, fun small => hdesc small, hq, hqh⟩
  rw [hflag, caseTwo_true]
  rfl

/-- In Case 2, stage 3's description is that of `B*_pf` (`g.selectedPair`'s second circuit). -/
theorem stage3_pf (s : GateSources) (g : GateParams) (ν : ℕ) (z : BitInput (2 ^ ν)) (h : g.IsCaseTwo s ν z) :
    (oracleSelector (g.matchPCP s ν h.2.2.1 (Classical.choice (existsFirstTable _ h.2.1)).table) g.degree z
      h.2.2.2).circuit = (g.selectedPair s ν z h).pf := rfl

end NearCubicGates.Close.ENP.UInst
