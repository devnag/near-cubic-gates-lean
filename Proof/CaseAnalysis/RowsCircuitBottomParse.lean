import Proof.CaseAnalysis.RowsCircuitBottomLayout
import Proof.CaseAnalysis.RowsGateBankPorts

/-! The all-raw measured worker docks directly into the repeated bottom
bank. The actual PCPP domain is retained, and no global append cursor moves
while the original gate is decoded. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics RecoveryRootRound CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def parser:=RecoveryFocus.machine coreSlots (CloseoutRowsGateMeasured.machine false)

theorem parse_run_retained (cap core pos memberPos : ℕ) (bits out source membership : List Bool)
    (description wires : ℕ) (flag : Bool) (hin : 2*bits.length+1 ≤ cap)
    (hcap : CloseoutRowsGateMeasured.budget bits+1 ≤ cap) : ∃ bank result,
    runFrom parser (CloseoutRowsGateMeasured.budget bits)
      (cfg parser.start cap core pos memberPos bits out source membership description wires flag)=some result ∧
      result.steps ≤ CloseoutRowsGateMeasured.budget bits ∧
      result.final.heads=heads pos memberPos out description wires ∧
      (∀ i,result.final.tapes (coreSlots i)=CloseoutRowsGateBank.padded cap bank i) ∧
      CloseoutRowsGateMeasured.Output false core bits bank ∧
      Stored cap core out source membership description wires flag result.final.tapes ∧
      (∀ g,CanonicalWitnessCodec.decodeSupportedNormalizedGate core (value bits)=some g →
        result.final.tapes 994=ZeroPadding.pad cap
          (frame (CloseoutRowsGateSupport.gateMembers g.support))) := by
  obtain ⟨bank,run,meaning,bounds⟩:=CloseoutRowsGateBank.gate_run false cap core bits hin hcap
  have bitmap:=fun g hg=>CloseoutRowsGateBank.bitmap_retained false cap bits g hg _ _ run
  obtain ⟨base,hb,bt,bh,bs⟩:=run
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock coreSlots core_injective
    (CloseoutRowsGateMeasured.machine false) _ (heads pos memberPos out description wires)
    (data cap core bits out source membership description wires flag) _
    (heads_core pos memberPos out description wires)
    (data_core cap core bits out source membership description wires flag) base hb
  have outputs (i : Fin 1049) : r.final.tapes (coreSlots i)=CloseoutRowsGateBank.padded cap bank i:=by
    rw [rt,bt]
  refine ⟨bank,r,hr,rs ▸ bs,?_,outputs,meaning,⟨?_,?_,?_⟩,?_⟩
  · funext i
    refine Fin.addCases (m:=1049) (n:=10) ?_ ?_ i
    · intro j
      change r.final.heads (coreSlots j)=_
      rw [rh,bh]
      exact (heads_core pos memberPos out description wires j).symm
    · intro j
      exact (keep _ (core_other j)).1
  · intro i
    let k : Fin 1049:=⟨(scratchSlots i).val,scratch_small i⟩
    have he : coreSlots k=scratchSlots i:=Fin.ext rfl
    rw [←he,outputs]
    exact bounds k (scratch_not_core i)
  · change r.final.tapes (coreSlots 1035)=_
    rw [outputs]
    change ZeroPadding.pad 0 (bank 1035)=_
    rw [ZeroPadding.pad_zero]
    exact meaning.1
  · intro i
    exact ((keep _ (core_other i)).2).trans (data_extra cap core bits out source membership description wires flag i)
  · intro g hg
    exact (outputs 994).trans (bitmap g hg)

theorem parse_run (cap core pos memberPos : ℕ) (bits out source membership : List Bool)
    (description wires : ℕ) (flag : Bool) (hin : 2*bits.length+1 ≤ cap)
    (hcap : CloseoutRowsGateMeasured.budget bits+1 ≤ cap) : ∃ bank result,
    runFrom parser (CloseoutRowsGateMeasured.budget bits)
      (cfg parser.start cap core pos memberPos bits out source membership description wires flag)=some result ∧
      result.steps ≤ CloseoutRowsGateMeasured.budget bits ∧
      result.final.heads=heads pos memberPos out description wires ∧
      (∀ i,result.final.tapes (coreSlots i)=CloseoutRowsGateBank.padded cap bank i) ∧
      CloseoutRowsGateMeasured.Output false core bits bank ∧
      Stored cap core out source membership description wires flag result.final.tapes := by
  obtain ⟨bank,r,hr,hs,hh,ht,hm,store,_⟩:=
    parse_run_retained cap core pos memberPos bits out source membership description wires flag hin hcap
  exact ⟨bank,r,hr,hs,hh,ht,hm,store⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
