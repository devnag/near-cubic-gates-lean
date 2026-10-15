import Proof.SourceAssembly.SourceThresholdRetained

/- The actual full THR circuit is framed at its measured logical append head.
The native and declared-support streams remain available in their old ports. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyCircuitFrame
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity SupplierPipeline CompilerSemantics
open RepairSource.ProjectionNormalization
open CloseoutRowsOriginalClause (index negative)
noncomputable section

theorem fresh_forward {t s extra : Nat} (p : Machine t s) (i : Fin extra) :
    CursorRestore.NoLeft (TapeEmbedding.machine extra p) (i.natAdd t) := by
  intro q bs a ha
  obtain ⟨b,hb,he⟩:=Option.map_eq_some_iff.mp ha
  subst a
  simp only [TapeEmbedding.action,Fin.addCases_right]
  decide

theorem frame_forward : CursorRestore.NoLeft (CloseoutRowsTupleSeek.frameMachine true) 1 := by
  intro q bs a ha
  fin_cases q <;> simp [CloseoutRowsTupleSeek.frameMachine,CloseoutRowsTouching.FrameStream.machine] at ha
  all_goals subst a;simp

theorem pair_forward : CursorRestore.NoLeft (CloseoutRowsTupleSeek.pairMachine true) 1 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.embedded_forward 2 _ 1 frame_forward)
    (EquationRowCuts.unselected_forward _ _ 1 (by decide))

theorem assembler_forward : CursorRestore.NoLeft SourceAssemblySymmetricAssemble.machine 5 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.focus_forward _ (by decide) _ 2 EquationRowRaw.header_field_forward)
    (CursorRestore.composition_forward _ _ _
      (CursorRestore.focus_forward _ (by decide) _ 1 frame_forward)
      (CursorRestore.focus_forward _ (by decide) _ 1 (CursorRestore.repeat_forward _ _ 1 pair_forward)))

theorem threshold_forward : CursorRestore.NoLeft SourceAssemblyThresholdPhysical.machine 207 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (fresh_forward _ (1 : Fin 4))
      (EquationRowCuts.unselected_forward _ _ 207 (by decide)))
    (CursorRestore.focus_forward _ SourceAssemblyThresholdPhysical.slots_inj _ 5 assembler_forward)

def machine:=AppendOutputFrame.machine SourceAssemblyThresholdPhysical.machine 207

theorem run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right)+1 ≤ C)
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits) :
    let c:=normalizedThresholdParityCircuit ((a.output r).systematicSupport
      ⟨index ((a.output r).clauses ci).left,hk⟩)
    ∃ A,Step machine (2*SourceAssemblyThresholdPhysical.budget a r ci C hk+
        4*(PacketProduction.thrWord c).length+7) (fun _=>0)
      (AppendOutputFrame.input (SourceAssemblyThresholdReady.input a r ci C)) (fun _=>0) A ∧
      A 212=frame (PacketProduction.thrWord c) ∧
      A 207=PacketProduction.thrWord c ∧
      A 208=CloseoutRowsTupleSeek.supportWord (SourceAssemblyThresholdPhysical.gates r.arity
        (SourceAssemblySymmetricHeaderQuery.count a r ci)
        (SourceAssemblyThresholdCache.bits a r ci hk)) ∧ A 131=frame (natWord r.arity) := by
  dsimp only
  obtain ⟨A,⟨source,hr,rh,rt,rs⟩,hn,hs,h131⟩:=SourceAssemblyThresholdPhysical.run_retained a r ci C hc hk
  rw [SourceAssemblyThresholdCanonical.native_eq] at hn
  obtain ⟨s,sr,st,sh,sk,ss⟩:=PCPPNativeFrame.frame_run
    SourceAssemblyThresholdPhysical.machine 207 threshold_forward
    (SourceAssemblyThresholdPhysical.budget a r ci C hk)
    (SourceAssemblyThresholdReady.input a r ci C) source hr
    (PacketProduction.thrWord (normalizedThresholdParityCircuit
      ((a.output r).systematicSupport ⟨index ((a.output r).clauses ci).left,hk⟩)))
    (by rw [rt];exact hn) (by rw [rh];exact SourceAssemblyThresholdCanonical.native_head a r ci hk)
  refine ⟨s.final.tapes,(Step.of_run sr (funext sh) rfl).enlarge (by omega),st,?_,?_,?_⟩
  · exact (sk 207).trans (by rw [rt];exact hn)
  · exact (sk 208).trans (by rw [rt];exact hs)
  · exact (sk 131).trans (by rw [rt];exact h131)

end
end SourceAssemblyCircuitFrame
