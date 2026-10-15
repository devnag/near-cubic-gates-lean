import Proof.Amplification.RecoveryCaseOneSourceMeaning
import Proof.CaseAnalysis.RecoverySearchCanonical

/-! The original normalized outer PCP and its one-request serialization view
give the identical bounded verifier circuit and full formula at that request. -/
namespace NearCubicWires.RepairSource.CloseoutRecoverySourceIdentity
open SourceInterfaces BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem compiled_ext {n : ℕ} {prior : BooleanDAGBuilder n}
    {f : BoolFunction n} (a b : FinitePredicateCircuit.CompiledWire prior f)
    (hf : a.final = b.final) (ho : a.output.val = b.output.val) : a = b := by
  rcases a with ⟨af, ae, ao, ac⟩
  rcases b with ⟨bf, be, bo, bc⟩
  dsimp only at hf ho
  cases hf
  have hout : ao = bo := Fin.ext ho
  cases hout
  have he : ae = be := by
    rcases ae with ⟨asuffix, ah⟩
    rcases be with ⟨bsuffix, bh⟩
    have hs := List.append_cancel_left (ah.symm.trans bh)
    cases hs
    rfl
  cases he
  rfl

theorem source_circuit {v : OrdinaryVerifier} {T U : ℕ→ℕ}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest→InputRequest) (R Q : ℕ→ℕ)
    (hr : ∀ r : InputRequest,(source.output (encode r)).width ≤ R r.1)
    (hq : ∀ r : InputRequest,(source.output (encode r)).queries ≤ Q r.1)
    (r : InputRequest) (bound : ℕ) :
    boundedOracleVerifierCircuit (normalizedSourcePCP source H encode R Q hr hq) r.2 bound=
      boundedOracleVerifierCircuit
        (compactProjectionPCP ((source.output (encode r)).normalized (R r.1) (Q r.1) (hr r) (hq r)))
        r.2 bound := by
  rcases r with ⟨n,x⟩
  let globalPCP : ProjectionPCP H.timedView H.time :=
    { nativeWidth := R
      queryCount := Q
      queryAddressBits := (normalizedSourcePCP source H encode R Q hr hq).queryAddressBits
      decision := (normalizedSourcePCP source H encode R Q hr hq).decision
      constructionSteps := fun _ => 0 }
  let localPCP : ProjectionPCP ⟨fun _ _ => false, fun _ _ => 0⟩ (fun _ => 0) :=
    { nativeWidth := fun _ => R n
      queryCount := fun _ => Q n
      queryAddressBits := (compactProjectionPCP
        ((source.output (encode ⟨n,x⟩)).normalized (R n) (Q n) (hr ⟨n,x⟩) (hq ⟨n,x⟩))).queryAddressBits
      decision := (compactProjectionPCP
        ((source.output (encode ⟨n,x⟩)).normalized (R n) (Q n) (hr ⟨n,x⟩) (hq ⟨n,x⟩))).decision
      constructionSteps := fun _ => 0 }
  have hrows (count : ℕ) (hcount : count ≤ bound)
      (rows : List (BitInput (R n)))
      (builder : BooleanDAGBuilder (descriptionWidth (R n) bound)) :
      compileVerifierRows globalPCP x count hcount builder rows =
        compileVerifierRows localPCP x count hcount builder rows := by
    induction rows generalizing builder with
    | nil => rfl
    | cons head tail ih =>
        apply compiled_ext
        all_goals
          simp only [compileVerifierRows, FinitePredicateCircuit.CompiledWire.prepend]
          rw [ih]
          rfl
  have hcount (builder : BooleanDAGBuilder (descriptionWidth (R n) bound))
      (count : Fin bound) :
      compileFixedCount globalPCP x builder count =
        compileFixedCount localPCP x builder count := by
    apply compiled_ext
    all_goals
      simp only [compileFixedCount, FinitePredicateCircuit.CompiledWire.prepend]
      rw [hrows]
      rfl
  have hcounts (counts : List (Fin bound))
      (builder : BooleanDAGBuilder (descriptionWidth (R n) bound)) :
      compileCountCases globalPCP x builder counts =
        compileCountCases localPCP x builder counts := by
    induction counts generalizing builder with
    | nil => rfl
    | cons head tail ih =>
        apply compiled_ext
        all_goals
          simp only [compileCountCases, FinitePredicateCircuit.CompiledWire.prepend]
          rw [hcount, ih]
          rfl
  exact congrArg (fun c => c.final.finish c.output)
    (hcounts (List.ofFn id) (BooleanDAGBuilder.empty (descriptionWidth (R n) bound)))

theorem source_formula {v : OrdinaryVerifier} {T U : ℕ→ℕ}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest→InputRequest) (R Q : ℕ→ℕ)
    (hr : ∀ r : InputRequest,(source.output (encode r)).width ≤ R r.1)
    (hq : ∀ r : InputRequest,(source.output (encode r)).queries ≤ Q r.1)
    (r : InputRequest) (bound : ℕ) :
    boundedOracleRecoveryFormula (normalizedSourcePCP source H encode R Q hr hq) r.2 bound=
      boundedOracleRecoveryFormula
        (compactProjectionPCP ((source.output (encode r)).normalized (R r.1) (Q r.1) (hr r) (hq r)))
        r.2 bound := by
  unfold boundedOracleRecoveryFormula
  rw [source_circuit source H encode R Q hr hq r bound]
  rfl

end
end NearCubicWires.RepairSource.CloseoutRecoverySourceIdentity
