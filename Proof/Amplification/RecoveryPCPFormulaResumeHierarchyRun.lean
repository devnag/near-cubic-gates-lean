import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyState

/-! The one selected source is physically executed on the literal hierarchy
input, then its original query/clause streams feed the complete cold PCP
recovery formula. No serialized intermediate or realization is supplied. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem request_positive (k CH Cpad : Nat) (code x : List Bool) (hpad : k+3≤Cpad) :
    1≤(HierarchyStreams.request k CH Cpad code x).1 := by
  have h:=(HierarchyPadding.linear_length k CH Cpad code x hpad).1
  change 1≤(HierarchyPadding.rawInput k CH Cpad code x).length
  omega

def normalized (k CH Cpad : Nat) (code x : List Bool) (hpad : k+3≤Cpad) :=
  (source.output (HierarchyStreams.request k CH Cpad code x)).normalized
    (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x)
    (Dimensions.width_fits source _ (request_positive k CH Cpad code x hpad))
    (Dimensions.queries_fit source _ (request_positive k CH Cpad code x hpad))
def budget (k CH Cpad : Nat) (code : List Bool) {n : Nat} (x : BitInput n) (hpad : k+3≤Cpad) :=
  HierarchyStreams.budget source k CH Cpad code (List.ofFn x)+1+
    RecoveryPCPFormulaResumeCold.cursorBudget
      (HierarchyStreams.R source k CH Cpad code (List.ofFn x))
      (HierarchyStreams.Q source k CH Cpad code (List.ofFn x))
      (Codec.clauses (source.output (HierarchyStreams.request k CH Cpad code (List.ofFn x)))).length
      (RecoveryPCPFormulaResume.words (compactProjectionPCP (normalized source k CH Cpad code (List.ofFn x) hpad)) x)

private theorem embedded_initial {t s : Nat} (p : Machine t s) (hpos : 0<t) (word : List Bool) :
    TapeEmbedding.config (fun _ : Fin 785=>0) (fun _ : Fin 785=>[])
      (initialConfiguration p (SourceHandoff.sourceTapes word))=
      initialConfiguration (TapeEmbedding.machine 785 p) (SourceHandoff.sourceTapes word) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=t) (n:=785) (fun i=>?_) (fun i=>?_) i
    · change (Fin.addCases (m:=t) (n:=785) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)) (i.castAdd 785)=0
      rw [Fin.addCases_left]
    · change (Fin.addCases (m:=t) (n:=785) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)) (i.natAdd t)=0
      rw [Fin.addCases_right]
  · funext i
    refine Fin.addCases (m:=t) (n:=785) (fun i=>?_) (fun i=>?_) i
    · change (Fin.addCases (m:=t) (n:=785) (motive:=fun _=>List Bool)
        (SourceHandoff.sourceTapes word) (fun _=>[])) (i.castAdd 785)=SourceHandoff.sourceTapes word (i.castAdd 785)
      rw [Fin.addCases_left]
      rfl
    · change (Fin.addCases (m:=t) (n:=785) (motive:=fun _=>List Bool)
        (SourceHandoff.sourceTapes word) (fun _=>[])) (i.natAdd t)=SourceHandoff.sourceTapes word (i.natAdd t)
      rw [Fin.addCases_right]
      simp only [SourceHandoff.sourceTapes,Fin.val_natAdd]
      rw [if_neg (by omega)]

theorem constructor_run (k CH Cpad : Nat) (code bound : List Bool) {n : Nat} (x : BitInput n)
    (hpad : k+3≤Cpad) : ∃ r,
    run (machine source k CH Cpad code) (budget source k CH Cpad code x hpad)
      (SourceHandoff.sourceTapes (frame (List.ofFn x)++frame bound))=some r ∧
      r.final.tapes ((783 : Fin 785).natAdd (HierarchyStreams.tapes source k))=
        frame (balancedCNFPayload (outerProofRecoveryFormula
          (compactProjectionPCP (normalized source k CH Cpad code (List.ofFn x) hpad)) x)).bits ∧
      r.steps≤budget source k CH Cpad code x hpad := by
  obtain ⟨prior,hprior,priorSteps,hfields⟩ :=
    HierarchyStreams.scalar_run source k CH Cpad code (List.ofFn x) bound hpad
  let a:=TapeEmbedding.receipt (fun _ : Fin 785=>0) (fun _ : Fin 785=>[]) prior
  have ha:=TapeEmbedding.run_embed (HierarchyStreams.machine source k CH Cpad code)
    (fun _ : Fin 785=>0) (fun _ : Fin 785=>[]) _ _ prior hprior
  have hi:=embedded_initial (HierarchyStreams.machine source k CH Cpad code)
    (by omega) (frame (List.ofFn x)++frame bound)
  rw [hi] at ha
  obtain ⟨codeRun,hcode,ct,codeSteps⟩ := RecoveryPCPFormulaResumeCold.cursor_run
    (source.output (HierarchyStreams.request k CH Cpad code (List.ofFn x)))
    (HierarchyStreams.R source k CH Cpad code (List.ofFn x))
    (HierarchyStreams.Q source k CH Cpad code (List.ofFn x))
    (Dimensions.width_fits source _ (request_positive k CH Cpad code (List.ofFn x) hpad))
    (Dimensions.queries_fit source _ (request_positive k CH Cpad code (List.ofFn x) hpad)) x
  obtain ⟨b,hb,_bc,bSteps,_bh,bt,_bk⟩ := RecoveryFocus.dock (slots source k) (slots_injective source k)
    RecoveryPCPFormulaResumeCold.cursorMachine _ a.final.heads a.final.tapes
    ⟨RecoveryPCPFormulaResumeCold.cursorMachine.start,RecoveryPCPFormulaResumeCold.countHeads,
      RecoveryPCPFormulaResumeCold.input (source.output (HierarchyStreams.request k CH Cpad code (List.ofFn x)))
        (HierarchyStreams.R source k CH Cpad code (List.ofFn x))
        (HierarchyStreams.Q source k CH Cpad code (List.ofFn x))⟩
    (dock_heads source k CH Cpad code (List.ofFn x) bound prior.final hfields)
    (dock_tapes source k CH Cpad code (List.ofFn x) bound prior.final hfields) codeRun hcode
  have whole:=Composition.run_join (first source k CH Cpad code) (last source k) _ _ _ a b ha hb
  refine ⟨_,whole,?_,?_⟩
  · change b.final.tapes (slots source k 783)=_
    rw [bt,ct]
    rfl
  · change a.steps+1+b.steps≤_
    rw [bSteps]
    change prior.steps+1+codeRun.steps≤_
    unfold budget normalized
    exact Nat.add_le_add (Nat.add_le_add_right priorSteps 1) codeSteps

end
end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeHierarchy
