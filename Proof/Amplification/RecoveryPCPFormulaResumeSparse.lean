import Proof.Amplification.RecoveryPCPFormulaResumeSerialize
import Proof.MachineModel.OrdinaryZeroUnpadding

/-! Run the same complete original formula machine with initially blank
false-only scratch. The existing inverse-padding simulation preserves every
transition and charges only cells actually written by that machine. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSerialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
open CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def omitBlank (word : List Bool) : List Bool := if word=List.replicate word.length false then [] else word
theorem omit_blank (n : Nat) : omitBlank (List.replicate n false)=[] := by
  simp only [omitBlank,List.length_replicate,ite_true]
theorem pad_omitBlank (word : List Bool) : ZeroPadding.pad word.length (omitBlank word)=word := by
  unfold omitBlank
  split_ifs with h
  · simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
    exact h.symm
  · simp only [ZeroPadding.pad,Nat.sub_self,List.replicate_zero,List.append_nil]

noncomputable def sparseInput (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) (i : Fin 716) :=
  omitBlank (input p R Q cap logCap resetCap i)
noncomputable def initialCaps (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) (i : Fin 716) :=
  (input p R Q cap logCap resetCap i).length

theorem sparse_initial (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) :
    ZeroPadding.config (initialCaps p R Q cap logCap resetCap)
      (initialConfiguration machine (sparseInput p R Q cap logCap resetCap))=
      initialConfiguration machine (input p R Q cap logCap resetCap) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    exact pad_omitBlank _

theorem sparse_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (cap logCap resetCap : Nat)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : RecoveryPCPFormulaResumeRow.budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    run machine (budget cap R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x))
      (sparseInput p R Q cap logCap resetCap)=some r ∧
      r.final.tapes 714=frame (balancedCNFPayload
        (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)).bits ∧
      r.steps≤budget cap R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) := by
  obtain ⟨base,hbase,bt,bs⟩ := serialize_run p R Q hr hq x cap logCap resetCap hc hl hz
  change runFrom machine _ (initialConfiguration machine (input p R Q cap logCap resetCap))=some base at hbase
  rw [←sparse_initial] at hbase
  obtain ⟨r,hrun,rf,rs,_rp⟩ := ZeroPadding.run_unpad machine (initialCaps p R Q cap logCap resetCap) _ _ base hbase
  refine ⟨r,hrun,?_,rs.trans_le bs⟩
  have h:=(congrArg (fun c=>c.tapes 714) rf).trans bt
  change ZeroPadding.pad 0 (r.final.tapes 714)=_ at h
  simpa only [ZeroPadding.pad_zero] using h

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSerialize
