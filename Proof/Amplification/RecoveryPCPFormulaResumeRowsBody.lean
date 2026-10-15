import Proof.Amplification.RecoveryPCPFormulaResumeRowRandomness

/-! One actual randomness iteration appends its original row formula and
advances the same physical binary randomness field for the following row. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRows
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization
open RecoveryPCPFormulaResumeRowReset CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bodyMachine := Composition.machine RecoveryPCPFormulaResumeRowReusable.machine
  RecoveryPCPFormulaResumeRowRandomness.machine
def bodyBudget (cap R Q count : Nat) := RecoveryPCPFormulaResumeRowReusable.rowBudget cap R Q count+4*R+3
noncomputable def rowWord (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (k : Nat) :=
  FieldList.stream (RecoveryPCPFormulaResume.rowWords (compactProjectionPCP (p.normalized R Q hr hq)) x (bitInputOfCode R k))

theorem body_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (k cap logCap resetCap : Nat) (out : List Bool)
    (hk : k+1<2^R) (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : RecoveryPCPFormulaResumeRow.budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    runFrom bodyMachine (bodyBudget cap R Q (Codec.clauses p).length)
      ⟨bodyMachine.start,heads cap (DedupBytes.fields p) out (Codec.clauses p).length,
        input cap (DedupBytes.fields p) out (Codec.clauses p).length p R Q (bitInputOfCode R k) logCap resetCap⟩=some r ∧
      r.final.heads=heads cap (DedupBytes.fields p) (out++rowWord p R Q hr hq x k) (Codec.clauses p).length ∧
      r.final.tapes=input cap (DedupBytes.fields p) (out++rowWord p R Q hr hq x k)
        (Codec.clauses p).length p R Q (bitInputOfCode R (k+1)) logCap resetCap ∧
      r.steps≤bodyBudget cap R Q (Codec.clauses p).length := by
  obtain ⟨a,ha,ah,atapes,asteps⟩ := RecoveryPCPFormulaResumeRowReusable.row_run p R Q hr hq x
    (bitInputOfCode R k) cap logCap resetCap out hc hl hz
  obtain ⟨b,hb,bh,bt,bs⟩ := RecoveryPCPFormulaResumeRowRandomness.increment_run p R Q cap logCap resetCap k
    (DedupBytes.fields p) (out++rowWord p R Q hr hq x k) (Codec.clauses p).length hk
  have he : Composition.restart a.final RecoveryPCPFormulaResumeRowRandomness.machine.start=
      (⟨RecoveryPCPFormulaResumeRowRandomness.machine.start,
        heads cap (DedupBytes.fields p) (out++rowWord p R Q hr hq x k) (Codec.clauses p).length,
        input cap (DedupBytes.fields p) (out++rowWord p R Q hr hq x k)
          (Codec.clauses p).length p R Q (bitInputOfCode R k) logCap resetCap⟩ : Configuration 318 _) :=
    configuration_ext rfl ah atapes
  rw [←he] at hb
  have hall:=Composition.run_join RecoveryPCPFormulaResumeRowReusable.machine RecoveryPCPFormulaResumeRowRandomness.machine
    _ _ _ a b ha hb
  have ht : RecoveryPCPFormulaResumeRowReusable.rowBudget cap R Q (Codec.clauses p).length+1+(4*R+2)=
      bodyBudget cap R Q (Codec.clauses p).length := by unfold bodyBudget; omega
  rw [ht] at hall
  refine ⟨_,hall,bh,bt,?_⟩
  change a.steps+1+b.steps≤_
  unfold bodyBudget
  omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRows
