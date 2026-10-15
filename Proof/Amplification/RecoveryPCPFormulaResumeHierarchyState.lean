import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyLayout

/-! Exact tape and cursor transport from the actual hierarchy stream
endpoint into the cold recovery formula consumer. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem dock_heads {s : Nat} (k CH Cpad : Nat) (code x bound : List Bool)
    (c : Configuration (HierarchyStreams.tapes source k) s)
    (hf : HierarchyStreams.Fields source k CH Cpad code x bound c) (i : Fin 785) :
    (TapeEmbedding.config (fun _ : Fin 785=>0) (fun _ : Fin 785=>[]) c).heads (slots source k i)=
      RecoveryPCPFormulaResumeCold.countHeads i := by
  by_cases h0 : i.val=0
  · have he : i=(0 : Fin 785) := Fin.ext h0
    subst i
    change (Fin.addCases (m:=HierarchyStreams.tapes source k) (n:=785) (motive:=fun _=>Nat) c.heads (fun _ : Fin 785=>0)) ((port source k 0).castAdd 785)=_
    rw [Fin.addCases_left]
    exact hf.widthHead
  by_cases h28 : i.val=28
  · have he : i=(28 : Fin 785) := Fin.ext h28
    subst i
    change (Fin.addCases (m:=HierarchyStreams.tapes source k) (n:=785) (motive:=fun _=>Nat) c.heads (fun _ : Fin 785=>0)) ((port source k 1).castAdd 785)=_
    rw [Fin.addCases_left]
    exact hf.queriesHead
  by_cases h66 : i.val=66
  · have he : i=(66 : Fin 785) := Fin.ext h66
    subst i
    change (Fin.addCases (m:=HierarchyStreams.tapes source k) (n:=785) (motive:=fun _=>Nat) c.heads (fun _ : Fin 785=>0)) ((port source k 2).castAdd 785)=_
    rw [Fin.addCases_left]
    exact hf.queryStreamHead
  by_cases h67 : i.val=67
  · have he : i=(67 : Fin 785) := Fin.ext h67
    subst i
    change (Fin.addCases (m:=HierarchyStreams.tapes source k) (n:=785) (motive:=fun _=>Nat) c.heads (fun _ : Fin 785=>0)) ((port source k 3).castAdd 785)=_
    rw [Fin.addCases_left]
    exact hf.clauseStreamHead
  by_cases h68 : i.val=68
  · have he : i=(68 : Fin 785) := Fin.ext h68
    subst i
    change (Fin.addCases (m:=HierarchyStreams.tapes source k) (n:=785) (motive:=fun _=>Nat) c.heads (fun _ : Fin 785=>0)) ((port source k 4).castAdd 785)=_
    rw [Fin.addCases_left]
    exact hf.clauseCountHead
  simp only [slots,h0,h28,h66,h67,h68,ite_false,TapeEmbedding.config,Fin.addCases_right,
    RecoveryPCPFormulaResumeCold.countHeads]

theorem dock_tapes {s : Nat} (k CH Cpad : Nat) (code x bound : List Bool)
    (c : Configuration (HierarchyStreams.tapes source k) s)
    (hf : HierarchyStreams.Fields source k CH Cpad code x bound c) (i : Fin 785) :
    (TapeEmbedding.config (fun _ : Fin 785=>0) (fun _ : Fin 785=>[]) c).tapes (slots source k i)=
      RecoveryPCPFormulaResumeCold.input (source.output (HierarchyStreams.request k CH Cpad code x))
        (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x) i := by
  by_cases h0 : i.val=0
  · have he : i=(0 : Fin 785) := Fin.ext h0
    subst i
    change (Fin.addCases (m:=HierarchyStreams.tapes source k) (n:=785) (motive:=fun _=>List Bool) c.tapes (fun _ : Fin 785=>[])) ((port source k 0).castAdd 785)=_
    rw [Fin.addCases_left]
    exact hf.width
  by_cases h28 : i.val=28
  · have he : i=(28 : Fin 785) := Fin.ext h28
    subst i
    change (Fin.addCases (m:=HierarchyStreams.tapes source k) (n:=785) (motive:=fun _=>List Bool) c.tapes (fun _ : Fin 785=>[])) ((port source k 1).castAdd 785)=_
    rw [Fin.addCases_left]
    exact hf.queries
  by_cases h66 : i.val=66
  · have he : i=(66 : Fin 785) := Fin.ext h66
    subst i
    change (Fin.addCases (m:=HierarchyStreams.tapes source k) (n:=785) (motive:=fun _=>List Bool) c.tapes (fun _ : Fin 785=>[])) ((port source k 2).castAdd 785)=_
    rw [Fin.addCases_left]
    exact hf.queryStream
  by_cases h67 : i.val=67
  · have he : i=(67 : Fin 785) := Fin.ext h67
    subst i
    change (Fin.addCases (m:=HierarchyStreams.tapes source k) (n:=785) (motive:=fun _=>List Bool) c.tapes (fun _ : Fin 785=>[])) ((port source k 3).castAdd 785)=_
    rw [Fin.addCases_left]
    exact hf.clauseStream
  by_cases h68 : i.val=68
  · have he : i=(68 : Fin 785) := Fin.ext h68
    subst i
    change (Fin.addCases (m:=HierarchyStreams.tapes source k) (n:=785) (motive:=fun _=>List Bool) c.tapes (fun _ : Fin 785=>[])) ((port source k 4).castAdd 785)=_
    rw [Fin.addCases_left]
    exact hf.clauseCount
  simp only [slots,h0,h28,h66,h67,h68,ite_false,TapeEmbedding.config,Fin.addCases_right,
    RecoveryPCPFormulaResumeCold.input]

end
end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeHierarchy
