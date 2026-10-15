import Proof.Amplification.RecoveryPCPFormulaResumeSearchPairFrame
import Proof.Amplification.RecoveryFormulaPrefix

/-! The actual cold constructor now writes the complete externally framed
request of the accepted canonical proof-prefix search. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearchRequest
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceSlots (i : Fin 789) : Fin 796 := i.castAdd 7
def pairSlots (i : Fin 9) : Fin 796 :=
  if i=0 then 783 else if i=1 then 787 else ⟨787+i.val,by have hi:=i.isLt; omega⟩
theorem source_injective : Function.Injective sourceSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 796=>i.val) h)
theorem pair_injective : Function.Injective pairSlots := by
  intro i j h
  have hv:=congrArg (fun i : Fin 796=>i.val) h
  have hi:=i.isLt; have hj:=j.isLt
  apply Fin.ext
  dsimp [pairSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
noncomputable def first := RecoveryFocus.machine sourceSlots RecoveryPCPFormulaResumeSearch.readyMachine
noncomputable def last := RecoveryFocus.machine pairSlots RecoveryPCPFormulaResumeSearchPair.framedMachine
noncomputable def machine := Composition.machine first last
noncomputable def input (p : RawProjectionPCP) (R Q : Nat) : Fin 796→List Bool :=
  Fin.addCases (m:=789) (n:=7) (motive:=fun _=>List Bool)
    (RecoveryPCPFormulaResumeSearch.readyInput p R Q) (fun _=>[])
def budget (R Q count : Nat) (words : List (List Bool)) (payload : Nat) :=
  RecoveryPCPFormulaResumeSearch.readyBudget R Q count words+1+
    RecoveryPCPFormulaResumeSearchPair.framedBudget payload.bits (List.replicate (2^R) true)

theorem request_ready (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) : ∃ out,
    ClockJoin.ReadyRun machine (budget R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)
        (balancedCNFPayload (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)))
      (input p R Q) out ∧
      out 794=frame (RecoveryPrefixMeasure.request
        (balancedCNFPayload (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)) (2^R)) := by
  let payload:=balancedCNFPayload (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)
  obtain ⟨parts,hparts,p783,p787⟩ := RecoveryPCPFormulaResumeSearch.ready_parts p R Q hr hq x
  let a:=install sourceSlots (input p R Q) parts
  have ha:=hparts.focus sourceSlots source_injective (input p R Q) (by
    intro i; simp only [sourceSlots,input,Fin.addCases_left])
  obtain ⟨pair,hpair,p7⟩ := RecoveryPCPFormulaResumeSearchPair.framed_ready payload.bits (List.replicate (2^R) true)
  have ht : ∀ i : Fin 9,a (pairSlots i)=
      RecoveryPCPFormulaResumeSearchPair.fields payload.bits (List.replicate (2^R) true) i := by
    intro i
    by_cases h0 : i=0
    · subst i
      exact (install_slot sourceSlots source_injective _ parts 783).trans p783
    by_cases h1 : i=1
    · subst i
      exact (install_slot sourceSlots source_injective _ parts 787).trans p787
    have hv0 : i.val≠0 := fun h=>h0 (Fin.ext h)
    have hv1 : i.val≠1 := fun h=>h1 (Fin.ext h)
    let j : Fin 7 := ⟨i.val-2,by have hi:=i.isLt; omega⟩
    have he : pairSlots i=j.natAdd 789 := by
      apply Fin.ext
      simp only [pairSlots,h0,h1,ite_false,Fin.val_natAdd]
      dsimp [j]
      omega
    dsimp only [a]
    rw [he,install_other _ _ _ _ (by
      intro k hk
      have hkv:=congrArg (fun i : Fin 796=>i.val) hk
      have hkb:=k.isLt
      change k.val=789+j.val at hkv
      omega)]
    simp only [input,Fin.addCases_right,RecoveryPCPFormulaResumeSearchPair.fields,h0,h1,ite_false]
  have hb:=hpair.focus pairSlots pair_injective a ht
  refine ⟨_,ClockJoin.join first last _ _ _ _ _ ha hb,?_⟩
  exact (install_slot pairSlots pair_injective a pair 7).trans p7

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSearchRequest
