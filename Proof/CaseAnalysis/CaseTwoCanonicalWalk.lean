import Proof.CaseAnalysis.CaseTwoTraversalLoop
import Proof.CaseAnalysis.CaseTwoTraversalForward
import Proof.CaseAnalysis.CaseTwoCanonicalRows

/-! The original recovered canonical description physically yields its
native node/output word and actual node count in the same traversal. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.CanonicalWalk
open LocalBitMultitape RepairRepresentation OuterPCPRecovery Traversal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def body {n : ℕ} (c : BooleanCircuit n):=c.nodes.flatMap PCPPRequestNodeSchema.native++natWord c.output.val
def input {n : ℕ} (C bound : ℕ) (c : BooleanCircuit n):=
  Traversal.data C (boundedCircuitFieldLimit n bound) 0 (canonicalBoundedCircuitDescription bound c) 0 [] [] false
def budget {n : ℕ} (C : ℕ) (c : BooleanCircuit n):=256*(c.size+1)*(C+1)

theorem traverse_run {n bound : ℕ} (C : ℕ) (c : BooleanCircuit n) (hc : c.size≤bound)
    (h : Fits C (boundedCircuitFieldLimit n bound) (canonicalBoundedCircuitDescription bound c).length bound) :
    ∃ r,run Traversal.machine (budget C c) (input C bound c)=some r ∧ r.steps≤budget C c ∧
      r.final.tapes 27=body c ∧ r.final.heads 27=(body c).length ∧
      r.final.tapes 29=List.replicate c.size true ∧ r.final.heads 29=0 ∧
      r.final.tapes 0=ZeroPadding.pad C (frame (canonicalBoundedCircuitDescription bound c)) := by
  obtain ⟨r,hr,hs,hh,ht⟩:=loop_run C (boundedCircuitFieldLimit n bound)
    (canonicalBoundedCircuitDescription bound c).length bound c.nodes 0 c.output.val [] (canonicalTail bound c) [] h
    (by rw [List.nil_append,canonical_word_eq])
    (by simpa only [Nat.zero_add,BooleanCircuit.size] using hc) (canonical_values c hc) (canonical_output c hc)
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hr hh ht
  rw [canonical_word_eq] at hr ht
  have hi : cfg 0 (Traversal.heads []) (Traversal.data C (boundedCircuitFieldLimit n bound) 0
      (canonicalBoundedCircuitDescription bound c) 0 [] [] false)=
      initialConfiguration Traversal.machine (input C bound c):=by
    apply configuration_ext
    · rfl
    · funext i;change Traversal.heads [] i=0;simp [Traversal.heads]
    · rfl
  rw [hi] at hr
  refine ⟨r,hr,hs,?_,?_,?_,?_,?_⟩
  · rw [ht];rfl
  · rw [hh];rfl
  · rw [ht];rfl
  · rw [hh];rfl
  · rw [ht]
    change ZeroPadding.pad 0 (ZeroPadding.pad C (frame (canonicalBoundedCircuitDescription bound c)))=_
    rw [ZeroPadding.pad_zero]

noncomputable def measured:=AppendOutputLength.machine Traversal.machine 27
def measuredInput {n : ℕ} (C bound : ℕ) (c : BooleanCircuit n):=
  AppendOutputLength.input (AppendOutputLength.input (input C bound c))

theorem measured_run {n bound : ℕ} (C : ℕ) (c : BooleanCircuit n) (hc : c.size≤bound)
    (h : Fits C (boundedCircuitFieldLimit n bound) (canonicalBoundedCircuitDescription bound c).length bound) :
    ∃ r,run measured (2*budget C c+2) (measuredInput C bound c)=some r ∧
      r.steps≤2*budget C c+2 ∧ (∀ i,r.final.heads i=0) ∧
      r.final.tapes 27=body c ∧ r.final.tapes 29=List.replicate c.size true ∧
      r.final.tapes 30=List.replicate (body c).length true ∧
      r.final.tapes 0=ZeroPadding.pad C (frame (canonicalBoundedCircuitDescription bound c)) := by
  obtain ⟨base,hr,hs,ht,hh,hcount,_hcountH,hsource⟩:=traverse_run C c hc h
  obtain ⟨r,rr,rt,rl,rh,rs⟩:=AppendOutputLength.length_run Traversal.machine 27 forward _ _ base hr
  have hf : 2*base.steps+2≤2*budget C c+2:=by omega
  have more:=runFrom_moreFuel measured _ (2*budget C c+2-(2*base.steps+2)) _ r rr
  rw [Nat.add_sub_of_le hf] at more
  refine ⟨r,more,by omega,rh,(rt 27).trans ht,(rt 29).trans hcount,?_,(rt 0).trans hsource⟩
  rw [hh] at rl
  exact rl

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.CanonicalWalk
