import Proof.CaseAnalysis.CaseTwoWholeBlockReset
import Proof.PCP.PCPPNativeCanonicalBounds
import Proof.Circuits.PaddedRunnerBudgetClosure
import Proof.CaseAnalysis.ScheduleBounds

/-! Coarse bounds for the original Case 2 occurrence worker. The same PCPP
source bounds every actual clause and assignment index. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBudget
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open RepairSource.ProjectionNormalization PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def measure (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :=
  PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)

theorem components (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :
    let M:=measure a r
    1≤M ∧ r.arity≤M ∧ (pcppInput r).length≤3*M+3 ∧
      (a.output r).systematicBits≤M ∧ (a.output r).auxiliaryBits≤M ∧
      2^(a.output r).clauseBits≤M ∧ (a.output r).clauseBits≤M ∧
      HonestCall.sourceBudget a r≤M := by
  obtain ⟨hpos,hs,hq,hcode,hsys,haux,hcount,hcb⟩:=PCPPQueryBounds.components a r
  have hc:=PCPPQueryCachedBounds.majorant_bound a (r.circuit.size+r.arity)
  have hx : PCPPQueryBounds.scalar a (r.circuit.size+r.arity)+1≤
      (PCPPQueryBounds.scalar a (r.circuit.size+r.arity)+1)^2 := Nat.le_self_pow (by decide) _
  have hscalar : PCPPQueryBounds.scalar a (r.circuit.size+r.arity)≤ measure a r := by
    dsimp only [PCPPQueryBounds.majorant,measure] at *
    omega
  have hw:=PCPPQueryCost.width_le r.arity
  refine ⟨hpos.trans hscalar,
    hq.trans hscalar,?_,hsys.trans hscalar,haux.trans hscalar,
    hcount.trans hscalar,hcb.trans hscalar,hs.trans hscalar⟩
  simp only [pcppInput,List.length_append,DecompositionSource.natWord_length]
  omega

theorem metadata_bound (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :
    Metadata.budget r (a.output r)≤1000*(measure a r+1)^2 := by
  obtain ⟨_,hq,_,hs,ha,_,hc,_⟩:=components a r
  have bs:=PCPPQueryCost.natural_le _ _ hs
  have ba:=PCPPQueryCost.natural_le _ _ ha
  have bc:=PCPPQueryCost.natural_le _ _ hc
  unfold Metadata.budget Shape.budget Shape.rawBudget PCPPNativeNodeRead.budget
  norm_num only [PCPPQueryField.fieldCost,show natBitLength 3=2 by decide]
  nlinarith

theorem literal_bound {n M : ℕ} (left right : Literal n) (position : Bool)
    (hn : n≤2*M) : LiteralIndices.budget left right position≤20000*(M+1)^2 := by
  have hli:=PCPPQueryBounds.literal_le left
  have hri:=PCPPQueryBounds.literal_le right
  have hl : LiteralFields.index left≤2*M := by cases left <;>simp only [LiteralFields.index] <;>omega
  have hr : LiteralFields.index right≤2*M := by cases right <;>simp only [LiteralFields.index] <;>omega
  have hn0:=PCPPQueryCost.natural_le 2 (4*M+2) (by omega)
  have hnl:=PCPPQueryCost.natural_le (literalIndex left) (4*M+2) (by omega)
  have hnr:=PCPPQueryCost.natural_le (literalIndex right) (4*M+2) (by omega)
  have hbl : (LiteralFields.negative left).toNat≤1 := by cases LiteralFields.negative left <;>decide
  have hbr : (LiteralFields.negative right).toNat≤1 := by cases LiteralFields.negative right <;>decide
  have hsel : LiteralIndices.selected left right position≤2*M := by
    unfold LiteralIndices.selected
    split_ifs <;>assumption
  unfold LiteralIndices.budget LiteralFields.budget LiteralFields.splitBudget PCPPNativeNodeRead.budget
  nlinarith

theorem assignment_bound (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index : ℕ) (hi : index≤2*measure a r) :
    Assignment.budget a r u index≤1000*(measure a r+1)^2 := by
  obtain ⟨_,hq,hlen,_,_,_,_,hh⟩:=components a r
  have hmin:=Nat.min_le_right (a.output r).systematicBits index
  have hsub:=Nat.sub_le index (a.output r).systematicBits
  unfold Assignment.budget VariablePrep.budget VariablePrep.auxiliaryBudget
    SystematicBit.budget AuxiliaryBit.budget HonestCall.budget HonestInput.budget HonestInput.rawBudget
    PCPPQueryCachedBounds.callBudget
  simp only [List.length_append,List.length_ofFn]
  change _≤1000*(measure a r+1)^2
  change _≤ measure a r at hh
  change _≤_ at hlen
  simp only [show PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)=measure a r from rfl]
  nlinarith

theorem bit_bound (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index : Fin (2^(a.output r).clauseBits)) (position : Bool) :
    OccurrenceBit.budget a r u index position≤30000*(measure a r+1)^2 := by
  obtain ⟨_,_,_,hs,ha,_,_,_⟩:=components a r
  have hl:=literal_bound ((a.output r).clauses index).left
    ((a.output r).clauses index).right position (by omega :
      (a.output r).systematicBits+(a.output r).auxiliaryBits≤2*measure a r)
  have hi : (OccurrenceBit.named a r index position).val≤2*measure a r := by
    have h:=(OccurrenceBit.named a r index position).isLt
    omega
  have hb:=assignment_bound a r u _ hi
  unfold OccurrenceBit.budget ClauseVariable.budget PCPPQueryCachedBounds.callBudget
  simp only [show PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)=measure a r from rfl]
  nlinarith

def widthEnvelope (D M : ℕ) :=
  2*M+6+DimensionPolynomial.coefficient D 1*(M+3)^(2*D+2)+
    128*((M+2)^D+1)^2+1+80*((D+1)*(M+1)+2)^2

theorem width_bound (D q M : ℕ) (hq : q≤M) :
    CloseoutSchedule.Width.budget D 1 q≤widthEnvelope D M := by
  have hp:=DimensionPolynomial.budget_bound D 1 (q+1)
  have hp':=hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : q+1+2≤M+3) _))
  have hc:=CloseoutSchedule.Clog.budget_bound ((q+2)^D)
  have hc':=hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.pow_le_pow_left (by omega : q+2≤M+2) D) 1) 2))
  have hw:=CloseoutLanguage.clause_linear D q
  have hs:=CloseoutSchedule.Scale.budget_bound 1 (q+1) (CloseoutLanguage.clauseWidth D q)
  have hbase : q+1+CloseoutLanguage.clauseWidth D q+2≤(D+1)*(M+1)+2 := by
    have hm:=Nat.mul_le_mul_left D (Nat.add_le_add_right hq 1)
    nlinarith
  have hs':=hs.trans (Nat.mul_le_mul_left 80 (Nat.pow_le_pow_left hbase 2))
  unfold CloseoutSchedule.Width.budget CloseoutSchedule.Clause.budget widthEnvelope
  omega

def localEnvelope (D copies M : ℕ) :=
  widthEnvelope D M+100000*(copies+1)*((D+1)*(M+1)+3)^2

theorem address_bound (D copies block : ℕ) (a : PointwisePCPPAlgorithm)
    (r : PCPPRequest a.minimumArity) (padding index : ℕ) (hb : block≤copies)
    (hi : index≤ measure a r)
    (hpad : (a.output r).clauseBits+padding=CloseoutLanguage.clauseWidth D r.arity) :
    OccurrenceAddress.budget D block a r padding index≤
      widthEnvelope D (measure a r)+50000*(copies+1)*((D+1)*(measure a r+1)+3)^2 := by
  let M:=measure a r
  let S:=(D+1)*(M+1)+2
  obtain ⟨_,hq,_,_,_,_,hc,_⟩:=components a r
  have hm : M≤S := by dsimp [S];nlinarith
  have hwidth:=CloseoutLanguage.clause_linear D r.arity
  have hmul:=Nat.mul_le_mul_left D (Nat.add_le_add_right hq 1)
  have hpos : r.arity+CloseoutLanguage.clauseWidth D r.arity+2≤S := by dsimp [S,M];nlinarith
  have hpadding : padding≤S := by omega
  have hmeta:=metadata_bound a r
  have hmeta':=hmeta.trans (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left
    (Nat.add_le_add_right hm 1) 2))
  have hw:=width_bound D r.arity M hq
  have hp:=DimensionPower.cost_bound 1 block (r.arity+CloseoutLanguage.clauseWidth D r.arity+1) 1 le_rfl
  have hp' : DimensionPower.cost block (r.arity+CloseoutLanguage.clauseWidth D r.arity+1) 1≤
      2*copies+2+6*copies*S^2+7 := by
    have hm':=Nat.mul_le_mul hb (Nat.pow_le_pow_left hpos 2)
    norm_num only [Nat.one_mul,show 1+1=2 by decide] at hp
    nlinarith
  have hmidx:=Nat.mul_le_mul hi hc
  have hqS : r.arity≤S := hq.trans hm
  have hcS : (a.output r).clauseBits≤S := hc.trans hm
  have hiS : index≤S := hi.trans hm
  have hprod:=Nat.mul_le_mul hiS hcS
  have hblock:=Nat.mul_le_mul hb (by omega : r.arity+CloseoutLanguage.clauseWidth D r.arity+1≤S)
  have hS1 : 1≤S := by dsimp [S];omega
  have hSS : S≤S^2 := Nat.le_self_pow (by decide) _
  have hcc : copies≤copies*S^2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left copies (Nat.one_le_pow 2 S hS1)
  change _≤widthEnvelope D M+50000*(copies+1)*(S+1)^2
  unfold OccurrenceAddress.budget Widths.budget BlockScalars.budget AddressFields.budget
    BinaryField.budget SliceFrame.budget MatrixUnaryTemplate.budget
  nlinarith

theorem occurrence_bound (D copies block : ℕ) (a : PointwisePCPPAlgorithm)
    (r : PCPPRequest a.minimumArity) (u : BitInput r.arity)
    (clause : BitInput (a.output r).clauseBits) (position : Bool) (padding : ℕ)
    (hb : block≤copies)
    (hpad : (a.output r).clauseBits+padding=CloseoutLanguage.clauseWidth D r.arity) :
    Occurrence.budget D block a r u clause position padding≤localEnvelope D copies (measure a r) := by
  have hi : (binaryAddress clause).val≤ measure a r :=
    (binaryAddress clause).isLt.le.trans (components a r).2.2.2.2.2.1
  have ha:=address_bound D copies block a r padding _ hb hi hpad
  have hbit:=bit_bound a r u (binaryAddress clause) position
  have hbase : measure a r+1≤(D+1)*(measure a r+1)+3 := by nlinarith
  have hscaled:=Nat.mul_le_mul_left 30000 (Nat.pow_le_pow_left hbase 2)
  have hpos : 1≤((D+1)*(measure a r+1)+3)^2 := Nat.one_le_pow _ _ (by omega)
  unfold Occurrence.budget localEnvelope
  nlinarith

theorem local_polynomial (D copies : ℕ) {f : ℕ→ℕ} (hf : SourcePoly f) :
    SourcePoly (fun n=>localEnvelope D copies (f n)) := by
  have hc (n : ℕ):=polyDominated_const (measureOf:=(fun n : ℕ=>n)) n
  have h1:=hf.add (hc 1)
  have h2:=hf.add (hc 2)
  have h3:=hf.add (hc 3)
  have hd:=(h1.const_mul (D+1)).add (hc 2)
  have hw:=((((((hf.const_mul 2).add (hc 6)).add
    ((sourcePoly_pow h3 (2*D+2)).const_mul (DimensionPolynomial.coefficient D 1))).add
      ((sourcePoly_pow ((sourcePoly_pow h2 D).add (hc 1)) 2).const_mul 128)).add (hc 1)).add
        ((sourcePoly_pow hd 2).const_mul 80))
  exact hw.add ((sourcePoly_pow ((h1.const_mul (D+1)).add (hc 3)) 2).const_mul (100000*(copies+1)))

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBudget
