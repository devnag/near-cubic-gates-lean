import SourceAdapters.Compile.OracleQueryEncoding
import SourceAdapters.Compile.OracleAddress
import Proof.Gates.Cells.CompK

/-!
proof of `thm:short-pcp-ours`, Step 4: select the ell actual oracle-address wires from a framed query.
Every possible prefix length is tested with the polynomial marker formula;
uniqueness of the terminated frame ensures selection of the decoded payload.
Bits above the payload length are zero, exactly matching bitsValue.testBit.
-/
namespace NearCubicGates.Adapters.Compile.OracleExecution
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

theorem framePrefix_unique {word : List Bool} {left right : ℕ}
    (hl : framePrefix left word=true) (hr : framePrefix right word=true) : left=right := by
  obtain ⟨a,p,ha,hpa⟩ := (framePrefix_parse _ _).1 hl
  obtain ⟨b,q,hb,hpb⟩ := (framePrefix_parse _ _).1 hr
  rw [hpa] at hpb
  cases hpb
  omega

theorem framePrefix_count_bound {word : List Bool} {count width : ℕ}
    (h : framePrefix count word=true) (hw : word.length ≤ width) : count<width := by
  obtain ⟨bits,padding,hb,he⟩ := framePrefix_sound _ _ h
  rw [he] at hw
  simp only [List.length_append,frame_length] at hw
  omega

theorem query_payload (bits padding : List Bool) (position : ℕ) (hp : position<bits.length) :
    (RepairOrdinary.frame bits++padding).getD (2*position+1) false=bits.getD position false := by
  rw [List.getD_append _ _ _ _ (by simp [frame_length]; omega)]
  change NearCubicWires.LocalBitMultitape.readTapeBit (RepairOrdinary.frame bits) (2*position+1)=_
  rw [NearCubicGates.Close.Cells.frame_read]
  simp [show (2*position+1)/2=position by omega]

def queryAddressExpression (width bit : ℕ) : BoolExpr (queryWordBits width) :=
  anyExpression (List.ofFn fun count : Fin width =>
    .and (queryPrefixExpression width count.val)
      (if bit<count.val then queryCellExpression width (2*bit+1) else .const false))

theorem queryAddressExpression_true (width bit : ℕ) (word : List Bool) (hw : word.length ≤ width) :
    (queryAddressExpression width bit).eval (queryWordEncoding width word)=true ↔
      ∃ count : Fin width, framePrefix count.val word=true ∧
        bit<count.val ∧ word.getD (2*bit+1) false=true := by
  simp only [queryAddressExpression,anyExpression_true,List.mem_ofFn,exists_exists_eq_and,
    BoolExpr.eval,queryPrefixExpression_eval _ _ _ hw,Bool.and_eq_true]
  apply exists_congr
  intro count
  by_cases h : bit<count.val
  · simp [h,queryCellExpression_eval _ _ _ hw]
  · simp [h,BoolExpr.eval]

theorem queryAddressExpression_eval (width bit : ℕ) (bits padding : List Bool)
    (hw : (RepairOrdinary.frame bits++padding).length ≤ width) :
    (queryAddressExpression width bit).eval
      (queryWordEncoding width (RepairOrdinary.frame bits++padding))=bits.getD bit false := by
  apply Bool.eq_iff_iff.mpr
  rw [queryAddressExpression_true _ _ _ hw]
  constructor
  · rintro ⟨count,hc,hb,hv⟩
    have he : count.val=bits.length := framePrefix_unique hc (framePrefix_append bits padding)
    have hp : bit<bits.length := by omega
    rwa [query_payload bits padding bit hp] at hv
  · intro hb
    have hp : bit<bits.length := by
      by_contra h
      have hn : bits.length ≤ bit := by omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hn] at hb
    refine ⟨⟨bits.length,framePrefix_count_bound (framePrefix_append bits padding) hw⟩,
      framePrefix_append bits padding,hp,?_⟩
    rwa [query_payload bits padding bit hp]

/-- The emitted arguments reproduce the exact source query for any oracle. -/
theorem queryAddress_oracle {ell : ℕ} (O : BitInput ell → Bool)
    (width : ℕ) (bits padding : List Bool)
    (hw : (RepairOrdinary.frame bits++padding).length ≤ width) :
    O (fun bit => (queryAddressExpression width bit.val).eval
      (queryWordEncoding width (RepairOrdinary.frame bits++padding)))=
      fixedArityOracle O (CanonicalBinary.bitsValue bits) := by
  unfold fixedArityOracle
  congr 1
  funext bit
  rw [queryAddressExpression_eval _ _ _ _ hw,NearCubicGates.Close.Succinct.testBit_bitsValue]

theorem queryAddressExpression_operations (width bit : ℕ) :
    expressionOperations (queryAddressExpression width bit) ≤ width*(4*width+9)+1 := by
  apply (anyExpression_operations _ (4*width+8) ?_).trans (by simp)
  intro e he
  obtain ⟨count,rfl⟩ := List.mem_ofFn.mp he
  have hp := queryPrefixExpression_operations width count.val
  have hc := queryCellExpression_operations width (2*bit+1)
  have hn := count.isLt
  simp only [expressionOperations]
  split
  · omega
  · change expressionOperations (queryPrefixExpression width count.val)+1+1 ≤ _
    omega

end NearCubicGates.Adapters.Compile.OracleExecution
