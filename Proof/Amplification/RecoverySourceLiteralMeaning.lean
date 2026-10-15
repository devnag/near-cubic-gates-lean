import Proof.Amplification.RecoverySourceLiteralCode

/-! The executed literal word is exactly the original outer-proof recovery
formula's literal, on the SAME PCP's query-address table. This specializes
only input fields and values; it does not change the machine or encoding. -/
namespace NearCubicWires.RepairSource.RecoverySourceLiteralMeaning
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def query {q : Nat} : Literal q→Fin q
  | .positive j=>j
  | .negative j=>j

def addressBits {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (j : Fin (pcp.queryCount n)) :=
  List.ofFn (fun i=>(pcp.queryAddressBits x j i).eval randomness)
def fields {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) := List.ofFn (addressBits pcp x randomness)
def skipped {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (literal : Literal (pcp.queryCount n)) :=
  (fields pcp x randomness).take (query literal).val

theorem value_address {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (j : Fin (pcp.queryCount n)) :
    value (addressBits pcp x randomness j)=(pcp.queryAddress x randomness j).val := by
  let f : BitInput (pcp.nativeWidth n) := fun i=>(pcp.queryAddressBits x j i).eval randomness
  have he : (fun i : Fin (pcp.nativeWidth n)=>(value (List.ofFn f)).testBit i.val)=f :=
    funext (GeneratedAmplifier.address_bit f)
  have h:=binaryAddress_testBit (GeneratedAmplifier.address_lt f)
  rw [he] at h
  exact (congrArg Fin.val h).symm

theorem skipped_length {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (literal : Literal (pcp.queryCount n)) :
    (skipped pcp x randomness literal).length=(query literal).val := by
  simp only [skipped,fields,List.length_take,List.length_ofFn,min_eq_left (query literal).isLt.le]

private theorem stream_append (a b : List (List Bool)) :
    FieldList.stream (a++b)=FieldList.stream a++FieldList.stream b := by
  simp only [FieldList.stream,List.map_append,List.flatten_append]

theorem stream_index {q : Nat} (words : Fin q→List Bool) (j : Fin q) :
    FieldList.stream (List.ofFn words)=FieldList.stream ((List.ofFn words).take j.val)++RepairOrdinary.frame (words j)++
      FieldList.stream ((List.ofFn words).drop (j.val+1)) := by
  have ht := List.take_append_getElem (l:=List.ofFn words) (i:=j.val) (by simpa only [List.length_ofFn] using j.isLt)
  simp only [List.getElem_ofFn] at ht
  have hs : (List.ofFn words).take j.val++[words j]++(List.ofFn words).drop (j.val+1)=List.ofFn words := by
    rw [ht,List.take_append_drop]
  have h := congrArg FieldList.stream hs
  simpa only [stream_append,FieldList.stream_cons,FieldList.stream_nil,List.append_nil] using h.symm

def word {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (literal : Literal (pcp.queryCount n)) :=
  RecoverySourceLiteralCode.word (RecoverySourceLiteral.negative literal) (addressBits pcp x randomness (query literal))

theorem word_value {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (literal : Literal (pcp.queryCount n)) :
    value (word pcp x randomness literal)=Encodable.encode (outerProofLiteral pcp x randomness literal) := by
  rw [word,RecoverySourceLiteralCode.word_value,value_address]
  cases literal <;> rfl

def budget {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (literal : Literal (pcp.queryCount n)) :=
  RecoverySourceLiteralCode.budget (RecoverySourceLiteral.negative literal) (skipped pcp x randomness literal)
    (addressBits pcp x randomness (query literal))

theorem literal_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (literal : Literal (pcp.queryCount n)) : ∃ out,
    ClockJoin.ReadyRun RecoverySourceLiteralCode.machine (budget pcp x randomness literal)
      (RecoverySourceLiteralCode.input (literalCode literal).bits (FieldList.stream (fields pcp x randomness))) out ∧
      out 44=RepairOrdinary.frame (word pcp x randomness literal) := by
  have hc : 2*(skipped pcp x randomness literal).length+(RecoverySourceLiteral.negative literal).toNat=literalCode literal := by
    rw [skipped_length]
    cases literal <;> rfl
  have hs := stream_index (addressBits pcp x randomness) (query literal)
  change FieldList.stream (fields pcp x randomness)=FieldList.stream (skipped pcp x randomness literal)++
    RepairOrdinary.frame (addressBits pcp x randomness (query literal))++
      FieldList.stream ((fields pcp x randomness).drop ((query literal).val+1)) at hs
  have h := RecoverySourceLiteralCode.code_run (RecoverySourceLiteral.negative literal)
    (skipped pcp x randomness literal) (addressBits pcp x randomness (query literal))
    (FieldList.stream ((fields pcp x randomness).drop ((query literal).val+1)))
  rw [hc,←hs] at h
  exact h

end NearCubicWires.RepairSource.RecoverySourceLiteralMeaning
