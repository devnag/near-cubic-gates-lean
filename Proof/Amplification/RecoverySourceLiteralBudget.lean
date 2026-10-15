import Proof.Amplification.RecoverySourceLiteralMeaning

namespace NearCubicWires.RepairSource.RecoverySourceLiteralMeaning
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def uniformBudget (Q R : Nat) := 1048576*(Q+R+1)^2

theorem equal_width_stream (words : List (List Bool)) (R : Nat) (hw : ∀ bits∈words,bits.length=R) :
    (FieldList.stream words).length=words.length*(2*R+1) := by
  induction words with
  | nil=>simp only [FieldList.stream_nil,List.length_nil,Nat.zero_mul]
  | cons bits words ih=>
    have hb:=hw bits (by simp)
    have ht : ∀ b∈words,b.length=R := fun b h=>hw b (by simp [h])
    simp only [FieldList.stream_cons,List.length_append,frame_length,hb,ih ht,List.length_cons]
    ring

theorem code_budget (negative : Bool) (words : List (List Bool)) (bits : List Bool) (Q R : Nat)
    (hQ : words.length≤Q) (hR : bits.length=R) (hw : ∀ b∈words,b.length=R) :
    RecoverySourceLiteralCode.budget negative words bits≤uniformBudget Q R := by
  have hn : negative.toNat≤1 := by cases negative <;> decide
  have hb := RecoveryProjectionRows.bits_le_value (2*words.length+negative.toNat)
  have hparse : Unary.budget (2*words.length+negative.toNat).bits≤24*(2*Q+2)^2 := by
    unfold Unary.budget
    rw [DimensionProducer.bits_value]
    calc
      24*(2*words.length+negative.toNat+1)*((2*words.length+negative.toNat).bits.length+1) ≤
          24*(2*Q+2)*(2*Q+2) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 24 (by omega)) (by omega)
      _=24*(2*Q+2)^2 := by ring
  have hp := PCPPairCold.budget_quadratic [!negative] bits
  simp only [List.length_singleton,hR] at hp
  have hs : (FieldList.stream words).length≤Q*(2*R+1) := by
    rw [equal_width_stream words R hw]
    exact Nat.mul_le_mul_right _ hQ
  have he : RecoverySourceLiteralCode.budget negative words bits ≤
      24*(2*Q+2)^2+20*Q+2+2*Q*(2*R+1)+8*R+56+1024*(R+2)^2 := by
    unfold RecoverySourceLiteralCode.budget RecoverySourceLiteralAddress.budget
      RecoverySourceLiteral.driverBudget RecoverySourceLiteral.budget Counter.budget
      RecoveryAddressFieldLookup.budget RecoveryAddressFieldLookup.rawBudget
    rw [hR]
    nlinarith
  apply he.trans
  unfold uniformBudget
  nlinarith [Nat.zero_le (Q*R)]

theorem budget_bound {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (literal : Literal (pcp.queryCount n)) :
    budget pcp x randomness literal≤uniformBudget (pcp.queryCount n) (pcp.nativeWidth n) := by
  apply code_budget
  · rw [skipped_length]
    exact (query literal).isLt.le
  · simp only [addressBits,List.length_ofFn]
  · intro bits hbits
    have hm : bits∈fields pcp x randomness := List.mem_of_mem_take hbits
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hm
    simp only [addressBits,List.length_ofFn]

theorem bounded_literal_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (literal : Literal (pcp.queryCount n)) : ∃ out,
    ClockJoin.ReadyRun RecoverySourceLiteralCode.machine (uniformBudget (pcp.queryCount n) (pcp.nativeWidth n))
      (RecoverySourceLiteralCode.input (literalCode literal).bits (FieldList.stream (fields pcp x randomness))) out ∧
      out 44=RepairOrdinary.frame (word pcp x randomness literal) ∧
      value (word pcp x randomness literal)=Encodable.encode (CanonicalRecoveryLanguage.outerProofLiteral pcp x randomness literal) := by
  obtain ⟨out,hr,hout⟩ := literal_run pcp x randomness literal
  exact ⟨out,ClockJoin.enlarge _ _ _ _ _ hr (budget_bound pcp x randomness literal),hout,word_value pcp x randomness literal⟩

end NearCubicWires.RepairSource.RecoverySourceLiteralMeaning
