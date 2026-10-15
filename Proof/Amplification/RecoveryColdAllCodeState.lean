import Proof.Amplification.RecoveryCompactWhole

/-! Exact all-code checker state supplied by the cold producer. The
natural input uses its canonical bits, so the physically counted input
width is exactly the semantic all-code bound. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdAllCode
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def state (bits word innerBits outerBits : List Bool) (count n m : Nat) : RecoveryAllCode.State :=
  ⟨⟨view bits word (2*(count*(width bits+2)+1)),RecoveryColdSAT.state bits word⟩,
    RecoveryColdMarker.state bits,
    RecoveryColdCompact.state bits word innerBits outerBits n m⟩

theorem state_width (bits word innerBits outerBits : List Bool) (count n m : Nat) :
    (state bits word innerBits outerBits count n m).width=width bits :=
  view_width bits word _

theorem state_code (code : Nat) (word innerBits outerBits : List Bool) (count n m : Nat) :
    (state code.bits word innerBits outerBits count n m).code=code :=
  (RecoveryColdHeader.code_value code.bits).trans (RecoveryUnpair.bits_value code)

theorem bound_code (code : Nat) : max 1 code.bits.length=natBitLength code := by
  have h := RecoveryColdWidthEntry.width_code code
  change max 1 code.bits.length+2=natBitLength code+2 at h
  omega

theorem prepared (code : Nat) (word innerBits outerBits : List Bool) (count n m : Nat)
    (hn : n≤limit code.bits) (hm : m≤limit code.bits)
    (hp : ∃ table rest,readList (limit code.bits) (readEntry (width code.bits)) word=some (table,rest)) :
    RecoveryAllCode.Prepared (state code.bits word innerBits outerBits count n m)
      (limit code.bits) word (count*(width code.bits+2)+1) innerBits outerBits [] [] := by
  have hw := RecoveryColdHeader.zero_length code.bits
  refine ⟨view_valid _ _ _,rfl,rfl,?_,rfl,rfl,?_,
    RecoveryColdCompact.prepared _ _ _ _ n m hn hm,?_,RecoveryColdMarker.valid _,rfl,?_,rfl,?_,?_,?_⟩
  · change RecoveryRawSAT.Inv (view code.bits word _).width (limit code.bits) 0 0 word
      (RecoveryColdSAT.state code.bits word)
    rw [view_width]
    exact RecoveryColdSAT.invariant _ _
  · change RadixSemantics.value (RecoveryColdHeader.boundWord code.bits)=
      natBitLength (state code.bits word innerBits outerBits count n m).code
    rw [RecoveryColdHeader.bound_value,state_code,bound_code]
  · change limit code.bits≤3*((RecoveryColdHeader.zeroWord code.bits).length+1)
    rw [hw]
    change 3*(max 1 code.bits.length+1)≤3*(max 1 code.bits.length+2+1)
    omega
  · rfl
  · exact (RecoveryColdMarker.initial_metadata code.bits).1.trans
      (congrArg (fun w=>frame (List.replicate w false)) hw.symm)
  · exact (RecoveryColdMarker.initial_metadata code.bits).2.trans
      (congrArg (fun w=>frame (List.replicate w false)) hw.symm)
  · change ∃ table rest,readList (limit code.bits)
      (readEntry (RecoveryColdHeader.zeroWord code.bits).length) word=some (table,rest)
    rw [hw]
    exact hp

end NearCubicWires.RepairOrdinary.RecoveryColdAllCode
