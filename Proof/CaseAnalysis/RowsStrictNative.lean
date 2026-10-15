import Proof.CaseAnalysis.RowsStrictThreshold
import Proof.CaseAnalysis.RowsSignedAppend

/-! Complete physical strict-threshold field: select the actual signed
arithmetic branch and append precisely intWord (theta-1). The original
checked decoder's sign and canonical magnitude are the only semantic seam. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsStrictNative
open LocalBitMultitape RadixSemantics CloseoutWitness CloseoutRowsStrictSelector CloseoutRowsStrictThreshold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem magnitude_length (source : List Bool) (n : ℕ) :
    (magnitude source n).bits.length≤n.bits.length+1 := by
  unfold magnitude
  split_ifs with h hn
  · rw [←RecoveryPrefixCounter.next_bits]
    exact (ClockIncrement.next_length n.bits).2
  · subst n
    decide
  · have hv := value_lt n.bits
    rw [CanonicalPositiveOutput.nat_bits_value] at hv
    exact (CanonicalPositiveOutput.nat_bits_length_le n.bits.length (n-1) (by omega)).trans (by omega)

theorem magnitude_eq (source : List Bool) (z : ℤ) (hs : negative source=decide (z<0)) :
    magnitude source z.natAbs=(z-1).natAbs := by
  cases z with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast,Int.natAbs_natCast] at hs ⊢
    have hn : ¬(n : ℤ)<0 := by omega
    have hneg : negative source=false := by simpa only [hn,decide_false] using hs
    cases n with
    | zero => simp [magnitude,hneg]
    | succ n =>
      have he : ((n+1 : ℕ) : ℤ)-1=(n : ℤ) := by omega
      rw [he]
      simp [magnitude,hneg]
  | negSucc n =>
    have hneg : negative source=true := by simpa using hs
    have he : Int.negSucc n-1=Int.negSucc (n+1) := by omega
    rw [he]
    simp [magnitude,hneg]

theorem sign_eq (source : List Bool) (z : ℤ) (hs : negative source=decide (z<0)) :
    resultSign source z.natAbs.bits=decide (z-1<0) := by
  cases z with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast,Int.natAbs_natCast] at hs ⊢
    have hn : ¬(n : ℤ)<0 := by omega
    have hneg : negative source=false := by simpa only [hn,decide_false] using hs
    cases n with
    | zero => simp [resultSign,hneg]
    | succ n =>
      have he : ((n+1 : ℕ) : ℤ)-1=(n : ℤ) := by omega
      simp only [he]
      have hn' : ¬(n : ℤ)<0 := by omega
      simp [resultSign,hneg,bits_nonempty (n+1) (by omega),hn']
  | negSucc n =>
    have hneg : negative source=true := by simpa using hs
    simp [resultSign,hneg]

def slots : Fin 4 → Fin 15 := ![11,4,13,14]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def fields := TapeEmbedding.machine 2 CloseoutRowsStrictThreshold.machine
noncomputable def append := RecoveryFocus.machine slots CloseoutRowsSignedAppend.machine
noncomputable def machine := Composition.machine fields append
def extraHeads (out : List Bool) : Fin 2 → ℕ := ![0,out.length]
def extraTapes (old out : List Bool) : Fin 2 → List Bool := ![old,out]
noncomputable def entry (source : List Bool) (n : ℕ) (old out : List Bool) :=
  Composition.leftConfig 7 (TapeEmbedding.config (extraHeads out) (extraTapes old out)
    (initialConfiguration CloseoutRowsStrictThreshold.machine (input source n.bits)))
def produced (source : List Bool) (n : ℕ) :=
  resultSign source n.bits :: RepairRepresentation.natWord (magnitude source n)
def budget (n : ℕ) := 26*n.bits.length+69

theorem native_run (source : List Bool) (n : ℕ) (old out : List Bool) : ∃ result,
    runFrom machine (budget n) (entry source n old out)=some result ∧
      result.steps≤budget n ∧ result.final.tapes 14=out++produced source n ∧
      result.final.heads 14=(out++produced source n).length := by
  obtain ⟨bank,⟨first,hf,ft,fh,fs⟩,word,sign⟩ := threshold_run source n
  let a := TapeEmbedding.receipt (extraHeads out) (extraTapes old out) first
  have ha := TapeEmbedding.run_embed CloseoutRowsStrictThreshold.machine (extraHeads out) (extraTapes old out)
    _ _ first hf
  let bits := (magnitude source n).bits
  let signSource := prepared source n.bits 11
  have hw : NativeWord.word bits=RepairRepresentation.natWord (magnitude source n) := by
    rw [NativeWord.word_eq _ (CanonicalBinary.Nat.bits_canonical _),CanonicalPositiveOutput.nat_bits_value]
  obtain ⟨raw,hr,rs,rt,rh,_,_⟩ := CloseoutRowsSignedAppend.append_run signSource bits old out
  obtain ⟨b,hb,_,bs,bh,bt,_⟩ := RecoveryFocus.dock slots slots_injective CloseoutRowsSignedAppend.machine
    _ a.final.heads a.final.tapes (CloseoutRowsSignedAppend.entry signSource bits old out)
    (by
      intro i;fin_cases i
      · exact (TapeEmbedding.receipt_heads_old _ _ first 11).trans (fh 11)
      · exact (TapeEmbedding.receipt_heads_old _ _ first 4).trans (fh 4)
      · exact TapeEmbedding.receipt_heads_new _ _ first 0
      · exact TapeEmbedding.receipt_heads_new _ _ first 1)
    (by
      intro i;fin_cases i
      · exact (TapeEmbedding.receipt_tapes_old _ _ first 11).trans ((congrFun ft 11).trans sign)
      · exact (TapeEmbedding.receipt_tapes_old _ _ first 4).trans (((congrFun ft 4).trans word).trans hw.symm)
      · exact TapeEmbedding.receipt_tapes_new _ _ first 0
      · exact TapeEmbedding.receipt_tapes_new _ _ first 1) raw hr
  have h := Composition.run_join fields append _ _ _ a b ha hb
  have ht : CloseoutRowsStrictThreshold.budget n.bits+1+(2*bits.length+8)≤budget n := by
    have hl := magnitude_length source n
    unfold CloseoutRowsStrictThreshold.budget budget
    dsimp only [bits]
    omega
  have more := runFrom_moreFuel machine _
    (budget n-(CloseoutRowsStrictThreshold.budget n.bits+1+(2*bits.length+8)))
    (entry source n old out) (Composition.joinedReceipt a b) h
  rw [Nat.add_sub_of_le ht] at more
  have hem : CloseoutRowsSignedAppend.appended signSource bits out=out++produced source n := by
    simp only [CloseoutRowsSignedAppend.appended,CloseoutRowsSignedAppend.signed,hw,produced]
    rw [List.append_assoc]
    rfl
  refine ⟨_,more,?_,?_,?_⟩
  · change a.steps+1+b.steps≤_
    rw [bs]
    change first.steps+1+raw.steps≤_
    omega
  · change b.final.tapes (slots 3)=_
    rw [bt,rt,hem]
  · change b.final.heads (slots 3)=_
    rw [bh,rh,hem]

theorem produced_eq (source : List Bool) (z : ℤ) (hs : negative source=decide (z<0)) :
    produced source z.natAbs=RepairRepresentation.intWord (z-1) := by
  rw [produced,sign_eq source z hs,magnitude_eq source z hs]
  rfl

theorem strict_native_run (source : List Bool) (z : ℤ) (old out : List Bool)
    (hs : negative source=decide (z<0)) : ∃ result,
    runFrom machine (budget z.natAbs) (entry source z.natAbs old out)=some result ∧
      result.steps≤budget z.natAbs ∧ result.final.tapes 14=out++RepairRepresentation.intWord (z-1) ∧
      result.final.heads 14=(out++RepairRepresentation.intWord (z-1)).length := by
  simpa only [produced_eq source z hs] using native_run source z.natAbs old out

end NearCubicWires.RepairOrdinary.CloseoutRowsStrictNative
