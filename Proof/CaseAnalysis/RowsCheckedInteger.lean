import Proof.CaseAnalysis.RowsIntegerGuard

/-! One actual checked signed-integer producer for the row source and
witness coefficients. Its exact canonical verdict and native intWord share
the same raw input, sign, magnitude, and executed binary copier. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCheckedInteger
open LocalBitMultitape RadixSemantics CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4→Fin 214:=![17,200,212,213]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def fields:=TapeEmbedding.machine 2 CloseoutRowsIntegerGuard.machine
noncomputable def append:=RecoveryFocus.machine slots CloseoutRowsSignedAppend.machine
noncomputable def machine:=Composition.machine fields append
def extraHeads (out : List Bool) : Fin 2→ℕ:=![0,out.length]
def extraTapes (old out : List Bool) : Fin 2→List Bool:=![old,out]
noncomputable def entry (bits old out : List Bool):=
  Composition.leftConfig 7 (TapeEmbedding.config (extraHeads out) (extraTapes old out)
    (initialConfiguration CloseoutRowsIntegerGuard.machine (CloseoutRowsIntegerGuard.input bits)))
def payload (bits : List Bool):=BitFields.payload (RecoveryFixedUnpair.rightWord bits)
def produced (bits : List Bool):=
  readTapeBit (frame (RecoveryFixedUnpair.leftWord bits)) 1::NativeWord.word (payload bits)
def budget (bits : List Bool):=CloseoutRowsIntegerGuard.budget bits+2*bits.length+11

theorem payload_bound (bits : List Bool) : (payload bits).length ≤ bits.length+1:=by
  have h:=Reencode.count_bound (RecoveryFixedUnpair.rightWord bits)
  simpa only [payload,BitFields.payload,Reencode.fields,List.length_map,
    TraversalCounted.count,(RecoveryFixedUnpair.word_lengths bits).2] using h

theorem native_run (bits old out : List Bool) : ∃ result,
    runFrom machine (budget bits) (entry bits old out)=some result ∧
      result.steps ≤ budget bits ∧
      result.final.tapes 213=out++produced bits ∧
      result.final.heads 213=(out++produced bits).length ∧
      result.final.tapes 17=frame (RecoveryFixedUnpair.leftWord bits) ∧
      result.final.tapes 194=frame (payload bits) ∧
      (readTapeBit (result.final.tapes 211) 0=true ↔
        (CanonicalBinary.decodeInt (value bits)).isSome) ∧
      (∀ z,CanonicalBinary.decodeInt (value bits)=some z →
        result.final.tapes 213=out++RepairRepresentation.intWord z):=by
  obtain ⟨bank,⟨first,hf,ft,fh,fs⟩,flag,sign,mag,word,typed⟩:=CloseoutRowsIntegerGuard.guard_run bits
  let a:=TapeEmbedding.receipt (extraHeads out) (extraTapes old out) first
  have ha:=TapeEmbedding.run_embed CloseoutRowsIntegerGuard.machine (extraHeads out) (extraTapes old out)
    _ _ first hf
  obtain ⟨raw,hr,rs,rt,rh,rsg,_⟩:=CloseoutRowsSignedAppend.append_run
    (frame (RecoveryFixedUnpair.leftWord bits)) (payload bits) old out
  obtain ⟨b,hb,_,bs,bh,bt,bkeep⟩:=RecoveryFocus.dock slots slots_injective CloseoutRowsSignedAppend.machine
    _ a.final.heads a.final.tapes
    (CloseoutRowsSignedAppend.entry (frame (RecoveryFixedUnpair.leftWord bits)) (payload bits) old out)
    (by
      intro i;fin_cases i
      · exact (TapeEmbedding.receipt_heads_old _ _ first 17).trans (fh 17)
      · exact (TapeEmbedding.receipt_heads_old _ _ first 200).trans (fh 200)
      · exact TapeEmbedding.receipt_heads_new _ _ first 0
      · exact TapeEmbedding.receipt_heads_new _ _ first 1)
    (by
      intro i;fin_cases i
      · exact (TapeEmbedding.receipt_tapes_old _ _ first 17).trans ((congrFun ft 17).trans sign)
      · exact (TapeEmbedding.receipt_tapes_old _ _ first 200).trans ((congrFun ft 200).trans word)
      · exact TapeEmbedding.receipt_tapes_new _ _ first 0
      · exact TapeEmbedding.receipt_tapes_new _ _ first 1) raw hr
  have h:=Composition.run_join fields append _ _ _ a b ha hb
  have ht:CloseoutRowsIntegerGuard.budget bits+1+(2*(payload bits).length+8) ≤ budget bits:=by
    have hp:=payload_bound bits
    unfold budget;omega
  have more:=runFrom_moreFuel machine _
    (budget bits-(CloseoutRowsIntegerGuard.budget bits+1+(2*(payload bits).length+8)))
    (entry bits old out) (Composition.joinedReceipt a b) h
  rw [Nat.add_sub_of_le ht] at more
  have emitted:b.final.tapes 213=out++produced bits:=by
    change b.final.tapes (slots 3)=_
    rw [bt,rt]
    simp only [CloseoutRowsSignedAppend.appended,CloseoutRowsSignedAppend.signed,produced,
      List.append_assoc,List.cons_append,List.nil_append]
  have kept (i : Fin 212) (hi : ∀ j,slots j≠i.castAdd 2) :
      b.final.tapes (i.castAdd 2)=bank i:=
    (bkeep _ hi).2.trans ((TapeEmbedding.receipt_tapes_old _ _ first i).trans (congrFun ft i))
  refine ⟨_,more,?_,emitted,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    rw [bs]
    change first.steps+1+raw.steps ≤ _
    omega
  · change b.final.heads (slots 3)=_
    rw [bh,rh]
    exact congrArg List.length (by
      simp only [CloseoutRowsSignedAppend.appended,CloseoutRowsSignedAppend.signed,produced,
        List.append_assoc,List.cons_append,List.nil_append])
  · change b.final.tapes (slots 0)=_
    rw [bt]
    exact rsg
  · exact (kept 194 (by decide)).trans mag
  · change readTapeBit (b.final.tapes ((211 : Fin 212).castAdd 2)) 0=true ↔ _
    rw [kept 211 (by decide)]
    exact flag
  · intro z hz
    change b.final.tapes 213=out++RepairRepresentation.intWord z
    rw [emitted]
    have hw:NativeWord.word (payload bits)=RepairRepresentation.natWord z.natAbs:=word.symm.trans (typed z hz)
    rw [produced,CloseoutRowsSignedAppend.sign_of_decode bits z hz,hw]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsCheckedInteger
