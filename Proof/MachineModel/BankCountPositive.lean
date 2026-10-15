import Proof.MachineModel.BankCountInputs

/-! One positive raw polynomial now produces its actual incidence table,
count and both binary index fields before calling the original worker. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def positive:=Composition.machine raw counted
def positiveBudget (B C Q w : ℕ) (ms : List (List ℕ)):=
  BankExecution.budget B C ms+1+budget C Q w ms.length

theorem positive_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (ms : List (List (Fin gs.length))) (p F Q w : ℕ) (out pre tail : List Bool)
    (hM : 0 < ms.length) (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (hQp : Q ≤ p)
    (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hheads : ∀ i,H (old i)=CloseoutRowsBankFields.heads out i)
    (hbase : ∀ i,i≠36 → i≠52 → i≠107 → A (old i)=
      (CloseoutRowsBankPolynomial.entry gs p F Q w
        (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) [] out).tapes i)
    (hcH : ∀ j,H (slots j)=0)
    (hcA : ∀ j,A (slots j)=CountIndexCopy.input
      (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) w 0 j)
    (hrH : ∀ j,H (rawOld (BankExecution.slots j))=Padded.heads pre.length 0 0 j)
    (hrA : ∀ j,A (rawOld (BankExecution.slots j))=Padded.tapes
      (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) gs.length
      (pre++stream (rawIndices ms)++tail) [] 0 j) :
    let C:=CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let word:=out++(CloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap (MatrixScoreBatch.cutWord p)
    ∃ result,runFrom positive (positiveBudget gs.length C Q w (rawIndices ms))
      ⟨positive.start,H,A⟩=some result ∧
      result.steps≤positiveBudget gs.length C Q w (rawIndices ms) ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      result.final.heads 113=pre.length+(stream (rawIndices ms)).length ∧
      result.final.tapes 113=A 113 ∧ result.final.heads 115=0 ∧
      result.final.tapes 115=List.replicate C false :=by
  dsimp only
  let C:=CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  let pos:=pre.length+(stream (rawIndices ms)).length
  have hB : gs.length≤C:=by
    have hs:=CloseoutRowsPreparationInput.small_fits (l+r) p F w gs.length Q
    unfold CloseoutRowsPreparationBounds.scale at hs
    dsimp only [C];omega
  have first:=raw_run ms C hB pre tail H A hrH hrA
    (BankFields.table_bound gs p F Q w ms hw.le)
    (BankConsumer.count_bound (l+r) p F w gs.length Q ms.length hw.le)
    (hheads 104) (hheads 105)
    ((hbase 104 (by decide) (by decide) (by decide)).trans (BankFields.driver gs p F Q w C [] out))
    ((hbase 105 (by decide) (by decide) (by decide)).trans (BankFields.log gs p F Q w C [] out))
  have hl : ∀ row∈rawRows ms,row.length=gs.length:=by
    intro row hr
    obtain ⟨m,_,rfl⟩:=List.mem_map.mp hr
    exact List.length_ofFn
  have hlen : (rawRows ms).length=ms.length:=by simp only [rawRows,List.length_map]
  obtain ⟨last,lastRun,_ls,lh,lt,keep⟩:=polynomial_run gs (rawRows ms) p F Q w out hl
    (by simpa only [hlen] using hM) (by simpa only [hlen] using hw) hQ hQp hp hF
    (afterHeads H pos) (afterTapes A C (rawRows ms).flatten ms.length)
    (counted_heads H pos hcH)
    (by simpa only [hlen] using counted_inputs A C w ms.length (rawRows ms).flatten hcA)
    (native_heads H pos out hheads)
    (by intro i h36 h52 h107
        exact (native_other A C ms.length (rawRows ms).flatten i h36).trans (hbase i h36 h52 h107))
    (by rw [after_tapes_eq];rfl)
  have time : (rawRows ms).length=(rawIndices ms).length:=by simp only [rawRows,rawIndices,List.length_map]
  rw [time] at lastRun
  obtain ⟨result,rr,rh,rt,rs⟩:=first.seq (Step.of_run lastRun rfl rfl)
  have outside (i : Fin 128) (hi : 113 ≤ i.val) : ∀ j,old j≠i:=by
    intro j he
    have hv : j.val=i.val:=congrArg (fun x : Fin 128=>x.val) he
    have hj:=j.isLt;omega
  refine ⟨result,rr,rs,?_,?_,?_,?_,?_,?_⟩
  · intro i;rw [rh];exact lh i
  · intro i;rw [rt];exact lt i
  · rw [rh,(keep 113 (outside 113 (by decide))).1,after_heads_eq];rfl
  · rw [rt,(keep 113 (outside 113 (by decide))).2]
    simp only [changed,Function.update_of_ne (by decide : (113 : Fin 128)≠107),
      Function.update_of_ne (by decide : (113 : Fin 128)≠52),
      Function.update_of_ne (by decide : (113 : Fin 128)≠115),after_tapes_eq,
      Function.update_of_ne (by decide : (113 : Fin 128)≠36)]
  · rw [rh,(keep 115 (outside 115 (by decide))).1,after_heads_eq];rfl
  · rw [rt,(keep 115 (outside 115 (by decide))).2];rfl

end NearCubicWires.ExtIncidence.BankCount
