import Proof.MachineModel.BankBranch
import Proof.CaseAnalysis.RowsPacketOptional

/-! One actual raw stream runs through the positive or empty bank entry.
The caller supplies the existing native ports; no separate marker, count pass
or serialized polynomial packet is required. -/
namespace NearCubicWires.ExtIncidence.BankOptional
open LocalBitMultitape RepairOrdinary BankConsumer
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def budget (B C Q : ℕ) (ms : List (List ℕ)):=
  max (BankConsumer.budget B C Q ms) (BankZero.budget B C)+2

theorem entry_size {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w : ℕ)
    (rows : List (List Bool)) (out : List Bool)
    (hl:∀ row∈rows,row.length=gs.length) (hw:rows.length ≤ 2^w)
    (hF:RowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 113) (hi:i≠31) (hlog:i≠105) :
    let C:=CloseoutRowsPreparationBounds.capacity n p F w gs.length Q
    ((CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes i).length ≤ C:=by
  dsimp only
  change (ZeroPadding.pad (CloseoutRowsBankCapacity.capacities _ i)
    ((CloseoutRowsPolynomial.input gs p F Q w _ rows out).tapes i)).length ≤ _
  rw [ZeroPadding.pad_length]
  refine max_le (by simp [CloseoutRowsBankCapacity.capacities,hi,hlog]) ?_
  exact CloseoutRowsBankCapacity.loop_bound _ gs 0 p F Q w 0 rows out hl hw (Nat.zero_le _) hF i hi hlog

theorem entry_out {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 31=out:=by
  change ZeroPadding.pad 0 (CloseoutRowsLoopLayout.inputTapes gs p F w 0 C rows out 31)=out
  rw [ZeroPadding.pad_zero]
  exact (CloseoutRowsPolynomial.output_fields gs p F w 0 C rows out).1

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (ms : List (List (Fin gs.length))) (p F Q w : ℕ) (out pre tail : List Bool)
    (hw:ms.length < 2^w) (hQp:Q ≤ p)
    (hp:RowTupleFixedCapacity.width gs Q ≤ p)
    (hF:RowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (H : Fin 116→ℕ) (A : Fin 116→List Bool)
    (hheads:∀ i,H (old i)=CloseoutRowsBankFields.heads out i)
    (hother:∀ i,i≠36 → A (old i)=
      (CloseoutRowsBankPolynomial.entry gs p F Q w
        (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) (rawRows ms) out).tapes i)
    (hext:H 113=pre.length ∧ H 114=0 ∧ H 115=0)
    (hsource:A 113=pre++stream (rawIndices ms)++tail)
    (hblank:A 36=List.replicate (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false)
    (hscratch:A 114=List.replicate (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false)
    (hcount:A 115=List.replicate (CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q) false) :
    let C:=CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
    let word:=out++(CloseoutRowsSharedDigits.cuts gs Q w (rawRows ms)).flatMap (MatrixScoreBatch.cutWord p)
    ∃ result,runFrom BankBranch.machine (budget gs.length C Q (rawIndices ms))
      ⟨BankBranch.machine.start,H,A⟩=some result ∧
      result.steps ≤ budget gs.length C Q (rawIndices ms) ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      result.final.heads 113=pre.length+(stream (rawIndices ms)).length ∧
      result.final.tapes 113=A 113 ∧ result.final.heads 115=0 ∧
      result.final.tapes 115=ZeroPadding.pad C (List.replicate ms.length true):=by
  dsimp only
  let C:=CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  have marker:readTapeBit (A 113) (H 113)=decide (0 < ms.length):=by
    rw [hsource,hext.1,BankBranch.stream_marker]
    simp only [rawIndices,List.length_map]
  by_cases hempty:ms=[]
  · subst ms
    have hB:gs.length ≤ C:=by
      have h:=CloseoutRowsPreparationInput.small_fits (l+r) p F w gs.length Q
      unfold CloseoutRowsPreparationBounds.scale at h
      dsimp only [C];omega
    have hh:∀ j,H (BankExecution.slots j)=Padded.heads pre.length 0 0 j:=by
      intro j;fin_cases j
      · exact hext.1
      · exact hheads 38
      · exact hext.2.1
      · exact hheads 36
      · exact hext.2.2
    have ht:∀ j,A (BankExecution.slots j)=Padded.tapes C gs.length (pre++[false]++tail) [] 0 j:=by
      intro j;fin_cases j
      · exact hsource
      · exact (hother 38 (by decide)).trans (BankFields.template gs p F Q w C [] out)
      · exact hscratch
      · change A 36=ZeroPadding.pad C []
        simpa only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append] using hblank
      · change A 115=ZeroPadding.pad C (List.replicate 0 true)
        simpa only [List.replicate_zero,ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append] using hcount
    have hsize:∀ i,i≠31 → i≠105 → (A (old i)).length ≤ C:=by
      intro i hi hlog
      by_cases h36:i=36
      · subst i;rw [show old 36=(36 : Fin 116) from rfl,hblank,List.length_replicate]
      · rw [hother i h36]
        exact entry_size gs p F Q w [] out (by simp) (by simp) hF i hi hlog
    obtain ⟨base,hbase,_,bh,bt,bs,ba,bch,bct⟩:=BankZero.zero_run gs.length C hB out pre tail H A hh ht
      hheads hsize ((hother 31 (by decide)).trans (entry_out gs p F Q w C [] out))
      ((hother 104 (by decide)).trans (BankFields.driver gs p F Q w C [] out))
      ((hother 105 (by decide)).trans (BankFields.log gs p F Q w C [] out))
    obtain ⟨z,hz,zs,zh,zt⟩:=BankBranch.dispatch_run BankConsumer.machine BankZero.machine 2 (Or.inr rfl)
      _ H A base (by rw [marker];rfl) hbase
    have hb:BankZero.budget gs.length C+2 ≤ budget gs.length C Q (rawIndices (B:=gs.length) []):=
      Nat.add_le_add_right (Nat.le_max_right _ _) 2
    have more:=runFrom_moreFuel BankBranch.machine _
      (budget gs.length C Q (rawIndices (B:=gs.length) [])-(BankZero.budget gs.length C+2)) _ z hz
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨z,more,zs.trans hb,?_,?_,?_,?_,?_,?_⟩
    all_goals simp only [zh,zt,rawRows,rawIndices,List.map_nil,CloseoutRowsPacketOptional.cuts_nil,
      List.flatMap_nil,List.append_nil,stream_nil,List.length_singleton,List.length_nil,
      List.replicate_zero,ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
    · exact bh
    · exact bt
    · exact bs
    · exact ba
    · exact bch
    · exact bct
  · obtain ⟨base,hbase,_,bh,bt,bs,ba,bch,bct⟩:=BankConsumer.polynomial_run gs ms p F Q w out pre tail
      (List.length_pos_iff.mpr hempty) hw hQp hp hF H A hheads hother hext hsource hblank hscratch hcount
    obtain ⟨z,hz,zs,zh,zt⟩:=BankBranch.dispatch_run BankConsumer.machine BankZero.machine 1 (Or.inl rfl)
      _ H A base (by rw [marker,if_pos (by simpa using List.length_pos_iff.mpr hempty)]) hbase
    have hb:BankConsumer.budget gs.length C Q (rawIndices ms)+2 ≤ budget gs.length C Q (rawIndices ms):=
      Nat.add_le_add_right (Nat.le_max_left _ _) 2
    have more:=runFrom_moreFuel BankBranch.machine _
      (budget gs.length C Q (rawIndices ms)-(BankConsumer.budget gs.length C Q (rawIndices ms)+2)) _ z hz
    rw [Nat.add_sub_of_le hb] at more
    exact ⟨z,more,zs.trans hb,by rw [zh];exact bh,by rw [zt];exact bt,
      by rw [zh];exact bs,by rw [zt];exact ba,by rw [zh];exact bch,by rw [zt];exact bct⟩

end
end NearCubicWires.ExtIncidence.BankOptional
