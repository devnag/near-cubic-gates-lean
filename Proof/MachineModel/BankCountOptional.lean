import Proof.MachineModel.BankCountBranch

/-! Every original raw polynomial, including the empty polynomial, executes
without a supplied row count or either last-index field. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def optionalBudget (B C Q w : ℕ) (ms : List (List ℕ)):=
  max (positiveBudget B C Q w ms) (BankZero.budget B C)+2

theorem optional_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (ms : List (List (Fin gs.length))) (p F Q w : ℕ) (out pre tail : List Bool)
    (hw : ms.length < 2^w) (hQ : 1 ≤ Q) (hQp : Q ≤ p)
    (hp : RowTupleFixedCapacity.width gs Q ≤ p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
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
    ∃ result,runFrom optional (optionalBudget gs.length C Q w (rawIndices ms))
      ⟨optional.start,H,A⟩=some result ∧
      result.steps≤optionalBudget gs.length C Q w (rawIndices ms) ∧
      (∀ i,result.final.heads (old i)=CloseoutRowsBankClear.zeroHeads word i) ∧
      (∀ i,result.final.tapes (old i)=CloseoutRowsBankClear.blank C word i) ∧
      result.final.heads 113=pre.length+(stream (rawIndices ms)).length ∧
      result.final.tapes 113=A 113 ∧ result.final.heads 115=0 ∧
      result.final.tapes 115=List.replicate C false:=by
  dsimp only
  let C:=CloseoutRowsPreparationBounds.capacity (l+r) p F w gs.length Q
  have marker : readTapeBit (A 113) (H 113)=decide (0 < ms.length):=by
    have ha : A 113=pre++stream (rawIndices ms)++tail:=hrA 0
    have hh : H 113=pre.length:=hrH 0
    rw [ha,hh,BankBranch.stream_marker]
    simp only [rawIndices,List.length_map]
  by_cases empty : ms=[]
  · subst ms
    have hB : gs.length ≤ C:=by
      have hs:=CloseoutRowsPreparationInput.small_fits (l+r) p F w gs.length Q
      unfold CloseoutRowsPreparationBounds.scale at hs
      dsimp only [C];omega
    have hsize : ∀ i,i≠31 → i≠105 → (A (old i)).length ≤ C:=by
      intro i hi hlog
      by_cases h36 : i=36
      · subst i
        have ha : A (old 36)=ZeroPadding.pad C []:=hrA 3
        rw [ha];simp [ZeroPadding.pad]
      by_cases h52 : i=52
      · subst i
        have ha : A (old 52)=ZeroPadding.pad C []:=hcA 11
        rw [ha];simp [ZeroPadding.pad]
      by_cases h107 : i=107
      · subst i
        have ha : A (old 107)=List.replicate C false:=hcA 15
        rw [ha,List.length_replicate]
      rw [hbase i h36 h52 h107]
      exact BankOptional.entry_size gs p F Q w [] out (by simp) (by simp) hF i hi hlog
    obtain ⟨base,hb,_bs,bh,bt,bp,ba,bch,bct⟩:=zero_run gs.length C hB out pre tail H A hrH hrA hheads hsize
      ((hbase 31 (by decide) (by decide) (by decide)).trans (BankOptional.entry_out gs p F Q w C [] out))
      ((hbase 104 (by decide) (by decide) (by decide)).trans (BankFields.driver gs p F Q w C [] out))
      ((hbase 105 (by decide) (by decide) (by decide)).trans (BankFields.log gs p F Q w C [] out))
    obtain ⟨z,hz,zs,zh,zt⟩:=dispatch_run positive zero 2 (Or.inr rfl) _ H A base (by rw [marker];rfl) hb
    have bound : BankZero.budget gs.length C+2 ≤ optionalBudget gs.length C Q w (rawIndices (B:=gs.length) []):=
      Nat.add_le_add_right (Nat.le_max_right _ _) 2
    have more:=runFrom_moreFuel optional _ (optionalBudget gs.length C Q w (rawIndices (B:=gs.length) [])-(BankZero.budget gs.length C+2)) _ z hz
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨z,more,zs.trans bound,?_,?_,?_,?_,?_,?_⟩
    all_goals simp only [zh,zt,rawRows,rawIndices,List.map_nil,CloseoutRowsPacketOptional.cuts_nil,
      List.flatMap_nil,List.append_nil,stream_nil,List.length_singleton]
    · exact bh
    · exact bt
    · exact bp
    · exact ba
    · exact bch
    · exact bct
  · obtain ⟨base,hb,_bs,bh,bt,bp,ba,bch,bct⟩:=positive_run gs ms p F Q w out pre tail
      (List.length_pos_iff.mpr empty) hw hQ hQp hp hF H A hheads hbase hcH hcA hrH hrA
    obtain ⟨z,hz,zs,zh,zt⟩:=dispatch_run positive zero 1 (Or.inl rfl) _ H A base
      (by rw [marker,if_pos (by simpa using List.length_pos_iff.mpr empty)]) hb
    have bound : positiveBudget gs.length C Q w (rawIndices ms)+2 ≤ optionalBudget gs.length C Q w (rawIndices ms):=
      Nat.add_le_add_right (Nat.le_max_left _ _) 2
    have more:=runFrom_moreFuel optional _ (optionalBudget gs.length C Q w (rawIndices ms)-(positiveBudget gs.length C Q w (rawIndices ms)+2)) _ z hz
    rw [Nat.add_sub_of_le bound] at more
    exact ⟨z,more,zs.trans bound,by rw [zh];exact bh,by rw [zt];exact bt,
      by rw [zh];exact bp,by rw [zt];exact ba,by rw [zh];exact bch,by rw [zt];exact bct⟩

end NearCubicWires.ExtIncidence.BankCount
