import Proof.CaseAnalysis.WitnessMassPaddedCheck

/-! The sum's actual mass check uses the cleared term parser for constant
scratch and retains the same source, compact coefficient stream and Store. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumCheck
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorThresholdAmbient
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 110) : Fin 827:=⟨if i.val<94 then 725+i.val else i.val-94,by split_ifs <;> omega⟩
theorem slots_injective : Function.Injective slots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  dsimp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem native_slot (i : Fin 94) : slots (native i)=((i.castAdd 7).natAdd 725).castAdd 1:=by
  apply Fin.ext
  change (if i.val<94 then 725+i.val else _)=725+i.val
  rw [if_pos i.isLt]
theorem scratch_slot (i : Fin 16) : slots (i.natAdd 94)=(i.castAdd 709).castAdd 102:=by
  apply Fin.ext
  change (if 94+i.val<94 then _ else 94+i.val-94)=i.val
  rw [if_neg (by omega)]
  omega
def changed (terms : Fin 725→List Bool) (result : Fin 110→List Bool) (i : Fin 725):=
  if h:i.val<16 then result ⟨94+i.val,by omega⟩ else terms i
noncomputable def machine (k : ℕ) (q : ℚ):=RecoveryFocus.machine slots (MassCheck.machine k q)

theorem heads_slots (position : ℕ) (out : List Bool) (i : Fin 110) :
    TermCommit.heads position out (slots i)=0:=by
  refine Fin.addCases (m:=94) (n:=16) ?_ ?_ i
  · intro j
    change TermCommit.heads position out (slots (native j))=0
    rw [native_slot,TermCommit.heads,Fin.addCases_left,TermMass.heads,Fin.addCases_right]
  · intro j
    rw [scratch_slot]
    change TermCommit.heads position out (TermCommit.eraseSlots (j.castAdd 709))=0
    rw [TermCommit.heads_core]
    change TermRead.heads position ((j.castAdd 704).castAdd 5)=0
    rw [TermRead.heads,Fin.addCases_left]
theorem blank_small (P b : ℕ) (source : List Bool) (flag : Bool) (i : Fin 16) (hP : 1≤P) :
    TermRead.data P b [] source flag (i.castAdd 709)=List.replicate P false:=by
  change TermRead.data P b [] source flag ((i.castAdd 704).castAdd 5)=_
  rw [TermRead.data,Fin.addCases_left]
  unfold TermPadded.input TermCoefficient.input
  simp only [Fin.val_castAdd,if_neg (show i.val≠149 by omega)]
  split_ifs
  · exact CloseoutRowsIntegerReady.pad_empty_frame P hP
  · simp [ZeroPadding.pad]
theorem input_slots (P b : ℕ) (source out : List Bool) (flag : Bool)
    (ambient : Fin 94→List Bool) (hP : 1≤P) (i : Fin 110) :
    TermCommit.data P (TermRead.data P b [] source flag) ambient out (slots i)=
      MassPaddedCheck.input P ambient i:=by
  refine Fin.addCases (m:=94) (n:=16) ?_ ?_ i
  · intro j
    change TermCommit.data _ _ _ _ (slots (native j))=_
    rw [native_slot,TermCommit.data,Fin.addCases_left,TermMass.data,Fin.addCases_right,
      TermMass.tail,Fin.addCases_left]
    exact (MassPaddedCheck.input_native P ambient j).symm
  · intro j
    rw [scratch_slot]
    change TermCommit.data _ _ _ _ (TermCommit.eraseSlots (j.castAdd 709))=_
    rw [TermCommit.data_core,MassPaddedCheck.input_scratch,blank_small P b source flag j hP]
theorem output_slots (P : ℕ) (terms : Fin 725→List Bool) (result : Fin 110→List Bool)
    (out : List Bool) (i : Fin 110) :
    TermCommit.data P (changed terms result) (project result) out (slots i)=result i:=by
  refine Fin.addCases (m:=94) (n:=16) ?_ ?_ i
  · intro j
    change TermCommit.data _ _ _ _ (slots (native j))=_
    rw [native_slot,TermCommit.data,Fin.addCases_left,TermMass.data,Fin.addCases_right,
      TermMass.tail,Fin.addCases_left]
    rfl
  · intro j
    rw [scratch_slot]
    change TermCommit.data _ _ _ _ (TermCommit.eraseSlots (j.castAdd 709))=_
    rw [TermCommit.data_core,changed,dif_pos (by change j.val<16;exact j.isLt)]
    rfl
theorem output_outside (P : ℕ) (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (result : Fin 110→List Bool) (out : List Bool) (i : Fin 827)
    (hi : ∀ j,slots j≠i) :
    TermCommit.data P terms ambient out i=TermCommit.data P (changed terms result) (project result) out i:=by
  revert hi
  refine Fin.addCases (m:=826) (n:=1) ?_ ?_ i
  · intro j
    refine Fin.addCases (m:=725) (n:=101) ?_ ?_ j
    · intro k hk
      change TermCommit.data P terms ambient out (TermCommit.eraseSlots k)=
        TermCommit.data P (changed terms result) (project result) out (TermCommit.eraseSlots k)
      rw [TermCommit.data_core,TermCommit.data_core]
      by_cases hsmall:k.val<16
      · have hs:=hk (⟨94+k.val,by omega⟩ : Fin 110)
        apply (hs _).elim
        apply Fin.ext
        change (if 94+k.val<94 then _ else 94+k.val-94)=k.val
        rw [if_neg (by omega)]
        omega
      · rw [changed,dif_neg hsmall]
    · intro k
      refine Fin.addCases (m:=94) (n:=7) ?_ ?_ k
      · intro l hl;exact (hl (native l) (native_slot l)).elim
      · intro l _;simp only [TermCommit.data,Fin.addCases_left,TermMass.data,Fin.addCases_right,TermMass.tail]
  · intro j _;simp only [TermCommit.data,Fin.addCases_right]

theorem check_run (P B b k position : ℕ) (q : ℚ) (a : Estimate)
    (source out : List Bool) (flag : Bool) (ambient : Fin 94→List Bool)
    (h : Store B a [] ambient) (ha : a.Valid B) (hq : 0≤q) (hk : k≤B)
    (hp : CompetitorThresholdDecision.numerator q<2^k) (hd : q.den<2^k)
    (hc : MassCheck.budget B k+1≤P) (hi : ∀ i,(ambient i).length≤P) : ∃ checked result,
    runFrom (machine k q) (MassCheck.budget B k)
      ⟨(machine k q).start,TermCommit.heads position out,
        TermCommit.data P (TermRead.data P b [] source flag) ambient out⟩=some result ∧
      result.steps≤MassCheck.budget B k ∧ result.final.heads=TermCommit.heads position out ∧
      result.final.tapes=TermCommit.data P (changed (TermRead.data P b [] source flag) checked)
        (project checked) out ∧ Store B a [] (project checked) ∧
      (readTapeBit (checked 65) 0=true ↔ a.value≤q) ∧ (∀ i,(checked i).length≤P):=by
  obtain ⟨checked,⟨base,hb,bt,bh,bs⟩,store,meaning,bound⟩:=MassPaddedCheck.check_run P B k q a [] ambient
    h ha hq hk hp hd hc hi
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots slots_injective (MassCheck.machine k q) _
    (TermCommit.heads position out) (TermCommit.data P (TermRead.data P b [] source flag) ambient out) _
    (heads_slots position out) (input_slots P b source out flag ambient (by omega)) base hb
  refine ⟨checked,r,hr,rs.trans_le bs,?_,?_,store,meaning,bound⟩
  · funext i
    by_cases hs:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rh,bh,heads_slots]
    · exact (keep i (by simpa using hs)).1
  · funext i
    by_cases hs:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rt,bt,output_slots]
    · exact ((keep i (by simpa using hs)).2).trans
        (output_outside P (TermRead.data P b [] source flag) ambient checked out i (by simpa using hs))

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumCheck
