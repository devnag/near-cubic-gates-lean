import Proof.CaseAnalysis.WitnessTermRead

/-! The term reader's reusable bank is cleared in one paid sweep. Its
original coefficient width and the canonical stream cursor are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRead
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots (i : Fin 721) : Fin 725:=
  if i.val<149 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
def scratchSlots (i : Fin 719):=eraseSlots (i.castAdd 2)
theorem erase_val (i : Fin 721) : (eraseSlots i).val=if i.val<149 then i.val else i.val+1:=by
  unfold eraseSlots
  split <;> rfl
theorem erase_injective : Function.Injective eraseSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [erase_val,erase_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem erase_upper (i : Fin 721) : (eraseSlots i).val≤721:=by
  rw [erase_val]
  split_ifs <;> omega
theorem erase_width (i : Fin 721) : eraseSlots i≠149:=by
  intro h
  have hv:=congrArg Fin.val h
  rw [erase_val] at hv
  split_ifs at hv <;> omega
theorem erase_later (i : Fin 5) (hi : 2 ≤ i.val) : ∀ j : Fin 721,eraseSlots j≠i.natAdd 720:=by
  intro j h
  have hv:=congrArg Fin.val h
  have hu:=erase_upper j
  change (eraseSlots j).val=720+i.val at hv
  omega
theorem scratch_small (i : Fin 719) : (scratchSlots i).val<720:=by
  rw [scratchSlots,erase_val]
  split_ifs <;> simp_all <;> omega
theorem scratch_covers (i : Fin 720) (hi : i≠149) : ∃ j : Fin 719,scratchSlots j=core i:=by
  have hn:i.val≠149:=by intro h;exact hi (Fin.ext h)
  by_cases h:i.val<149
  · refine ⟨⟨i.val,by omega⟩,Fin.ext ?_⟩
    simp only [scratchSlots,erase_val,Fin.val_castAdd,core,h,if_true]
  · refine ⟨⟨i.val-1,by omega⟩,Fin.ext ?_⟩
    rw [scratchSlots,erase_val]
    simp only [Fin.val_castAdd,core]
    rw [if_neg (show ¬i.val-1<149 by omega)]
    omega
noncomputable def eraser:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 719)
noncomputable def erased (P : ℕ) (tapes : Fin 725→List Bool):=
  install eraseSlots tapes (PCPTraversal.clearedLocal 719 P (P+1))
theorem erased_scratch (P : ℕ) (tapes : Fin 725→List Bool) (i : Fin 719) :
    erased P tapes (scratchSlots i)=List.replicate P false:=by
  have h:=install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 719 P (P+1))
    ((i.castAdd 1).castAdd 1)
  have he:(i.castAdd 1).castAdd 1=i.castAdd 2:=Fin.ext rfl
  have hout:PCPTraversal.clearedLocal 719 P (P+1) ((i.castAdd 1).castAdd 1)=List.replicate P false:=by
    simp only [PCPTraversal.clearedLocal,Fin.addCases_left]
  rw [hout] at h
  simpa only [erased,scratchSlots,he] using h

theorem erased_data (P b : ℕ) (source : List Bool) (flag : Bool) (tapes : Fin 725→List Bool)
    (hP : 1≤P) (hwidth : tapes 149=ZeroPadding.pad P (List.replicate b true))
    (hextra : ∀ i,tapes (i.natAdd 720)=extra P source flag i) :
    erased P tapes=data P b [] source flag:=by
  funext i
  refine Fin.addCases (m:=720) (n:=5) ?_ ?_ i
  · intro j
    simp only [data,Fin.addCases_left]
    by_cases hj:j=149
    · subst j
      exact (install_other _ _ _ _ erase_width).trans hwidth
    · have hb:TermPadded.input P b [] j=List.replicate P false:=by
        have hn:j.val≠149:=by intro h;exact hj (Fin.ext h)
        simp only [TermPadded.input,TermCoefficient.input,if_neg hn]
        split_ifs
        · exact CloseoutRowsIntegerReady.pad_empty_frame P hP
        · simp [ZeroPadding.pad]
      rw [hb]
      obtain ⟨k,hk⟩:=scratch_covers j hj
      change erased P tapes (core j)=_
      rw [←hk,erased_scratch]
  · intro j
    fin_cases j
    · exact install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 719 P (P+1)) 719
    · have h:=install_slot eraseSlots erase_injective tapes (PCPTraversal.clearedLocal 719 P (P+1))
        ((0 : Fin 1).natAdd 720)
      have he:eraseSlots ((0 : Fin 1).natAdd 720)=(721 : Fin 725):=by decide
      change erased P tapes 721=List.replicate (P+1) false
      simpa only [erased,he,PCPTraversal.clearedLocal,Fin.addCases_right,Nat.max_self] using h
    · exact (install_other _ _ _ _ (erase_later 2 (by decide))).trans (hextra 2)
    · exact (install_other _ _ _ _ (erase_later 3 (by decide))).trans (hextra 3)
    · exact (install_other _ _ _ _ (erase_later 4 (by decide))).trans (hextra 4)

theorem erase_run (P b position : ℕ) (source : List Bool) (flag : Bool)
    (tapes : Fin 725→List Bool) (hP : 1≤P)
    (hbound : ∀ i : Fin 719,(tapes (scratchSlots i)).length≤P)
    (hwidth : tapes 149=ZeroPadding.pad P (List.replicate b true))
    (hextra : ∀ i,tapes (i.natAdd 720)=extra P source flag i) : ∃ result,
    runFrom eraser (2*P+4) ⟨eraser.start,heads position,tapes⟩=some result ∧
      result.steps=2*P+4 ∧ result.final.heads=heads position ∧
      result.final.tapes=data P b [] source flag:=by
  have h:=RecoveryScratchErase.erase_ready P (P+1) (fun i=>tapes (scratchSlots i)) hbound
  obtain ⟨r,hr,rh,rt,rs⟩:=h.focus_at eraseSlots erase_injective (heads position) tapes
    (by
      intro i
      refine Fin.addCases (m:=720) (n:=1) ?_ ?_ i
      · intro j
        refine Fin.addCases (m:=719) (n:=1) ?_ ?_ j
        · intro k;simp only [Fin.addCases_left];rfl
        · intro k;fin_cases k;exact hextra 0
      · intro j;fin_cases j;exact hextra 1)
    (by
      intro i
      have hu:=erase_upper i
      have hz (j : Fin 725) (hj : j.val≤721) : heads position j=0:=by
        revert hj
        refine Fin.addCases (m:=720) (n:=5) ?_ ?_ j
        · intro k _;simp only [heads,Fin.addCases_left]
        · intro k hk
          have hv:k.val≤1:=by change 720+k.val≤721 at hk;omega
          have he:k=0 ∨ k=1:=by simp only [Fin.ext_iff];omega
          rcases he with rfl|rfl <;> rfl
      exact hz _ hu)
  exact ⟨r,hr,rs,rh,rt.trans (erased_data P b source flag tapes hP hwidth hextra)⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRead
