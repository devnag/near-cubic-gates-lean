import Proof.Amplification.RecoveryTseitinNativeCarrier

/-! Allocate the reusable native scratch by a paid erase pass from the
actual bounded cold prefix. Its reset log starts blank and is produced. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coldEraseSlots (i : Fin 1334) : Fin 1370 := (Reuse.eraseSlots i).castAdd 32
theorem coldErase_injective : Function.Injective coldEraseSlots := by
  intro i j he
  apply Reuse.erase_injective
  have hv:=congrArg Fin.val he
  exact Fin.ext hv
theorem coldErase_away (i : Fin 1338) (hi : Reuse.retained i) :
    ∀ j,coldEraseSlots j≠i.castAdd 32 := by
  intro j he
  have hv:=congrArg Fin.val he
  exact Reuse.erase_away i hi j (Fin.ext hv)
noncomputable def coldEraseProgram:=RecoveryFocus.machine coldEraseSlots (RecoveryScratchErase.resetMachine 1332)

theorem cold_erase_run (cap n count output : Nat) (word : List Bool)
    (heads : Fin 1370→Nat) (data : Fin 1370→List Bool)
    (hout : data 1333=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n))
    (hh : ∀ i,i≠1333 → heads i=0)
    (ht : ∀ i,retained i → data i=workspaceData cap n count output word i)
    (hb : ∀ j,(data ((Reuse.scratch j).castAdd 34)).length ≤ cap) : ∃ r,
    runFrom coldEraseProgram (2*cap+4)
      ⟨coldEraseProgram.start,heads,data⟩=some r ∧
      r.final.heads=heads ∧
      (∀ i : Fin 1338,r.final.tapes (i.castAdd 32)=Reuse.data n 0 word
        (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n)) (cap) i) ∧
      (∀ i : Fin 4,r.final.tapes ((i.natAdd 1338).castAdd 28)=
        (![CompareMachine.word count,List.replicate output true,[],[]] : Fin 4→List Bool) i) ∧
      r.steps ≤ 2*cap+4 := by
  let backing : Fin 1332→List Bool:=fun j=>data ((Reuse.scratch j).castAdd 34)
  have hcap : data 1336=List.replicate cap true :=
    ht 1336 (Or.inr (Or.inr (Or.inr ⟨by decide,by decide⟩)))
  have hlog : data 1337=[] := ht 1337 (Or.inr (Or.inr (Or.inr ⟨by decide,by decide⟩)))
  have hin (j : Fin 1334) : data (coldEraseSlots j)=
      (Fin.addCases (m:=1333) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=1332) (n:=1) (motive:=fun _=>List Bool) backing (fun _=>List.replicate cap true))
        (fun _=>[])) j := by
    refine Fin.addCases (m:=1332) (n:=2) (fun k=>?_) (fun k=>?_) j
    · simp only [coldEraseSlots,Reuse.eraseSlots,Fin.addCases_left]
      have he : k.castAdd 2=(k.castAdd 1).castAdd 1 := rfl
      rw [he]
      simp only [Fin.addCases_left,backing]
      rfl
    · fin_cases k
      · exact hcap
      · exact hlog
  have hhead (j : Fin 1334) : heads (coldEraseSlots j)=0 :=
    hh _ (coldErase_away 1333 (Or.inr (Or.inr (Or.inr rfl))) j)
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryScratchErase.erase_ready cap 0 backing hb).focus_at
    coldEraseSlots coldErase_injective heads data hin hhead
  refine ⟨r,hr,rh,?_,?_,rs.le⟩
  · intro i
    rw [rt]
    rcases Reuse.coverage i with hi|⟨j,rfl⟩
    · rw [install_other _ _ _ _ (coldErase_away i hi)]
      rcases hi with rfl|rfl|rfl|rfl
      · exact ht 0 (Or.inl rfl)
      · exact ht 1 (Or.inr (Or.inl rfl))
      · exact ht 1062 (Or.inr (Or.inr (Or.inl rfl)))
      · exact hout
    · change install coldEraseSlots data _ (coldEraseSlots j)=_
      rw [install_slot coldEraseSlots coldErase_injective]
      refine Fin.addCases (m:=1332) (n:=2) (fun k=>?_) (fun k=>?_) j
      · simp only [Reuse.eraseSlots,Fin.addCases_left]
        have he : k.castAdd 2=(k.castAdd 1).castAdd 1 := rfl
        rw [he]
        simp only [Fin.addCases_left]
        exact (Reuse.data_scratch n 0 word _ cap k).symm
      · fin_cases k
        · rfl
        · simp only [Nat.zero_max]; rfl
  · intro i
    rw [rt,install_other _ _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      have hj:=(Reuse.eraseSlots j).isLt
      simp only [coldEraseSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
      omega)]
    have hi : retained ((i.natAdd 1338).castAdd 28) := Or.inr (Or.inr (Or.inr (by
      have hi:=i.isLt
      simp only [Fin.val_castAdd,Fin.val_natAdd]
      omega)))
    rw [ht _ hi]
    fin_cases i <;> rfl

theorem cold_erase_forward : CursorRestore.NoLeft coldEraseProgram (1333 : Fin 1370) :=
  EquationRowCuts.unselected_forward coldEraseSlots _ _
    (coldErase_away 1333 (Or.inr (Or.inr (Or.inr rfl))))

end NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
