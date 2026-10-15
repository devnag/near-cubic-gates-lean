import Proof.CaseAnalysis.RecoveryProjectionScalars

/-! Two existing paid sweeps initialize precisely the original projector
scratch and its two B-sized retained cells. -/
namespace NearCubicWires.RepairOrdinary.RecoveryProjectionCold
open LocalBitMultitape RepairSource RecoveryRootRound SourceInterfaces
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 29)
noncomputable def backingMachine := RecoveryFocus.machine backingSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def bankMachine := Composition.machine eraseMachine backingMachine
def bankBudget (R B : ℕ) := (2*RecoveryProjectionRows.capacity R+4)+1+(2*B+4)

private theorem erased_low (R Q : ℕ) (queries : List Bool) (i : Fin 37) (hi : i.val<28) :
    erasedBank R Q queries i=List.replicate (RecoveryProjectionRows.capacity R) false := by
  have hn (j : Fin 37) (hj : (28 : ℕ)≤(j : Fin 37).val) : i≠j := by
    intro he;have hv:=congrArg Fin.val he;omega
  simp only [erasedBank,hn 28 (by decide),hn 29 (by decide),hn 32 (by decide),
    hn 34 (by decide),hn 35 (by decide),hn 33 (by decide),hn 31 (by decide),hn 36 (by decide),
    ite_false,or_self]

theorem erase_bank (R Q : ℕ) (queries : List Bool) (A : Fin 113→List Bool)
    (hbank : ∀ i,A (bankSlots i)=beforeBank R Q queries i) : ∃ O,
    ClockJoin.ReadyRun eraseMachine (2*RecoveryProjectionRows.capacity R+4) A O ∧
      (∀ i,O (bankSlots i)=erasedBank R Q queries i) ∧
      (∀ i : Fin 113,(37 : ℕ)≤(i : Fin 113).val→O i=A i) := by
  let cap:=RecoveryProjectionRows.capacity R
  have h:=(RecoveryScratchErase.erase_ready cap 0 (fun _ : Fin 29=>[]) (by simp)).focus
    eraseSlots erase_injective A (by
      intro i
      exact (hbank ((RecoveryProjectionInitialize.eraseSlots i).castAdd 1)).trans (by
        fin_cases i <;> rfl))
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  let data : Fin 31→List Bool := Fin.addCases (m:=30) (n:=1)
    (Fin.addCases (m:=29) (n:=1) (fun _=>List.replicate cap false) (fun _=>List.replicate cap true))
    (fun _=>List.replicate (max 0 (cap+1)) false)
  let O:=install eraseSlots A data
  refine ⟨O,⟨r,hr,ht,hh,hs.le⟩,?_,?_⟩
  · intro i
    by_cases hi : i.val<28
    · let j : Fin 29:=⟨i.val,by omega⟩
      have he : bankSlots i=eraseSlots ((j.castAdd 1).castAdd 1) := by
        apply Fin.ext
        simp only [bankSlots,eraseSlots,RecoveryProjectionInitialize.eraseSlots,Fin.val_castAdd,j,hi,ite_true]
      dsimp only [O]
      rw [he,install_slot _ erase_injective]
      simp only [data,Fin.addCases_left]
      change List.replicate cap false=erasedBank R Q queries i
      exact (erased_low R Q queries i hi).symm
    have cases : i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 := by
      have hil:=i.isLt
      have hv : i.val=28 ∨ i.val=29 ∨ i.val=30 ∨ i.val=31 ∨ i.val=32 ∨ i.val=33 ∨ i.val=34 ∨ i.val=35 ∨ i.val=36 := by omega
      norm_num only [Fin.ext_iff]
      exact hv
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (install_other eraseSlots A data _ (by decide)).trans (hbank 28)
    · exact (install_other eraseSlots A data _ (by decide)).trans (hbank 29)
    · exact install_slot eraseSlots erase_injective A data 28
    · exact (install_other eraseSlots A data _ (by decide)).trans (hbank 31)
    · exact install_slot eraseSlots erase_injective A data 29
    · have hz:=install_slot eraseSlots erase_injective A data 30
      change O 33=List.replicate (max 0 (cap+1)) false at hz
      change O 33=List.replicate (cap+1) false
      simpa only [Nat.zero_max] using hz
    · exact (install_other eraseSlots A data _ (by decide)).trans (hbank 34)
    · exact (install_other eraseSlots A data _ (by decide)).trans (hbank 35)
    · exact (install_other eraseSlots A data _ (by decide)).trans (hbank 36)
  · intro i hi
    apply install_other
    intro j h
    have hv:=congrArg (fun i : Fin 113=>i.val) h
    dsimp only [eraseSlots,RecoveryProjectionInitialize.eraseSlots,Fin.val_castAdd] at hv
    split_ifs at hv <;> omega

theorem bank_ready (R Q B : ℕ) (queries : List Bool) (A : Fin 113→List Bool)
    (hbank : ∀ i,A (bankSlots i)=beforeBank R Q queries i)
    (h104 : A 104=List.replicate B true) (h105 : A 105=[]) : ∃ O,
    ClockJoin.ReadyRun bankMachine (bankBudget R B) A O ∧
      (∀ i,O (bankSlots i)=readyBank R Q B queries i) ∧ O 104=List.replicate B true ∧
      (∀ i : Fin 113,(37 : ℕ)≤(i : Fin 113).val→i≠104→i≠105→O i=A i) := by
  obtain ⟨M,hm,hmbank,hmkeep⟩ := erase_bank R Q queries A hbank
  have h:=(RecoveryScratchErase.erase_ready B 0 (fun _ : Fin 2=>[]) (by simp)).focus
    backingSlots backing_injective M (by
      intro i;fin_cases i
      · exact hmbank 31
      · exact hmbank 36
      · exact (hmkeep 104 (by decide)).trans h104
      · exact (hmkeep 105 (by decide)).trans h105)
  let data : Fin 4→List Bool := ![List.replicate B false,List.replicate B false,
    List.replicate B true,List.replicate (B+1) false]
  have hd : ClockJoin.ReadyRun backingMachine (2*B+4) M (install backingSlots M data) := by
    obtain ⟨r,hr,ht,hh,hs⟩ := h
    refine ⟨r,hr,?_,hh,hs.le⟩
    rw [ht]
    congr 1
    funext i;fin_cases i <;> rfl
  let O:=install backingSlots M data
  refine ⟨O,ClockJoin.join eraseMachine backingMachine _ _ _ _ _ hm hd,?_,?_,?_⟩
  · intro i
    by_cases h31 : i=31
    · subst i;exact install_slot backingSlots backing_injective M data 0
    by_cases h36 : i=36
    · subst i;exact install_slot backingSlots backing_injective M data 1
    have hn : ∀ j,backingSlots j≠bankSlots i := by
      intro j h
      fin_cases j
      · exact h31 (Fin.ext (congrArg (fun i : Fin 113=>i.val) h).symm)
      · exact h36 (Fin.ext (congrArg (fun i : Fin 113=>i.val) h).symm)
      · have hv:=congrArg (fun i : Fin 113=>i.val) h
        change 104=i.val at hv
        have hi:=i.isLt;omega
      · have hv:=congrArg (fun i : Fin 113=>i.val) h
        change 105=i.val at hv
        have hi:=i.isLt;omega
    exact (install_other backingSlots M data _ hn).trans ((hmbank i).trans (by simp [readyBank,h31,h36]))
  · exact install_slot backingSlots backing_injective M data 2
  · intro i hi h104' h105'
    have hn : ∀ j,backingSlots j≠i := by
      intro j h;fin_cases j
      all_goals first
        | exact h104' h.symm
        | exact h105' h.symm
        | (have hv:=congrArg (fun i : Fin 113=>i.val) h;change 31=i.val at hv;omega)
        | (have hv:=congrArg (fun i : Fin 113=>i.val) h;change 36=i.val at hv;omega)
    exact (install_other backingSlots M data i hn).trans (hmkeep i hi)

end NearCubicWires.RepairOrdinary.RecoveryProjectionCold
