import Proof.MachineModel.TopDownPaidFamilyConsumers

/-! A physical reset of the completed raw-family output followed by the
existing mixed-width natural sum. All old tape words are preserved. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace NearCubicWires.P1TopDownPaidFamilySum
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open RecoveryRootRound RecoveryExecution SignedSortKey
open CloseoutFinalC10RowAnswerWord

noncomputable def mixedInput (b v : Nat) (xs : List Nat) : Fin 10→List Bool :=
  Fin.addCases (m:=9) (n:=1) (motive:=fun _=>List Bool)
    (CompetitorCountEntry.input b v xs) (fun _ : Fin 1=>[])

theorem mixed_run (b v : Nat) (xs : List Nat) (hw : b ≤ v)
    (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^v) :
    ∃ Z, Step sumMachine (rowAnswerFuel v xs.length) (fun _=>0) (mixedInput b v xs)
      (fun _=>0) Z ∧ Z 0=CompetitorCountFold.raw b xs ∧ Z 5=frame (binary v xs.sum) := by
  obtain ⟨base,hbase,h5,h0,hsteps⟩:=CompetitorCountEntry.entry_run b v xs hw hx hfit
  obtain ⟨r,hr,ht,_,hh,hs,_⟩:=Rewind.Workspace.reset_workspace CompetitorCountEntry.machine _ _ base hbase 0
  rw [hsteps] at hr hs
  refine ⟨r.final.tapes,⟨r,hr,funext hh,rfl,hs.le⟩,?_,?_⟩
  · exact (ht 0).trans h0
  · exact (ht 5).trans h5

def extra (b v N : Nat) : Fin 11→List Bool :=
  ![List.replicate (N*b) true,[],List.replicate b true,List.replicate v true,[],
    List.replicate (2*v+1) false,frame (binary v 0),[],[],
    RepairSource.VerifierDecoding.CompareMachine.word N,[]]
def readSlots {m : Nat} (raw : Fin m) : Fin 3→Fin (m+11) :=
  ![raw.castAdd 11,(0 : Fin 11).natAdd m,(1 : Fin 11).natAdd m]
def sumSlots {m : Nat} (raw : Fin m) : Fin 10→Fin (m+11) :=
  ![raw.castAdd 11,(2 : Fin 11).natAdd m,(3 : Fin 11).natAdd m,(4 : Fin 11).natAdd m,
    (5 : Fin 11).natAdd m,(6 : Fin 11).natAdd m,(7 : Fin 11).natAdd m,
    (8 : Fin 11).natAdd m,(9 : Fin 11).natAdd m,(10 : Fin 11).natAdd m]

theorem read_injective {m : Nat} (raw : Fin m) : Function.Injective (readSlots raw) := by
  intro i j h
  have hv:=congrArg Fin.val h
  have hp:=raw.isLt
  fin_cases i <;> fin_cases j <;> simp [readSlots] at hv ⊢ <;> omega

theorem sum_injective {m : Nat} (raw : Fin m) : Function.Injective (sumSlots raw) := by
  intro i j h
  have hv:=congrArg Fin.val h
  have hp:=raw.isLt
  fin_cases i <;> fin_cases j <;> simp [sumSlots] at hv ⊢ <;> omega

noncomputable def first {m : Nat} (raw : Fin m) := RecoveryFocus.machine (readSlots raw) CompetitorRecordRewind.machine
noncomputable def last {m : Nat} (raw : Fin m) := RecoveryFocus.machine (sumSlots raw) sumMachine
noncomputable def machine {m : Nat} (raw : Fin m) := Composition.machine (first raw) (last raw)
def budget (b v N : Nat) := 2*(N*b)+2+1+rowAnswerFuel v N

theorem raw_length (b : Nat) (xs : List Nat) : (CompetitorCountFold.raw b xs).length=xs.length*b := by
  induction xs with
  | nil=>simp [CompetitorCountFold.raw]
  | cons x xs _ih=>simp [CompetitorCountFold.raw,List.length_append,binary_length,Nat.add_mul,Nat.add_comm]

theorem read_sum_ne {m : Nat} (raw : Fin m) (i : Fin 3) (j : Fin 10) (hj : j≠0) :
    readSlots raw i≠sumSlots raw j := by
  intro he
  have h:=congrArg Fin.val he
  have hp:=raw.isLt
  fin_cases i <;> fin_cases j <;> simp [readSlots,sumSlots] at h hj <;> omega

theorem sum_old_hit {m : Nat} (raw i : Fin m) (j : Fin 10)
    (he : sumSlots raw j=i.castAdd 11) : i=raw := by
  have h:=congrArg Fin.val he
  have hi:=i.isLt
  fin_cases j <;> simp [sumSlots] at h
  · exact Fin.ext h.symm
  all_goals omega

theorem read_old_hit {m : Nat} (raw i : Fin m) (j : Fin 3)
    (he : readSlots raw j=i.castAdd 11) : i=raw := by
  have h:=congrArg Fin.val he
  have hi:=i.isLt
  fin_cases j <;> simp [readSlots] at h
  · exact Fin.ext h.symm
  all_goals omega

private theorem old_install {m n : Nat} [NeZero n] (raw : Fin m) (slots : Fin n→Fin (m+11))
    (hinj : Function.Injective slots) (hzero : slots 0=raw.castAdd 11)
    (hit : ∀ i j,slots j=i.castAdd 11→i=raw)
    (A : Fin (m+11)→List Bool) (Z : Fin n→List Bool) (hz : Z 0=A (raw.castAdd 11)) :
    ∀ i : Fin m,install slots A Z (i.castAdd 11)=A (i.castAdd 11) := by
  intro i
  by_cases hi : i=raw
  · subst i;rw [←hzero,install_slot _ hinj];simpa only [hzero] using hz
  · rw [install_other _ _ _ _ (fun j he=>hi (hit i j he))]

private theorem old_heads {m n : Nat} [NeZero n] (raw : Fin m) (slots : Fin n→Fin (m+11))
    (hinj : Function.Injective slots) (hzero : slots 0=raw.castAdd 11)
    (hit : ∀ i j,slots j=i.castAdd 11→i=raw)
    (H : Fin (m+11)→Nat) :
    ∀ i,dockH slots H (fun _=>0) (i.castAdd 11)=if i=raw then 0 else H (i.castAdd 11) := by
  intro i
  by_cases hi : i=raw
  · subst i;rw [←hzero,dockH_slot _ hinj];simp
  · rw [dockH_other _ _ _ _ (fun j he=>hi (hit i j he)),if_neg hi]

noncomputable def rewound {m : Nat} (raw : Fin m) (A : Fin m→List Bool) (b v : Nat) (xs : List Nat) :=
  install (readSlots raw) (Fin.addCases A (extra b v xs.length))
    (![CompetitorCountFold.raw b xs,List.replicate (xs.length*b) true,
      List.replicate (xs.length*b) false] : Fin 3→List Bool)
noncomputable def rewoundHeads {m : Nat} (raw : Fin m) (H : Fin m→Nat) :=
  dockH (readSlots raw) (Fin.addCases H (fun _ : Fin 11=>0)) (fun _=>0)
noncomputable def final {m : Nat} (raw : Fin m) (A : Fin m→List Bool) (b v : Nat) (xs : List Nat) (Z : Fin 10→List Bool) :=
  install (sumSlots raw) (rewound raw A b v xs) Z
noncomputable def finalHeads {m : Nat} (raw : Fin m) (H : Fin m→Nat) :=
  dockH (sumSlots raw) (rewoundHeads raw H) (fun _=>0)

set_option maxHeartbeats 1000000 in
theorem run {m : Nat} (raw : Fin m) (H : Fin m→Nat) (A : Fin m→List Bool)
    (b v : Nat) (xs : List Nat) (hH : H raw=(CompetitorCountFold.raw b xs).length)
    (hA : A raw=CompetitorCountFold.raw b xs) (hw : b ≤ v)
    (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^v) :
    ∃ Z, Step (machine raw) (budget b v xs.length)
      (Fin.addCases H (fun _ : Fin 11=>0)) (Fin.addCases A (extra b v xs.length))
      (finalHeads raw H) (final raw A b v xs Z) ∧
      final raw A b v xs Z ((6 : Fin 11).natAdd m)=frame (binary v xs.sum) ∧
      (∀ i,final raw A b v xs Z (i.castAdd 11)=A i) ∧
      (∀ i,finalHeads raw H (i.castAdd 11)=if i=raw then 0 else H i) := by
  obtain ⟨r,hr,hf,hs⟩:=CompetitorRecordRewind.rewind_run
    (CompetitorCountFold.raw b xs) (xs.length*b) (CompetitorCountFold.raw b xs).length
    (by rw [raw_length])
  have read : Step CompetitorRecordRewind.machine (2*(xs.length*b)+2)
      ![(CompetitorCountFold.raw b xs).length,0,0]
      ![CompetitorCountFold.raw b xs,List.replicate (xs.length*b) true,[]]
      (fun _=>0) ![CompetitorCountFold.raw b xs,List.replicate (xs.length*b) true,
        List.replicate (xs.length*b) false] := by
    exact ⟨r,hr,by rw [hf];funext i;fin_cases i <;> rfl,by rw [hf];rfl,hs.le⟩
  have firstStep:=read.dock (readSlots raw) (read_injective raw)
    (Fin.addCases H (fun _ : Fin 11=>0)) (Fin.addCases A (extra b v xs.length))
    (by intro i;fin_cases i <;> simp [readSlots,hH])
    (by intro i;fin_cases i <;> simp [readSlots,extra,hA])
  obtain ⟨Z,sumStep,hz0,hz5⟩:=mixed_run b v xs hw hx hfit
  have secondStep:=sumStep.dock (sumSlots raw) (sum_injective raw)
    (rewoundHeads raw H) (rewound raw A b v xs)
    (by
      intro j
      by_cases hj : j=0
      · subst j;unfold rewoundHeads
        change dockH (readSlots raw) _ _ (readSlots raw 0)=0
        rw [dockH_slot _ (read_injective raw)]
      · unfold rewoundHeads
        rw [dockH_other _ _ _ _ (fun i=>read_sum_ne raw i j hj)]
        fin_cases j <;> simp [sumSlots] at hj ⊢)
    (by
      intro j
      by_cases hj : j=0
      · subst j;unfold rewound
        change install (readSlots raw) _ _ (readSlots raw 0)=_
        rw [install_slot _ (read_injective raw)]
        rfl
      · unfold rewound
        rw [install_other _ _ _ _ (fun i=>read_sum_ne raw i j hj)]
        fin_cases j <;> simp [sumSlots,extra,mixedInput,CompetitorCountEntry.input,Fin.addCases] at hj ⊢)
  refine ⟨Z,firstStep.seq secondStep,?_,?_,?_⟩
  · change install (sumSlots raw) _ Z (sumSlots raw 5)=_
    rw [install_slot _ (sum_injective raw)]
    exact hz5
  · intro i
    have hr0 : rewound raw A b v xs (raw.castAdd 11)=A raw := by
      unfold rewound
      change install (readSlots raw) _ _ (readSlots raw 0)=A raw
      rw [install_slot _ (read_injective raw)]
      exact hA.symm
    have sr:=old_install raw (sumSlots raw) (sum_injective raw) rfl (sum_old_hit raw)
      (rewound raw A b v xs) Z (hz0.trans (hA.symm.trans hr0.symm)) i
    unfold final
    rw [sr]
    simpa only [rewound,Fin.addCases_left] using old_install raw (readSlots raw) (read_injective raw) rfl (read_old_hit raw)
      (Fin.addCases A (extra b v xs.length))
      (![CompetitorCountFold.raw b xs,List.replicate (xs.length*b) true,
        List.replicate (xs.length*b) false] : Fin 3→List Bool)
      (by simpa using hA.symm) i
  · intro i
    rw [finalHeads,old_heads raw (sumSlots raw) (sum_injective raw) rfl (sum_old_hit raw),
      rewoundHeads,old_heads raw (readSlots raw) (read_injective raw) rfl (read_old_hit raw)]
    split_ifs <;> simp

end NearCubicWires.P1TopDownPaidFamilySum
