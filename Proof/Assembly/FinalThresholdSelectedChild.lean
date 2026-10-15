import Proof.Supplier.RowCachedCoordinateBounds
import Proof.Circuits.DecompositionCachedChildAccess
import Proof.CaseAnalysis.RowsTupleSeekFamilyRewind
import Proof.Amplification.RecoveryScratchErase

/-! The actual native-cache child is positioned, copied into one reusable padded
record bank, and rewound for its consumer. Dirty locator scratch is retained;
the separate copy backing/output are paidly erased before every copy. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdSelectedChild
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000

def heads (pos outPos : ℕ) : Fin 6 → ℕ := ![pos,0,outPos,1,0,0]
def bank (source backing out : List Bool) (n C : ℕ) : Fin 6 → List Bool :=
  ![source,backing,out,UnaryTemplate.tape n,List.replicate C true,List.replicate (C+1) false]
def rewindSlots : Fin 3 → Fin 6 := ![2,4,5]
def clearSlots : Fin 4 → Fin 6 := ![1,2,4,5]
noncomputable def rewind := RecoveryFocus.machine rewindSlots CompetitorRecordRewind.machine
noncomputable def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def copy := TapeEmbedding.machine 2 DecompositionSource.Records.child
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine rewind clear) copy) rewind
def budget {n : ℕ} (g : ExactThresholdGate n) (C : ℕ) :=
  6*C+(exactWord g).length+6*n+18

theorem rewind_run (source backing out : List Bool) (n C pos outPos : ℕ) (hp : outPos≤C) :
    Step rewind (2*C+2) (heads pos outPos) (bank source backing out n C)
      (heads pos 0) (bank source backing out n C) := by
  have h := CloseoutRowsTupleSeek.rewind_at (2 : Fin 6) 4 5 (by decide) (by decide) (by decide)
    C (heads pos outPos) (bank source backing out n C) hp rfl rfl rfl rfl
  refine h.congr ?_ rfl
  funext i;fin_cases i <;> simp [heads,Function.update]

theorem clear_run (source backing out : List Bool) (n C pos : ℕ)
    (hb : backing.length≤C) (ho : out.length≤C) :
    Step clear (2*C+4) (heads pos 0) (bank source backing out n C)
      (heads pos 0) (bank source (List.replicate C false) (List.replicate C false) n C) := by
  have base := Step.of_ready (RecoveryScratchErase.erase_ready C (C+1)
    (![backing,out] : Fin 2 → List Bool) (by intro i;fin_cases i <;>assumption))
  have h := base.dock clearSlots (by decide) (heads pos 0) (bank source backing out n C)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  refine h.congr (dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)) ?_
  apply HierarchyAllocation.install_eq clearSlots (by decide)
  · intro i;fin_cases i <;> first | rfl | simp [bank,clearSlots,Fin.addCases]
  · intro i hi;fin_cases i
    all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)

theorem copy_run {n : ℕ} (g : ExactThresholdGate n) (pre tail : List Bool) (C : ℕ) :
    Step copy ((exactWord g).length+6*n+7) (heads pre.length 0)
      (bank (pre++exactWord g++tail) (List.replicate C false) (List.replicate C false) n C)
      (heads (pre.length+(exactWord g).length) (exactWord g).length)
      (bank (pre++exactWord g++tail) (ZeroPadding.pad C (DecompositionSource.Records.childSaved g []))
        (ZeroPadding.pad C (exactWord g)) n C) := by
  obtain ⟨r,hr,hf,_⟩ := DecompositionSource.Records.child_run g pre tail [] []
  have h := (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).pad
    (![0,C,C,n+2] : Fin 4 → ℕ)
  have padded : Step DecompositionSource.Records.child ((exactWord g).length+6*n+7)
      (![pre.length,0,0,1] : Fin 4 → ℕ)
      ![pre++exactWord g++tail,List.replicate C false,List.replicate C false,UnaryTemplate.tape n]
      ![pre.length+(exactWord g).length,0,(exactWord g).length,1]
      ![pre++exactWord g++tail,ZeroPadding.pad C (DecompositionSource.Records.childSaved g []),
        ZeroPadding.pad C (exactWord g),UnaryTemplate.tape n] := by
    refine (h.congr_in rfl ?_).congr ?_ ?_
    · funext i;fin_cases i
      · exact ZeroPadding.pad_zero _
      · simp [ZeroPadding.pad]
      · simp [ZeroPadding.pad]
      · exact DecompositionSource.Records.template_pad n
    · funext i;fin_cases i <;>simp [DecompositionSource.Records.store]
    · funext i;fin_cases i <;>simp [DecompositionSource.Records.store,DecompositionSource.Records.template_pad]
  have he := padded.embed (fun _ : Fin 2=>0) (![List.replicate C true,List.replicate (C+1) false] : Fin 2 → List Bool)
  refine (he.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>rfl

theorem run {n : ℕ} (g : ExactThresholdGate n) (pre tail backing out : List Bool)
    (C outPos : ℕ) (hb : backing.length≤C) (ho : out.length≤C) (hp : outPos≤C)
    (hg : (exactWord g).length≤C) :
    Step machine (budget g C) (heads pre.length outPos) (bank (pre++exactWord g++tail) backing out n C)
      (heads (pre.length+(exactWord g).length) 0)
      (bank (pre++exactWord g++tail) (ZeroPadding.pad C (DecompositionSource.Records.childSaved g []))
        (ZeroPadding.pad C (exactWord g)) n C) := by
  have a := rewind_run (pre++exactWord g++tail) backing out n C pre.length outPos hp
  have b := clear_run (pre++exactWord g++tail) backing out n C pre.length hb ho
  have c := copy_run g pre tail C
  have d := rewind_run (pre++exactWord g++tail) (ZeroPadding.pad C (DecompositionSource.Records.childSaved g []))
    (ZeroPadding.pad C (exactWord g)) n C (pre.length+(exactWord g).length) (exactWord g).length hg
  have all := ((a.seq b).seq c).seq d
  simpa only [machine,budget,show ((2*C+2+1+(2*C+4))+1+((exactWord g).length+6*n+7))+1+(2*C+2)=
    6*C+(exactWord g).length+6*n+18 by omega] using all

private theorem saved_fit (zs : List ℤ) (backing : List Bool) (C : ℕ)
    (hz : ∀ z∈zs,natBitLength z.natAbs+2≤C) (hb : backing.length≤C) :
    (DecompositionSource.Fields.savedList zs backing).length≤C := by
  induction zs generalizing backing with
  | nil => exact hb
  | cons z zs ih =>
    apply ih _ (fun z hz'=>hz z (by simp [hz']))
    have h := hz z (by simp)
    simp [DecompositionSource.Fields.saved,PCPPQueryField.saved,
      StablePartition.Workspace.overlay_length,UnaryTemplate.tape]
    omega

theorem child_saved_fit {n : ℕ} (g : ExactThresholdGate n) (C : ℕ)
    (hC : (exactWord g).length+2≤C) :
    (DecompositionSource.Records.childSaved g []).length≤C := by
  have hh : ∀ z∈RowNativeCoordinate.fields g,natBitLength z.natAbs+2≤C := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hz
    have hi' : i≤n := by rw [RowNativeCoordinate.fields_length] at hi;omega
    have hb := (RowCachedCoordinateBounds.coordinate_bytes g i hi').2
    change natBitLength ((RowNativeCoordinate.fields g)[i]).natAbs≤(exactWord g).length at hb
    omega
  have h := saved_fit (RowNativeCoordinate.fields g) [] C hh (by simp)
  simpa [DecompositionSource.Records.childSaved,DecompositionSource.Fields.savedList,
    RowNativeCoordinate.fields,List.foldl_append] using h

def selectedSlots : Fin 6 → Fin 9 := ![0,5,6,3,7,8]
def extras (backing out : List Bool) (C : ℕ) : Fin 4 → List Bool :=
  ![backing,out,List.replicate C true,List.replicate (C+1) false]
def selectedHeads (outPos : ℕ) : Fin 9 → ℕ :=
  Fin.addCases (motive := fun _=>ℕ) (![0,0,0,1,1] : Fin 5 → ℕ) (![0,outPos,0,0] : Fin 4 → ℕ)
def selectedInput {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (backing out : List Bool) (C : ℕ) :
    Fin 9 → List Bool := Fin.addCases (motive := fun _=>List Bool)
      (![exactListWord gs,[],[],UnaryTemplate.tape n,UnaryTemplate.tape i] : Fin 5 → List Bool)
      (extras backing out C)
noncomputable def selectedMachine := Composition.machine
  (TapeEmbedding.machine 4 DecompositionCachedChild.machine) (RecoveryFocus.machine selectedSlots machine)

theorem selected_run {n : ℕ} (gs : List (ExactThresholdGate n)) (i : Fin gs.length)
    (backing out : List Bool) (C outPos : ℕ)
    (hb : backing.length≤C) (ho : out.length≤C) (hp : outPos≤C)
    (hg : (exactWord (gs.get i)).length+2≤C) :
    ∃ (H : Fin 9 → ℕ) (A : Fin 9 → List Bool),
      Step selectedMachine (DecompositionCachedChild.budget gs i.val+1+budget (gs.get i) C)
        (selectedHeads outPos) (selectedInput gs i.val backing out C) H A ∧
      A 0=exactListWord gs ∧
      H 0=(natWord gs.length++(gs.take i.val).flatMap exactWord).length+(exactWord (gs.get i)).length ∧
      A 3=UnaryTemplate.tape n ∧ H 3=1 ∧ A 4=UnaryTemplate.tape i.val ∧ H 4=1 ∧
      A 6=ZeroPadding.pad C (exactWord (gs.get i)) ∧ H 6=0 ∧
      A 5=ZeroPadding.pad C (DecompositionSource.Records.childSaved (gs.get i) []) ∧ H 5=0 ∧
      A 7=List.replicate C true ∧ H 7=0 ∧ A 8=List.replicate (C+1) false ∧ H 8=0 := by
  obtain ⟨r,hr,hs,hpos,ha,hah,hi,hih,_⟩ := DecompositionCachedChild.position_run gs i.val i.isLt.le
  have first := (Step.of_run hr rfl rfl).embed (![0,outPos,0,0] : Fin 4 → ℕ) (extras backing out C)
  let P : Fin 9 → ℕ := Fin.addCases (motive := fun _=>ℕ) r.final.heads (![0,outPos,0,0] : Fin 4 → ℕ)
  let B : Fin 9 → List Bool := Fin.addCases (motive := fun _=>List Bool) r.final.tapes (extras backing out C)
  let pre := natWord gs.length++(gs.take i.val).flatMap exactWord
  let tail := (gs.drop (i.val+1)).flatMap exactWord
  have hword : exactListWord gs=pre++exactWord (gs.get i)++tail :=
    DecompositionCachedChild.selected_word gs i.val i.isLt
  have ready := run (gs.get i) pre tail backing out C outPos hb ho hp (by omega)
  have docked := ready.dock selectedSlots (by decide) P B (by
    intro j;fin_cases j
    · change r.final.heads 0=pre.length
      simpa [pre,List.length_append] using hpos
    · rfl
    · rfl
    · exact hah
    · rfl
    · rfl) (by
    intro j;fin_cases j
    · exact hs.trans hword
    · rfl
    · rfl
    · exact ha
    · rfl
    · rfl)
  have all := first.seq docked
  refine ⟨_,_,all,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_slot selectedSlots (by decide) _ _ 0).trans hword.symm
  · exact dockH_slot selectedSlots (by decide) _ _ 0
  · exact install_slot selectedSlots (by decide) _ _ 3
  · exact dockH_slot selectedSlots (by decide) _ _ 3
  · exact (install_other selectedSlots _ _ _ (by decide)).trans hi
  · exact (dockH_other selectedSlots _ _ _ (by decide)).trans hih
  · exact install_slot selectedSlots (by decide) _ _ 2
  · exact dockH_slot selectedSlots (by decide) _ _ 2
  · exact install_slot selectedSlots (by decide) _ _ 1
  · exact dockH_slot selectedSlots (by decide) _ _ 1
  · exact install_slot selectedSlots (by decide) _ _ 4
  · exact dockH_slot selectedSlots (by decide) _ _ 4
  · exact install_slot selectedSlots (by decide) _ _ 5
  · exact dockH_slot selectedSlots (by decide) _ _ 5

end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdSelectedChild
