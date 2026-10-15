import Proof.Hierarchy.CompetitorPlaneTableEntry

/-! The native table entry creates its zero accumulator bank and reusable
reset tape by an actual erase, before consuming the serialized planes. The
physical dimension fields are explicit retained inputs of this parent. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneTableInitialize
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneTable CompetitorPlaneStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev capacity := CompetitorPlanePacketPass.capacity
def input (b w n : ℕ) (source : List Bool) : Fin 34 → List Bool := fun i =>
  if i=9 then ZeroPadding.pad (capacity w n) (List.replicate w true)
  else if i=20 then ZeroPadding.pad (capacity w n) (List.replicate b true)
  else if i=21 then ZeroPadding.pad (capacity w n) (List.replicate (CompetitorPlane.capacity w) true)
  else if i=27 then ZeroPadding.pad (capacity w n) (RepairSource.VerifierDecoding.CompareMachine.word n)
  else if i=30 then List.replicate (capacity w n) true
  else if i=32 then source else if i=33 then List.replicate (n*b) true else []
def slots : Fin 3 → Fin 34 := ![19,30,31]
def eraseOutput (D : ℕ) : Fin 3 → List Bool :=
  ![List.replicate D false,List.replicate D true,List.replicate (D+1) false]
noncomputable def clear := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 1)
noncomputable def cleared (b w n : ℕ) (source : List Bool) :=
  install slots (input b w n source) (eraseOutput (capacity w n))

theorem erase_ready (D : ℕ) : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 1) (2*D+4)
    (![[],List.replicate D true,[]]) (eraseOutput D) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryScratchErase.erase_ready D 0 (fun _ : Fin 1 => [])
    (by intro i; simp)
  have he : (Fin.addCases (m := 2) (n := 1) (motive := fun _ => List Bool)
      (Fin.addCases (m := 1) (n := 1) (motive := fun _ => List Bool)
        (fun _ => []) (fun _ => List.replicate D true)) (fun _ => List.replicate 0 false))=
      ![[],List.replicate D true,[]] := by funext i; fin_cases i <;> rfl
  rw [he] at hr
  refine ⟨r,hr,?_,hh,hs.le⟩
  funext i
  fin_cases i <;> exact congrFun ht _

theorem clear_ready (b w n : ℕ) (source : List Bool) :
    ClockJoin.ReadyRun clear (2*capacity w n+4) (input b w n source) (cleared b w n source) := by
  exact CompetitorRationalProducts.bounded_focus slots (by decide) _ _ _ (erase_ready (capacity w n)) (input b w n source)
    (by intro i; fin_cases i <;> rfl)

theorem zero_word (w n : ℕ) : oldWords w (canonical (zero n))=List.replicate (n*(2*w)) false := by
  simp only [oldWords,canonical,cells,List.flatMap_def,List.map_ofFn]
  have hz : (fun i : Fin n => oldWord w (cell (fun _ => 0) (zero n) i))=
      (fun _ : Fin n => List.replicate (2*w) false) := by
    funext i
    simp [oldWord,cell,zero,CompetitorPlane.pairWord,RankCarrier.binary_zero,two_mul]
  change (List.ofFn (fun i : Fin n => oldWord w (cell (fun _ => 0) (zero n) i))).flatten=_
  rw [hz,List.ofFn_const]
  exact List.flatten_replicate_replicate ..

theorem cleared_context (b w n : ℕ) (source : List Bool) (hb : b≤w) :
    TableContext b w (zero n) (cleared b w n source) := by
  have hinj : Function.Injective slots := by decide
  have keep (i : Fin 34) (h19 : i≠19) (h30 : i≠30) (h31 : i≠31) :
      cleared b w n source i=input b w n source i :=
    install_other slots _ _ i (by intro j; fin_cases j <;> first | exact Ne.symm h19 | exact Ne.symm h30 | exact Ne.symm h31)
  have h19 : cleared b w n source 19=List.replicate (capacity w n) false :=
    install_slot slots hinj _ _ 0
  have h30 : cleared b w n source 30=List.replicate (capacity w n) true :=
    install_slot slots hinj _ _ 1
  have h31 : cleared b w n source 31=List.replicate (capacity w n+1) false :=
    install_slot slots hinj _ _ 2
  obtain ⟨hw,hold,hn,hC⟩ := CompetitorPlanePaddedEntry.capacity_bounds w n
  change 2*w+1≤capacity w n at hw
  change n*(2*w)≤capacity w n at hold
  change n+1≤capacity w n at hn
  change CompetitorPlane.capacity w≤capacity w n at hC
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [show (canonical (zero n)).length=n from cells_length _ _]
    rw [h19,zero_word]
    simp only [ZeroPadding.pad,List.length_replicate,← List.replicate_add,Nat.add_sub_of_le hold]
  · simpa [canonical,cells_length,input] using keep 9 (by decide) (by decide) (by decide)
  · simpa [canonical,cells_length,input] using keep 20 (by decide) (by decide) (by decide)
  · simpa [canonical,cells_length,input] using keep 21 (by decide) (by decide) (by decide)
  · simpa [canonical,cells_length,input] using keep 27 (by decide) (by decide) (by decide)
  · simpa [CompetitorPlanePaddedEntry.count_length,canonical,cells_length,input] using keep 33 (by decide) (by decide) (by decide)
  · simpa only [canonical,cells_length] using h30
  · simpa only [canonical,cells_length] using h31
  · intro i
    simp only [canonical,cells_length]
    change (cleared b w n source (CompetitorPlanePacketPass.localTape i)).length≤capacity w n
    by_cases hi : CompetitorPlanePacketPass.localTape i=19
    · rw [hi,h19,List.length_replicate]
    · have h30' : CompetitorPlanePacketPass.localTape i≠30 := by intro h; have hv:=congrArg Fin.val h; change i.val=30 at hv; omega
      have h31' : CompetitorPlanePacketPass.localTape i≠31 := by intro h; have hv:=congrArg Fin.val h; change i.val=31 at hv; omega
      rw [keep _ hi h30' h31']
      fin_cases i <;>
        simp [input,CompetitorPlanePacketPass.localTape,ZeroPadding.pad_length,RepairSource.VerifierDecoding.CompareMachine.word] <;> omega

end NearCubicWires.RepairOrdinary.CompetitorPlaneTableInitialize
