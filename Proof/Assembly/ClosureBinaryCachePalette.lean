import Proof.Assembly.ClosureHardwireAssignments
import Proof.MachineModel.NativeFanout

/-! The cold assignment bank has only nine distinct nonblank source words.
Padding the accepted program's private ports collapses all nested scratch
capacities, including D and E, to a single paid fanout capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdPalette
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound ExtIncidence
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline SupplierEstimator
open SignedSortKey VerifierDecoding

variable {q : Nat} (live : Finset (Fin q)) (gs : List (ExactThresholdGate q)) (B w : Nat)
def S := HardwireAssignments.reserve live gs B w (2*live.card)
def U := S live gs B w+1
noncomputable def words : Fin 9→List Bool :=
  ![List.replicate w true,RepairOrdinary.frame (binary w 0),List.replicate (HardwireBudget.C w) true,
    CompareMachine.word q,CloseoutRowsGateSupport.gateMembers live,
    List.replicate (HardwireBudget.R B q w) true,List.replicate B true,
    CompareMachine.word gs.length,List.replicate (S live gs B w) true]
def nativeSelect (i : Fin 48) : Option (Fin 9) :=
  if i=9 then some 0 else if i=13 ∨ i=14 then some 1 else if i=40 then some 2
  else if i=42 ∨ i=46 then some 3 else if i=45 then some 4 else none
def coreSelect : Fin 98→Option (Fin 9) :=
  fun i=>Fin.addCases nativeSelect
    (fun j=>Fin.addCases (fun k : Fin 47=>nativeSelect (HardwireReusable.work k))
      (![none,some 5,none] : Fin 3→Option (Fin 9)) j) i
def baselineSelect : Fin 112→Option (Fin 9) :=
  fun i=>Fin.addCases coreSelect
    (![none,none,some 3,some 6,none,some 7,none,none,none,none,some 3,none,none,none] :
      Fin 14→Option (Fin 9)) i
def select : Fin 224→Option (Fin 9) :=
  fun i=>Fin.addCases
    (fun j=>Fin.addCases baselineSelect
      (fun k=>Fin.addCases (fun a : Fin 108=>baselineSelect (AssignmentRestore.work a))
        (![none,some 8,none] : Fin 3→Option (Fin 9)) k) j)
    (fun _ : Fin 1=>none) i
def caps (U : Nat) (i : Fin 224) := if i=34 ∨ i=98 ∨ i=104 ∨ i=223 then 0 else U

theorem pad_zeros (U n : Nat) (hn : n≤U) :
    ZeroPadding.pad U (List.replicate n false)=ZeroPadding.pad U [] := by
  simp only [ZeroPadding.pad,List.length_replicate,List.length_nil,Nat.sub_zero,List.nil_append]
  rw [←List.replicate_add,Nat.add_sub_of_le hn]

theorem pad_template (U n : Nat) (hn : n+2≤U) :
    ZeroPadding.pad U (UnaryTemplate.tape n)=ZeroPadding.pad U (CompareMachine.word n) := by
  rw [←DecompositionSource.Records.template_pad n]
  exact MatrixBucketRootPower.pad_pad _ _ _ hn

theorem scalar_bounds : HardwireBudget.C w≤U live gs B w ∧
    HardwireBudget.D q w≤U live gs B w ∧ HardwireBudget.E B q≤U live gs B w ∧
    q+2≤U live gs B w ∧ HardwireBudget.R B q w+1≤U live gs B w ∧
    B+1≤U live gs B w ∧ live.card≤U live gs B w ∧ 4*q+3≤U live gs B w ∧
    gs.length+1≤U live gs B w ∧ 2*live.card≤U live gs B w := by
  obtain ⟨_,hR,hN,hB,hK,hq⟩ := HardwireAssignments.reserve_bounds live gs B w (2*live.card)
  have sq := Nat.le_self_pow (by decide : 2≠0) (B+q+w+1)
  have hS : 2*live.card≤S live gs B w := by unfold S HardwireAssignments.reserve;omega
  unfold U S HardwireBudget.D HardwireBudget.C HardwireBudget.E HardwireBudget.R at *
  constructor
  · omega
  constructor
  · nlinarith
  omega

theorem native_pad (out : List Bool) (i : Fin 48) (hi : i≠34) :
    ZeroPadding.pad (U live gs B w)
      (HardwireCacheBody.native live (fun _=>false) [] w (HardwireBudget.C w)
        (HardwireBudget.D q w) (HardwireBudget.E B q) [] out i)=
      ZeroPadding.pad (U live gs B w) (NativeFanout.word nativeSelect (words live gs B w) i) := by
  obtain ⟨hC,hD,hE,hq,_hR,_hB,_hK,_hq4,_hN,_hcap⟩ := scalar_bounds live gs B w
  have hC1 : HardwireBudget.C w+1≤U live gs B w := by
    unfold HardwireBudget.C U S HardwireAssignments.reserve HardwireAssignmentsRaw.budget HardwireBudget.R
    nlinarith [Nat.le_self_pow (by decide : 2≠0) (B+q+w+1)]
  fin_cases i <;> first
    | exact False.elim (hi rfl)
    | skip
  all_goals
    simp only [HardwireCacheBody.native,C10NaturalHardwireScoreInputs.data,
        C10NaturalHardwireScoreInputs.extra,
        
        HardwireChild.extra,
        HardwireAssignmentsRaw.frozen_zero,NativeFanout.word,nativeSelect,words,
        Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,
        Fin.isValue,Fin.reduceEq,↓reduceIte,Option.elim_some,Option.elim_none,or_self,or_false,false_or]
    first
    | rfl
    | exact pad_zeros _ _ hC
    | exact pad_zeros _ _ hC1
    | exact pad_zeros _ _ hD
    | exact pad_zeros _ _ hE
    | exact pad_zeros _ _ (by omega)
    | exact MatrixBucketRootPower.pad_pad _ _ _ hC

theorem core_pad (framed out : List Bool) (i : Fin 98) (hi : i≠34) :
    ZeroPadding.pad (U live gs B w)
      (HardwireAssignments.baseline live gs B w (2*live.card) framed out (HardwireAssignmentsRaw.old i))=
      ZeroPadding.pad (U live gs B w) (NativeFanout.word coreSelect (words live gs B w) i) := by
  simp only [HardwireAssignments.baseline]
  rw [HardwireAssignmentsRaw.baseline_old]
  obtain ⟨_,_,_,_,hR,_,_,_,_,_⟩ := scalar_bounds live gs B w
  revert hi
  refine Fin.addCases (m:=48) (n:=50) (fun i=>?_) (fun i=>?_) i
  · intro hi
    simp only [HardwireCacheBody.localState,HardwireReusable.state,Fin.addCases_left]
    have hx : i≠34 := by intro h;subst i;exact hi rfl
    simp only [HardwireCacheBody.padded,HardwireReusable.caps,hx,↓reduceIte]
    rw [MatrixBucketRootPower.pad_pad _ _ _ (by omega)]
    simpa only [NativeFanout.word,coreSelect,Fin.addCases_left] using native_pad live gs B w out i hx
  · intro _
    simp only [HardwireCacheBody.localState,HardwireReusable.state,Fin.addCases_right]
    refine Fin.addCases (m:=47) (n:=3) (fun j=>?_) (fun j=>?_) i
    · simp only [Fin.addCases_left]
      have hn : ∀ j,HardwireReusable.work j≠34 := by decide
      simpa only [HardwireCacheBody.masters,NativeFanout.word,coreSelect,Fin.addCases_left,Fin.addCases_right]
        using native_pad live gs B w [] (HardwireReusable.work j) (hn j)
    · fin_cases j
      · exact pad_zeros _ _ (by omega)
      · rfl
      · exact pad_zeros _ _ hR

theorem baseline_pad (framed out : List Bool) (i : Fin 112)
    (h34 : i≠34) (h98 : i≠98) (h104 : i≠104) :
    ZeroPadding.pad (U live gs B w)
      (HardwireAssignments.baseline live gs B w (2*live.card) framed out i)=
      ZeroPadding.pad (U live gs B w) (NativeFanout.word baselineSelect (words live gs B w) i) := by
  obtain ⟨_,_,_,hq,_,hB,hK,hq4,_hN,hcap⟩ := scalar_bounds live gs B w
  revert h34 h98 h104
  refine Fin.addCases (m:=98) (n:=14) (fun i=>?_) (fun i=>?_) i
  · intro h34 _ _
    have he : HardwireAssignmentsRaw.old i=i.castAdd 14 := Fin.ext rfl
    simpa only [he,NativeFanout.word,baselineSelect,Fin.addCases_left] using
      core_pad live gs B w framed out i (by intro h;subst i;exact h34 rfl)
  · intro _ h98 h104
    rw [HardwireAssignments.baseline_tail]
    fin_cases i <;> first
      | exact False.elim (h98 rfl)
      | exact False.elim (h104 rfl)
      | rfl
      | exact pad_template _ _ hq
      | exact pad_zeros _ _ hB
      | exact pad_zeros _ _ hK
      | exact pad_zeros _ _ hq4
      | exact pad_zeros _ _ hcap

end NearCubicWires.P1Closure.BinaryCacheColdPalette
