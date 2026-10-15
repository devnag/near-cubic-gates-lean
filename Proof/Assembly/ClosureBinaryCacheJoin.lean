import Proof.Assembly.ClosureBinaryCacheControl
import Proof.Assembly.ClosureBinaryCacheInitialize
import Proof.Assembly.ClosureBinaryCacheHeader
import Proof.Assembly.ClosureBinaryCachePoolCount
import Proof.Assembly.ClosureBinaryCacheMetadata
import Proof.Assembly.ClosureOriginalCacheBounds

/-! Fixed physical cold-cache construction. The finite wiring graph is generated
and checked for aliasing; each read and each complete stage join is checked by
Lean. Initial words are only the ORIGINAL native cache, unary domain/live sizes,
and membership bits. All derived templates and copied banks are computed. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdJoin
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation RepairSource.CloseoutFinal RepairSource.VerifierDecoding SignedSortKey

structure Args (q : Nat) where
  live : Finset (Fin q)
  gs : List (ExactThresholdGate q)
variable {q : Nat}
abbrev Args.L (r : Args q) := (exactListWord r.gs).length
abbrev Args.N (r : Args q) := r.gs.length
abbrev Args.K (r : Args q) := r.live.card
abbrev Args.W (r : Args q) := natBitLength r.N
abbrev Args.B (r : Args q) := r.L+2
abbrev Args.w (r : Args q) := r.L+1
abbrev Args.members (r : Args q) := CloseoutRowsGateSupport.gateMembers r.live
abbrev Args.poolCount (r : Args q) := 2^r.K*r.N+1
abbrev Args.prefix (r : Args q) := BinaryCachePrefix.prefixWord r.poolCount (q-r.K)
theorem Args.card_le (r : Args q) : r.K≤q := by
  simpa using Finset.card_le_univ r.live

theorem of_clock {t s : Nat} {p : Machine t s} {n : Nat} {A B : Fin t→List Bool}
    (h : ClockJoin.ReadyRun p n A B) : Step p n (fun _=>0) A (fun _=>0) B := by
  obtain ⟨actual,hr,ht,hh,_⟩ := h
  exact Step.of_run hr (funext hh) ht

def data0 (r : Args q) : Fin 372→List Bool := fun i=>
  if i=98 then exactListWord r.gs else if i=224 then UnaryTemplate.tape q
  else if i=225 then UnaryTemplate.tape r.K else if i=226 then r.members else []
def heads0 (_r : Args q) : Fin 372→Nat := fun _=>0

noncomputable def measureOutput (r : Args q) := Classical.choose (BinaryCacheColdMeasure.run r.gs)
theorem measure_spec (r : Args q) :
    Step BinaryCacheColdMeasure.machine (BinaryCacheColdMeasure.budget r.gs) (fun _=>0)
      (BinaryCacheColdMeasure.coldInput r.gs) (fun _=>0) (measureOutput r) ∧
    measureOutput r 0=exactListWord r.gs ∧ measureOutput r 10=UnaryTemplate.tape r.N ∧
    measureOutput r 12=UnaryTemplate.tape q ∧ measureOutput r 15=List.replicate r.L true :=
  Classical.choose_spec (BinaryCacheColdMeasure.run r.gs)
noncomputable def binaryScratch (r : Args q) := Classical.choose (BinaryCacheColdControl.binary_run r.K)
theorem binary_spec (r : Args q) :
    Step BinaryCacheColdControl.binaryMachine (BinaryInitialize.budget r.K+5) (fun _=>0)
      (BinaryCacheColdControl.binaryInput r.K) BinaryCacheColdControl.binaryHeads
      (BinaryCacheColdControl.binaryOutput r.K (binaryScratch r)) :=
  Classical.choose_spec (BinaryCacheColdControl.binary_run r.K)

def localInput1 (r : Args q) := BinaryCacheColdMeasure.coldInput r.gs
noncomputable def localOutput1 (r : Args q) := measureOutput r
def localHeadsIn1 (_r : Args q) : Fin 17→Nat := fun _=>0
def localHeadsOut1 (_r : Args q) : Fin 17→Nat := fun _=>0
def localBudget1 (r : Args q) := BinaryCacheColdMeasure.budget r.gs
theorem localStep1 (r : Args q) : Step BinaryCacheColdMeasure.machine (localBudget1 r)
    (localHeadsIn1 r) (localInput1 r) (localHeadsOut1 r) (localOutput1 r) := (measure_spec r).1

def localInput2 (r : Args q) := BinaryCacheColdHeader.input (exactListWord r.gs)
def localOutput2 (r : Args q) := BinaryCacheColdHeader.output r.N (r.gs.flatMap exactWord)
def localHeadsIn2 (_r : Args q) : Fin 7→Nat := fun _=>0
def localHeadsOut2 (_r : Args q) : Fin 7→Nat := fun _=>0
def localBudget2 (r : Args q) := BinaryCacheColdHeader.budget r.N
theorem localStep2 (r : Args q) : Step BinaryCacheColdHeader.machine (localBudget2 r)
    (localHeadsIn2 r) (localInput2 r) (localHeadsOut2 r) (localOutput2 r) :=
  BinaryCacheColdHeader.run r.N (r.gs.flatMap exactWord)

def localInput3 (r : Args q) := BinaryCacheColdMetadata.input r.L q r.N r.K r.W r.members
noncomputable def localOutput3 (r : Args q) := BinaryCacheColdMetadata.output r.L q r.N r.K r.W r.members
def localHeadsIn3 (_r : Args q) : Fin 88→Nat := fun _=>0
def localHeadsOut3 (_r : Args q) : Fin 88→Nat := fun _=>0
def localBudget3 (r : Args q) := BinaryCacheColdMetadata.budget r.L q r.N r.K r.W
theorem localStep3 (r : Args q) : Step BinaryCacheColdMetadata.machine (localBudget3 r)
    (localHeadsIn3 r) (localInput3 r) (localHeadsOut3 r) (localOutput3 r) :=
  of_clock (BinaryCacheColdMetadata.ready r.L q r.N r.K r.W r.members)

def localInput4 (r : Args q) := BinaryCacheColdControl.binaryInput r.K
noncomputable def localOutput4 (r : Args q) := BinaryCacheColdControl.binaryOutput r.K (binaryScratch r)
def localHeadsIn4 (_r : Args q) : Fin 11→Nat := fun _=>0
def localHeadsOut4 (_r : Args q) := BinaryCacheColdControl.binaryHeads
def localBudget4 (r : Args q) := BinaryInitialize.budget r.K+5
theorem localStep4 (r : Args q) : Step BinaryCacheColdControl.binaryMachine (localBudget4 r)
    (localHeadsIn4 r) (localInput4 r) (localHeadsOut4 r) (localOutput4 r) := binary_spec r

def lower := DecompositionCountPosition.move (fun _ : Fin 1=>HeadMove.left)
def localInput5 (r : Args q) : Fin 1→List Bool := fun _=>CompareMachine.word (2^r.K-1)
def localOutput5 (r : Args q) := localInput5 r
def localHeadsIn5 (_r : Args q) : Fin 1→Nat := fun _=>1
def localHeadsOut5 (_r : Args q) : Fin 1→Nat := fun _=>0
def localBudget5 (_r : Args q) := 1
theorem localStep5 (r : Args q) : Step lower (localBudget5 r)
    (localHeadsIn5 r) (localInput5 r) (localHeadsOut5 r) (localOutput5 r) := by
  obtain ⟨actual,hr,hf,_⟩ := DecompositionCountPosition.move_run (fun _ : Fin 1=>HeadMove.left)
    (localHeadsIn5 r) (localInput5 r)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

def localInput6 (r : Args q) := BinaryCacheColdPoolCount.input (2^r.K-1) r.N
def localOutput6 (r : Args q) := BinaryCacheColdPoolCount.output (2^r.K-1) r.N
def localHeadsIn6 (_r : Args q) : Fin 17→Nat := fun _=>0
def localHeadsOut6 (_r : Args q) : Fin 17→Nat := fun _=>0
def localBudget6 (r : Args q) := BinaryCacheColdPoolCount.budget (2^r.K-1) r.N
theorem localStep6 (r : Args q) : Step BinaryCacheColdPoolCount.machine (localBudget6 r)
    (localHeadsIn6 r) (localInput6 r) (localHeadsOut6 r) (localOutput6 r) :=
  of_clock (BinaryCacheColdPoolCount.run (2^r.K-1) r.N)

def localInput7 (r : Args q) := MatrixUnaryDifference.resetInput q r.K
noncomputable def localOutput7 (r : Args q) := BinaryCacheColdControl.differenceOutput q r.K r.card_le
def localHeadsIn7 (_r : Args q) : Fin 4→Nat := fun _=>0
def localHeadsOut7 (_r : Args q) : Fin 4→Nat := fun _=>0
def localBudget7 (_r : Args q) := 2*q+8
theorem localStep7 (r : Args q) : Step MatrixUnaryDifference.resetMachine (localBudget7 r)
    (localHeadsIn7 r) (localInput7 r) (localHeadsOut7 r) (localOutput7 r) :=
  (BinaryCacheColdControl.difference_spec q r.K r.card_le).1

def raise := DecompositionCountPosition.move (fun _ : Fin 2=>HeadMove.right)
def localInput8 (r : Args q) : Fin 2→List Bool :=
  ![CompareMachine.word (2^r.K-1),UnaryTemplate.tape (q-r.K)]
def localOutput8 (r : Args q) := localInput8 r
def localHeadsIn8 (_r : Args q) : Fin 2→Nat := fun _=>0
def localHeadsOut8 (_r : Args q) : Fin 2→Nat := fun _=>1
def localBudget8 (_r : Args q) := 1
theorem localStep8 (r : Args q) : Step raise (localBudget8 r)
    (localHeadsIn8 r) (localInput8 r) (localHeadsOut8 r) (localOutput8 r) := by
  obtain ⟨actual,hr,hf,_⟩ := DecompositionCountPosition.move_run (fun _ : Fin 2=>HeadMove.right)
    (localHeadsIn8 r) (localInput8 r)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

def localInput9 (r : Args q) := BinaryCacheColdControl.prefixInput r.poolCount (q-r.K) []
noncomputable def localOutput9 (r : Args q) := BinaryCacheColdControl.prefixOutput r.poolCount (q-r.K) []
def localHeadsIn9 (_r : Args q) := BinaryCachePrefix.inputHeads []
noncomputable def localHeadsOut9 (r : Args q) :=
  BinaryCachePrefix.replace (BinaryCachePrefix.headerHeads r.poolCount []) r.prefix.length
def localBudget9 (r : Args q) := BinaryCachePrefix.budget r.poolCount (q-r.K)
theorem localStep9 (r : Args q) : Step BinaryCachePrefix.machine (localBudget9 r)
    (localHeadsIn9 r) (localInput9 r) (localHeadsOut9 r) (localOutput9 r) :=
  BinaryCacheColdControl.prefix_run r.poolCount (q-r.K) []

noncomputable def localInput10 (r : Args q) := BinaryCacheColdInitialize.input r.live r.gs r.B r.w r.prefix
noncomputable def localOutput10 (r : Args q) :=
  BinaryCacheColdInitialize.output r.live r.gs r.B r.w (2^r.K-1) (r.prefix++HardwireAssignments.emitted r.live r.gs)
def localHeadsIn10 (r : Args q) := BinaryCacheColdInitialize.heads r.prefix
noncomputable def localHeadsOut10 (r : Args q) := BinaryCacheColdInitialize.heads (r.prefix++HardwireAssignments.emitted r.live r.gs)
def localBudget10 (r : Args q) := BinaryCacheColdInitialize.budget r.live r.gs r.B r.w
theorem localStep10 (r : Args q) : Step BinaryCacheColdInitialize.machine (localBudget10 r)
    (localHeadsIn10 r) (localInput10 r) (localHeadsOut10 r) (localOutput10 r) :=
  BinaryCacheColdInitialize.run r.live r.gs r.B r.w (OriginalCacheBounds.bytes r.gs)
    (by change 0<r.L+1;omega) (OriginalCacheBounds.magnitude r.gs) r.prefix

theorem projection1_0 (r : Args q) : localOutput1 r 0=exactListWord r.gs := by
  exact (measure_spec r).2.1

theorem projection1_10 (r : Args q) : localOutput1 r 10=UnaryTemplate.tape r.N := by
  exact (measure_spec r).2.2.1

theorem projection1_12 (r : Args q) : localOutput1 r 12=UnaryTemplate.tape q := by
  exact (measure_spec r).2.2.2.1

theorem projection1_15 (r : Args q) : localOutput1 r 15=List.replicate r.L true := by
  exact (measure_spec r).2.2.2.2

theorem projection2_0 (r : Args q) : localOutput2 r 0=exactListWord r.gs := by
  rfl

theorem projection2_1 (r : Args q) : localOutput2 r 1=List.replicate r.W true := by
  rfl

theorem projection3_0 (r : Args q) : localOutput3 r 0=List.replicate r.L true := by
  exact BinaryCacheColdMetadata.retained r.L q r.N r.K r.W r.members 0

theorem projection3_1 (r : Args q) : localOutput3 r 1=UnaryTemplate.tape q := by
  exact BinaryCacheColdMetadata.retained r.L q r.N r.K r.W r.members 1

theorem projection3_2 (r : Args q) : localOutput3 r 2=UnaryTemplate.tape r.N := by
  exact BinaryCacheColdMetadata.retained r.L q r.N r.K r.W r.members 2

theorem projection3_3 (r : Args q) : localOutput3 r 3=UnaryTemplate.tape r.K := by
  exact BinaryCacheColdMetadata.retained r.L q r.N r.K r.W r.members 3

theorem projection3_4 (r : Args q) : localOutput3 r 4=List.replicate r.W true := by
  exact BinaryCacheColdMetadata.retained r.L q r.N r.K r.W r.members 4

theorem projection3_5 (r : Args q) : localOutput3 r 5=BinaryCacheColdPalette.words r.live r.gs r.B r.w 4 := by
  exact (BinaryCacheColdMetadata.output_fields r.L q r.N r.K r.W r.members 4).trans
    (congrFun (BinaryCacheColdParameters.words_eq r.live r.gs r.L) 4)

theorem projection3_20 (r : Args q) : localOutput3 r 20=CompareMachine.word r.K := by
  exact BinaryCacheColdMetadata.output_compareK r.L q r.N r.K r.W r.members

theorem projection3_82 (r : Args q) : localOutput3 r 82=List.replicate (BinaryCacheColdPalette.U r.live r.gs r.B r.w) true := by
  exact (BinaryCacheColdMetadata.output_capacity r.L q r.N r.K r.W r.members).trans
    (congrArg (fun n=>List.replicate n true) (BinaryCacheColdParameters.capacity_eq r.live r.gs r.L))

theorem projection3_8 (r : Args q) : localOutput3 r 8=BinaryCacheColdPalette.words r.live r.gs r.B r.w 0 := by
  exact (BinaryCacheColdMetadata.output_fields r.L q r.N r.K r.W r.members 0).trans
    (congrFun (BinaryCacheColdParameters.words_eq r.live r.gs r.L) 0)

theorem projection3_85 (r : Args q) : localOutput3 r 85=BinaryCacheColdPalette.words r.live r.gs r.B r.w 1 := by
  exact (BinaryCacheColdMetadata.output_fields r.L q r.N r.K r.W r.members 1).trans
    (congrFun (BinaryCacheColdParameters.words_eq r.live r.gs r.L) 1)

theorem projection3_42 (r : Args q) : localOutput3 r 42=BinaryCacheColdPalette.words r.live r.gs r.B r.w 2 := by
  exact (BinaryCacheColdMetadata.output_fields r.L q r.N r.K r.W r.members 2).trans
    (congrFun (BinaryCacheColdParameters.words_eq r.live r.gs r.L) 2)

theorem projection3_16 (r : Args q) : localOutput3 r 16=BinaryCacheColdPalette.words r.live r.gs r.B r.w 3 := by
  exact (BinaryCacheColdMetadata.output_fields r.L q r.N r.K r.W r.members 3).trans
    (congrFun (BinaryCacheColdParameters.words_eq r.live r.gs r.L) 3)

theorem projection3_34 (r : Args q) : localOutput3 r 34=BinaryCacheColdPalette.words r.live r.gs r.B r.w 5 := by
  exact (BinaryCacheColdMetadata.output_fields r.L q r.N r.K r.W r.members 5).trans
    (congrFun (BinaryCacheColdParameters.words_eq r.live r.gs r.L) 5)

theorem projection3_10 (r : Args q) : localOutput3 r 10=BinaryCacheColdPalette.words r.live r.gs r.B r.w 6 := by
  exact (BinaryCacheColdMetadata.output_fields r.L q r.N r.K r.W r.members 6).trans
    (congrFun (BinaryCacheColdParameters.words_eq r.live r.gs r.L) 6)

theorem projection3_18 (r : Args q) : localOutput3 r 18=BinaryCacheColdPalette.words r.live r.gs r.B r.w 7 := by
  exact (BinaryCacheColdMetadata.output_fields r.L q r.N r.K r.W r.members 7).trans
    (congrFun (BinaryCacheColdParameters.words_eq r.live r.gs r.L) 7)

theorem projection3_80 (r : Args q) : localOutput3 r 80=BinaryCacheColdPalette.words r.live r.gs r.B r.w 8 := by
  exact (BinaryCacheColdMetadata.output_fields r.L q r.N r.K r.W r.members 8).trans
    (congrFun (BinaryCacheColdParameters.words_eq r.live r.gs r.L) 8)

theorem projection4_4 (r : Args q) : localOutput4 r 4=CompareMachine.word (2^r.K-1) := by
  rfl

theorem projection4_8 (r : Args q) : localOutput4 r 8=RepairOrdinary.frame (binary r.K 0) := by
  rfl

theorem projection5_0 (r : Args q) : localOutput5 r 0=CompareMachine.word (2^r.K-1) := by
  rfl

theorem projection6_0 (r : Args q) : localOutput6 r 0=CompareMachine.word (2^r.K-1) := by
  rfl

theorem projection6_1 (r : Args q) : localOutput6 r 1=UnaryTemplate.tape r.N := by
  rfl

theorem projection6_8 (r : Args q) : localOutput6 r 8=List.replicate r.poolCount true := by
  exact BinaryCacheColdPoolCount.binary_output r.K r.N

theorem projection7_0 (r : Args q) : localOutput7 r 0=UnaryTemplate.tape q := by
  exact (BinaryCacheColdControl.difference_spec q r.K r.card_le).2.1

theorem projection7_1 (r : Args q) : localOutput7 r 1=UnaryTemplate.tape r.K := by
  exact (BinaryCacheColdControl.difference_spec q r.K r.card_le).2.2.1

theorem projection7_2 (r : Args q) : localOutput7 r 2=UnaryTemplate.tape (q-r.K) := by
  exact (BinaryCacheColdControl.difference_spec q r.K r.card_le).2.2.2

theorem projection8_0 (r : Args q) : localOutput8 r 0=CompareMachine.word (2^r.K-1) := by
  rfl

theorem projection8_1 (r : Args q) : localOutput8 r 1=UnaryTemplate.tape (q-r.K) := by
  rfl

theorem projection9_17 (r : Args q) : localOutput9 r 17=r.prefix := by
  exact ZeroPadding.pad_zero r.prefix

theorem projection10_34 (r : Args q) : localOutput10 r 34=r.prefix++HardwireAssignments.emitted r.live r.gs := by
  rfl

theorem projection10_98 (r : Args q) : localOutput10 r 98=exactListWord r.gs := by
  rfl

def slots1 : Fin 17→Fin 372 := ![98,227,228,229,230,231,232,233,234,235,236,237,224,238,239,240,241]
theorem slots1_inj : Function.Injective slots1 := by decide
noncomputable def phase1 := RecoveryFocus.machine slots1 BinaryCacheColdMeasure.machine
noncomputable def data1 (r : Args q) := install slots1 (data0 r) (localOutput1 r)
noncomputable def heads1 (r : Args q) := dockH slots1 (heads0 r) (localHeadsOut1 r)
theorem data1_slot (r : Args q) (j : Fin 17) : data1 r (slots1 j)=localOutput1 r j :=
  install_slot slots1 slots1_inj _ _ j
theorem data1_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots1 j≠k) : data1 r k=data0 r k :=
  install_other slots1 _ _ k hk
theorem heads1_slot (r : Args q) (j : Fin 17) : heads1 r (slots1 j)=localHeadsOut1 r j :=
  dockH_slot slots1 slots1_inj _ _ j
theorem heads1_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots1 j≠k) : heads1 r k=heads0 r k :=
  dockH_other slots1 _ _ k hk

theorem heads1_input (r : Args q) : ∀ j,heads0 r (slots1 j)=localHeadsIn1 r j := by
  intro j
  fin_cases j
  · change heads0 r 98=localHeadsIn1 r 0
    rfl
  · change heads0 r 227=localHeadsIn1 r 1
    rfl
  · change heads0 r 228=localHeadsIn1 r 2
    rfl
  · change heads0 r 229=localHeadsIn1 r 3
    rfl
  · change heads0 r 230=localHeadsIn1 r 4
    rfl
  · change heads0 r 231=localHeadsIn1 r 5
    rfl
  · change heads0 r 232=localHeadsIn1 r 6
    rfl
  · change heads0 r 233=localHeadsIn1 r 7
    rfl
  · change heads0 r 234=localHeadsIn1 r 8
    rfl
  · change heads0 r 235=localHeadsIn1 r 9
    rfl
  · change heads0 r 236=localHeadsIn1 r 10
    rfl
  · change heads0 r 237=localHeadsIn1 r 11
    rfl
  · change heads0 r 224=localHeadsIn1 r 12
    rfl
  · change heads0 r 238=localHeadsIn1 r 13
    rfl
  · change heads0 r 239=localHeadsIn1 r 14
    rfl
  · change heads0 r 240=localHeadsIn1 r 15
    rfl
  · change heads0 r 241=localHeadsIn1 r 16
    rfl

theorem data1_input (r : Args q) : ∀ j,data0 r (slots1 j)=localInput1 r j := by
  intro j
  fin_cases j
  · change data0 r 98=localInput1 r 0
    rfl
  · change data0 r 227=localInput1 r 1
    rfl
  · change data0 r 228=localInput1 r 2
    rfl
  · change data0 r 229=localInput1 r 3
    rfl
  · change data0 r 230=localInput1 r 4
    rfl
  · change data0 r 231=localInput1 r 5
    rfl
  · change data0 r 232=localInput1 r 6
    rfl
  · change data0 r 233=localInput1 r 7
    rfl
  · change data0 r 234=localInput1 r 8
    rfl
  · change data0 r 235=localInput1 r 9
    rfl
  · change data0 r 236=localInput1 r 10
    rfl
  · change data0 r 237=localInput1 r 11
    rfl
  · change data0 r 224=localInput1 r 12
    rfl
  · change data0 r 238=localInput1 r 13
    rfl
  · change data0 r 239=localInput1 r 14
    rfl
  · change data0 r 240=localInput1 r 15
    rfl
  · change data0 r 241=localInput1 r 16
    rfl

theorem step1 (r : Args q) : Step phase1 (localBudget1 r)
    (heads0 r) (data0 r) (heads1 r) (data1 r) :=
  (localStep1 r).dock slots1 slots1_inj (heads0 r) (data0 r) (heads1_input r) (data1_input r)
noncomputable def joined1 := phase1
def budget1 (r : Args q) := localBudget1 r
theorem joined1_run (r : Args q) : Step joined1 (budget1 r) (heads0 r) (data0 r) (heads1 r) (data1 r) := step1 r

def slots2 : Fin 7→Fin 372 := ![98,242,243,244,245,246,247]
theorem slots2_inj : Function.Injective slots2 := by decide
noncomputable def phase2 := RecoveryFocus.machine slots2 BinaryCacheColdHeader.machine
noncomputable def data2 (r : Args q) := install slots2 (data1 r) (localOutput2 r)
noncomputable def heads2 (r : Args q) := dockH slots2 (heads1 r) (localHeadsOut2 r)
theorem data2_slot (r : Args q) (j : Fin 7) : data2 r (slots2 j)=localOutput2 r j :=
  install_slot slots2 slots2_inj _ _ j
theorem data2_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots2 j≠k) : data2 r k=data1 r k :=
  install_other slots2 _ _ k hk
theorem heads2_slot (r : Args q) (j : Fin 7) : heads2 r (slots2 j)=localHeadsOut2 r j :=
  dockH_slot slots2 slots2_inj _ _ j
theorem heads2_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots2 j≠k) : heads2 r k=heads1 r k :=
  dockH_other slots2 _ _ k hk

theorem heads2_input (r : Args q) : ∀ j,heads1 r (slots2 j)=localHeadsIn2 r j := by
  intro j
  fin_cases j
  · change heads1 r 98=localHeadsIn2 r 0
    rw [show heads1 r 98=localHeadsOut1 r 0 from heads1_slot r 0]
    rfl
  · change heads1 r 242=localHeadsIn2 r 1
    rw [heads1_other r 242 (by decide)]
    rfl
  · change heads1 r 243=localHeadsIn2 r 2
    rw [heads1_other r 243 (by decide)]
    rfl
  · change heads1 r 244=localHeadsIn2 r 3
    rw [heads1_other r 244 (by decide)]
    rfl
  · change heads1 r 245=localHeadsIn2 r 4
    rw [heads1_other r 245 (by decide)]
    rfl
  · change heads1 r 246=localHeadsIn2 r 5
    rw [heads1_other r 246 (by decide)]
    rfl
  · change heads1 r 247=localHeadsIn2 r 6
    rw [heads1_other r 247 (by decide)]
    rfl

theorem data2_input (r : Args q) : ∀ j,data1 r (slots2 j)=localInput2 r j := by
  intro j
  fin_cases j
  · change data1 r 98=localInput2 r 0
    rw [show data1 r 98=localOutput1 r 0 from data1_slot r 0]
    rw [projection1_0]
    rfl
  · change data1 r 242=localInput2 r 1
    rw [data1_other r 242 (by decide)]
    rfl
  · change data1 r 243=localInput2 r 2
    rw [data1_other r 243 (by decide)]
    rfl
  · change data1 r 244=localInput2 r 3
    rw [data1_other r 244 (by decide)]
    rfl
  · change data1 r 245=localInput2 r 4
    rw [data1_other r 245 (by decide)]
    rfl
  · change data1 r 246=localInput2 r 5
    rw [data1_other r 246 (by decide)]
    rfl
  · change data1 r 247=localInput2 r 6
    rw [data1_other r 247 (by decide)]
    rfl

theorem step2 (r : Args q) : Step phase2 (localBudget2 r)
    (heads1 r) (data1 r) (heads2 r) (data2 r) :=
  (localStep2 r).dock slots2 slots2_inj (heads1 r) (data1 r) (heads2_input r) (data2_input r)
noncomputable def joined2 := Composition.machine joined1 phase2
def budget2 (r : Args q) := budget1 r+1+localBudget2 r
theorem joined2_run (r : Args q) : Step joined2 (budget2 r) (heads0 r) (data0 r) (heads2 r) (data2 r) :=
  (joined1_run r).seq (step2 r)

def slots3 : Fin 88→Fin 372 := ![240,224,236,225,242,226,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329]
theorem slots3_inj : Function.Injective slots3 := by decide
noncomputable def phase3 := RecoveryFocus.machine slots3 BinaryCacheColdMetadata.machine
noncomputable def data3 (r : Args q) := install slots3 (data2 r) (localOutput3 r)
noncomputable def heads3 (r : Args q) := dockH slots3 (heads2 r) (localHeadsOut3 r)
theorem data3_slot (r : Args q) (j : Fin 88) : data3 r (slots3 j)=localOutput3 r j :=
  install_slot slots3 slots3_inj _ _ j
theorem data3_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots3 j≠k) : data3 r k=data2 r k :=
  install_other slots3 _ _ k hk
theorem heads3_slot (r : Args q) (j : Fin 88) : heads3 r (slots3 j)=localHeadsOut3 r j :=
  dockH_slot slots3 slots3_inj _ _ j
theorem heads3_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots3 j≠k) : heads3 r k=heads2 r k :=
  dockH_other slots3 _ _ k hk

theorem heads3_input (r : Args q) : ∀ j,heads2 r (slots3 j)=localHeadsIn3 r j := by
  intro j
  fin_cases j
  · change heads2 r 240=localHeadsIn3 r 0
    rw [heads2_other r 240 (by decide)]
    rw [show heads1 r 240=localHeadsOut1 r 15 from heads1_slot r 15]
    rfl
  · change heads2 r 224=localHeadsIn3 r 1
    rw [heads2_other r 224 (by decide)]
    rw [show heads1 r 224=localHeadsOut1 r 12 from heads1_slot r 12]
    rfl
  · change heads2 r 236=localHeadsIn3 r 2
    rw [heads2_other r 236 (by decide)]
    rw [show heads1 r 236=localHeadsOut1 r 10 from heads1_slot r 10]
    rfl
  · change heads2 r 225=localHeadsIn3 r 3
    rw [heads2_other r 225 (by decide)]
    rw [heads1_other r 225 (by decide)]
    rfl
  · change heads2 r 242=localHeadsIn3 r 4
    rw [show heads2 r 242=localHeadsOut2 r 1 from heads2_slot r 1]
    rfl
  · change heads2 r 226=localHeadsIn3 r 5
    rw [heads2_other r 226 (by decide)]
    rw [heads1_other r 226 (by decide)]
    rfl
  · change heads2 r 248=localHeadsIn3 r 6
    rw [heads2_other r 248 (by decide)]
    rw [heads1_other r 248 (by decide)]
    rfl
  · change heads2 r 249=localHeadsIn3 r 7
    rw [heads2_other r 249 (by decide)]
    rw [heads1_other r 249 (by decide)]
    rfl
  · change heads2 r 250=localHeadsIn3 r 8
    rw [heads2_other r 250 (by decide)]
    rw [heads1_other r 250 (by decide)]
    rfl
  · change heads2 r 251=localHeadsIn3 r 9
    rw [heads2_other r 251 (by decide)]
    rw [heads1_other r 251 (by decide)]
    rfl
  · change heads2 r 252=localHeadsIn3 r 10
    rw [heads2_other r 252 (by decide)]
    rw [heads1_other r 252 (by decide)]
    rfl
  · change heads2 r 253=localHeadsIn3 r 11
    rw [heads2_other r 253 (by decide)]
    rw [heads1_other r 253 (by decide)]
    rfl
  · change heads2 r 254=localHeadsIn3 r 12
    rw [heads2_other r 254 (by decide)]
    rw [heads1_other r 254 (by decide)]
    rfl
  · change heads2 r 255=localHeadsIn3 r 13
    rw [heads2_other r 255 (by decide)]
    rw [heads1_other r 255 (by decide)]
    rfl
  · change heads2 r 256=localHeadsIn3 r 14
    rw [heads2_other r 256 (by decide)]
    rw [heads1_other r 256 (by decide)]
    rfl
  · change heads2 r 257=localHeadsIn3 r 15
    rw [heads2_other r 257 (by decide)]
    rw [heads1_other r 257 (by decide)]
    rfl
  · change heads2 r 258=localHeadsIn3 r 16
    rw [heads2_other r 258 (by decide)]
    rw [heads1_other r 258 (by decide)]
    rfl
  · change heads2 r 259=localHeadsIn3 r 17
    rw [heads2_other r 259 (by decide)]
    rw [heads1_other r 259 (by decide)]
    rfl
  · change heads2 r 260=localHeadsIn3 r 18
    rw [heads2_other r 260 (by decide)]
    rw [heads1_other r 260 (by decide)]
    rfl
  · change heads2 r 261=localHeadsIn3 r 19
    rw [heads2_other r 261 (by decide)]
    rw [heads1_other r 261 (by decide)]
    rfl
  · change heads2 r 262=localHeadsIn3 r 20
    rw [heads2_other r 262 (by decide)]
    rw [heads1_other r 262 (by decide)]
    rfl
  · change heads2 r 263=localHeadsIn3 r 21
    rw [heads2_other r 263 (by decide)]
    rw [heads1_other r 263 (by decide)]
    rfl
  · change heads2 r 264=localHeadsIn3 r 22
    rw [heads2_other r 264 (by decide)]
    rw [heads1_other r 264 (by decide)]
    rfl
  · change heads2 r 265=localHeadsIn3 r 23
    rw [heads2_other r 265 (by decide)]
    rw [heads1_other r 265 (by decide)]
    rfl
  · change heads2 r 266=localHeadsIn3 r 24
    rw [heads2_other r 266 (by decide)]
    rw [heads1_other r 266 (by decide)]
    rfl
  · change heads2 r 267=localHeadsIn3 r 25
    rw [heads2_other r 267 (by decide)]
    rw [heads1_other r 267 (by decide)]
    rfl
  · change heads2 r 268=localHeadsIn3 r 26
    rw [heads2_other r 268 (by decide)]
    rw [heads1_other r 268 (by decide)]
    rfl
  · change heads2 r 269=localHeadsIn3 r 27
    rw [heads2_other r 269 (by decide)]
    rw [heads1_other r 269 (by decide)]
    rfl
  · change heads2 r 270=localHeadsIn3 r 28
    rw [heads2_other r 270 (by decide)]
    rw [heads1_other r 270 (by decide)]
    rfl
  · change heads2 r 271=localHeadsIn3 r 29
    rw [heads2_other r 271 (by decide)]
    rw [heads1_other r 271 (by decide)]
    rfl
  · change heads2 r 272=localHeadsIn3 r 30
    rw [heads2_other r 272 (by decide)]
    rw [heads1_other r 272 (by decide)]
    rfl
  · change heads2 r 273=localHeadsIn3 r 31
    rw [heads2_other r 273 (by decide)]
    rw [heads1_other r 273 (by decide)]
    rfl
  · change heads2 r 274=localHeadsIn3 r 32
    rw [heads2_other r 274 (by decide)]
    rw [heads1_other r 274 (by decide)]
    rfl
  · change heads2 r 275=localHeadsIn3 r 33
    rw [heads2_other r 275 (by decide)]
    rw [heads1_other r 275 (by decide)]
    rfl
  · change heads2 r 276=localHeadsIn3 r 34
    rw [heads2_other r 276 (by decide)]
    rw [heads1_other r 276 (by decide)]
    rfl
  · change heads2 r 277=localHeadsIn3 r 35
    rw [heads2_other r 277 (by decide)]
    rw [heads1_other r 277 (by decide)]
    rfl
  · change heads2 r 278=localHeadsIn3 r 36
    rw [heads2_other r 278 (by decide)]
    rw [heads1_other r 278 (by decide)]
    rfl
  · change heads2 r 279=localHeadsIn3 r 37
    rw [heads2_other r 279 (by decide)]
    rw [heads1_other r 279 (by decide)]
    rfl
  · change heads2 r 280=localHeadsIn3 r 38
    rw [heads2_other r 280 (by decide)]
    rw [heads1_other r 280 (by decide)]
    rfl
  · change heads2 r 281=localHeadsIn3 r 39
    rw [heads2_other r 281 (by decide)]
    rw [heads1_other r 281 (by decide)]
    rfl
  · change heads2 r 282=localHeadsIn3 r 40
    rw [heads2_other r 282 (by decide)]
    rw [heads1_other r 282 (by decide)]
    rfl
  · change heads2 r 283=localHeadsIn3 r 41
    rw [heads2_other r 283 (by decide)]
    rw [heads1_other r 283 (by decide)]
    rfl
  · change heads2 r 284=localHeadsIn3 r 42
    rw [heads2_other r 284 (by decide)]
    rw [heads1_other r 284 (by decide)]
    rfl
  · change heads2 r 285=localHeadsIn3 r 43
    rw [heads2_other r 285 (by decide)]
    rw [heads1_other r 285 (by decide)]
    rfl
  · change heads2 r 286=localHeadsIn3 r 44
    rw [heads2_other r 286 (by decide)]
    rw [heads1_other r 286 (by decide)]
    rfl
  · change heads2 r 287=localHeadsIn3 r 45
    rw [heads2_other r 287 (by decide)]
    rw [heads1_other r 287 (by decide)]
    rfl
  · change heads2 r 288=localHeadsIn3 r 46
    rw [heads2_other r 288 (by decide)]
    rw [heads1_other r 288 (by decide)]
    rfl
  · change heads2 r 289=localHeadsIn3 r 47
    rw [heads2_other r 289 (by decide)]
    rw [heads1_other r 289 (by decide)]
    rfl
  · change heads2 r 290=localHeadsIn3 r 48
    rw [heads2_other r 290 (by decide)]
    rw [heads1_other r 290 (by decide)]
    rfl
  · change heads2 r 291=localHeadsIn3 r 49
    rw [heads2_other r 291 (by decide)]
    rw [heads1_other r 291 (by decide)]
    rfl
  · change heads2 r 292=localHeadsIn3 r 50
    rw [heads2_other r 292 (by decide)]
    rw [heads1_other r 292 (by decide)]
    rfl
  · change heads2 r 293=localHeadsIn3 r 51
    rw [heads2_other r 293 (by decide)]
    rw [heads1_other r 293 (by decide)]
    rfl
  · change heads2 r 294=localHeadsIn3 r 52
    rw [heads2_other r 294 (by decide)]
    rw [heads1_other r 294 (by decide)]
    rfl
  · change heads2 r 295=localHeadsIn3 r 53
    rw [heads2_other r 295 (by decide)]
    rw [heads1_other r 295 (by decide)]
    rfl
  · change heads2 r 296=localHeadsIn3 r 54
    rw [heads2_other r 296 (by decide)]
    rw [heads1_other r 296 (by decide)]
    rfl
  · change heads2 r 297=localHeadsIn3 r 55
    rw [heads2_other r 297 (by decide)]
    rw [heads1_other r 297 (by decide)]
    rfl
  · change heads2 r 298=localHeadsIn3 r 56
    rw [heads2_other r 298 (by decide)]
    rw [heads1_other r 298 (by decide)]
    rfl
  · change heads2 r 299=localHeadsIn3 r 57
    rw [heads2_other r 299 (by decide)]
    rw [heads1_other r 299 (by decide)]
    rfl
  · change heads2 r 300=localHeadsIn3 r 58
    rw [heads2_other r 300 (by decide)]
    rw [heads1_other r 300 (by decide)]
    rfl
  · change heads2 r 301=localHeadsIn3 r 59
    rw [heads2_other r 301 (by decide)]
    rw [heads1_other r 301 (by decide)]
    rfl
  · change heads2 r 302=localHeadsIn3 r 60
    rw [heads2_other r 302 (by decide)]
    rw [heads1_other r 302 (by decide)]
    rfl
  · change heads2 r 303=localHeadsIn3 r 61
    rw [heads2_other r 303 (by decide)]
    rw [heads1_other r 303 (by decide)]
    rfl
  · change heads2 r 304=localHeadsIn3 r 62
    rw [heads2_other r 304 (by decide)]
    rw [heads1_other r 304 (by decide)]
    rfl
  · change heads2 r 305=localHeadsIn3 r 63
    rw [heads2_other r 305 (by decide)]
    rw [heads1_other r 305 (by decide)]
    rfl
  · change heads2 r 306=localHeadsIn3 r 64
    rw [heads2_other r 306 (by decide)]
    rw [heads1_other r 306 (by decide)]
    rfl
  · change heads2 r 307=localHeadsIn3 r 65
    rw [heads2_other r 307 (by decide)]
    rw [heads1_other r 307 (by decide)]
    rfl
  · change heads2 r 308=localHeadsIn3 r 66
    rw [heads2_other r 308 (by decide)]
    rw [heads1_other r 308 (by decide)]
    rfl
  · change heads2 r 309=localHeadsIn3 r 67
    rw [heads2_other r 309 (by decide)]
    rw [heads1_other r 309 (by decide)]
    rfl
  · change heads2 r 310=localHeadsIn3 r 68
    rw [heads2_other r 310 (by decide)]
    rw [heads1_other r 310 (by decide)]
    rfl
  · change heads2 r 311=localHeadsIn3 r 69
    rw [heads2_other r 311 (by decide)]
    rw [heads1_other r 311 (by decide)]
    rfl
  · change heads2 r 312=localHeadsIn3 r 70
    rw [heads2_other r 312 (by decide)]
    rw [heads1_other r 312 (by decide)]
    rfl
  · change heads2 r 313=localHeadsIn3 r 71
    rw [heads2_other r 313 (by decide)]
    rw [heads1_other r 313 (by decide)]
    rfl
  · change heads2 r 314=localHeadsIn3 r 72
    rw [heads2_other r 314 (by decide)]
    rw [heads1_other r 314 (by decide)]
    rfl
  · change heads2 r 315=localHeadsIn3 r 73
    rw [heads2_other r 315 (by decide)]
    rw [heads1_other r 315 (by decide)]
    rfl
  · change heads2 r 316=localHeadsIn3 r 74
    rw [heads2_other r 316 (by decide)]
    rw [heads1_other r 316 (by decide)]
    rfl
  · change heads2 r 317=localHeadsIn3 r 75
    rw [heads2_other r 317 (by decide)]
    rw [heads1_other r 317 (by decide)]
    rfl
  · change heads2 r 318=localHeadsIn3 r 76
    rw [heads2_other r 318 (by decide)]
    rw [heads1_other r 318 (by decide)]
    rfl
  · change heads2 r 319=localHeadsIn3 r 77
    rw [heads2_other r 319 (by decide)]
    rw [heads1_other r 319 (by decide)]
    rfl
  · change heads2 r 320=localHeadsIn3 r 78
    rw [heads2_other r 320 (by decide)]
    rw [heads1_other r 320 (by decide)]
    rfl
  · change heads2 r 321=localHeadsIn3 r 79
    rw [heads2_other r 321 (by decide)]
    rw [heads1_other r 321 (by decide)]
    rfl
  · change heads2 r 322=localHeadsIn3 r 80
    rw [heads2_other r 322 (by decide)]
    rw [heads1_other r 322 (by decide)]
    rfl
  · change heads2 r 323=localHeadsIn3 r 81
    rw [heads2_other r 323 (by decide)]
    rw [heads1_other r 323 (by decide)]
    rfl
  · change heads2 r 324=localHeadsIn3 r 82
    rw [heads2_other r 324 (by decide)]
    rw [heads1_other r 324 (by decide)]
    rfl
  · change heads2 r 325=localHeadsIn3 r 83
    rw [heads2_other r 325 (by decide)]
    rw [heads1_other r 325 (by decide)]
    rfl
  · change heads2 r 326=localHeadsIn3 r 84
    rw [heads2_other r 326 (by decide)]
    rw [heads1_other r 326 (by decide)]
    rfl
  · change heads2 r 327=localHeadsIn3 r 85
    rw [heads2_other r 327 (by decide)]
    rw [heads1_other r 327 (by decide)]
    rfl
  · change heads2 r 328=localHeadsIn3 r 86
    rw [heads2_other r 328 (by decide)]
    rw [heads1_other r 328 (by decide)]
    rfl
  · change heads2 r 329=localHeadsIn3 r 87
    rw [heads2_other r 329 (by decide)]
    rw [heads1_other r 329 (by decide)]
    rfl

theorem data3_input (r : Args q) : ∀ j,data2 r (slots3 j)=localInput3 r j := by
  intro j
  fin_cases j
  · change data2 r 240=localInput3 r 0
    rw [data2_other r 240 (by decide)]
    rw [show data1 r 240=localOutput1 r 15 from data1_slot r 15]
    rw [projection1_15]
    rfl
  · change data2 r 224=localInput3 r 1
    rw [data2_other r 224 (by decide)]
    rw [show data1 r 224=localOutput1 r 12 from data1_slot r 12]
    rw [projection1_12]
    rfl
  · change data2 r 236=localInput3 r 2
    rw [data2_other r 236 (by decide)]
    rw [show data1 r 236=localOutput1 r 10 from data1_slot r 10]
    rw [projection1_10]
    rfl
  · change data2 r 225=localInput3 r 3
    rw [data2_other r 225 (by decide)]
    rw [data1_other r 225 (by decide)]
    rfl
  · change data2 r 242=localInput3 r 4
    rw [show data2 r 242=localOutput2 r 1 from data2_slot r 1]
    rw [projection2_1]
    rfl
  · change data2 r 226=localInput3 r 5
    rw [data2_other r 226 (by decide)]
    rw [data1_other r 226 (by decide)]
    rfl
  · change data2 r 248=localInput3 r 6
    rw [data2_other r 248 (by decide)]
    rw [data1_other r 248 (by decide)]
    rfl
  · change data2 r 249=localInput3 r 7
    rw [data2_other r 249 (by decide)]
    rw [data1_other r 249 (by decide)]
    rfl
  · change data2 r 250=localInput3 r 8
    rw [data2_other r 250 (by decide)]
    rw [data1_other r 250 (by decide)]
    rfl
  · change data2 r 251=localInput3 r 9
    rw [data2_other r 251 (by decide)]
    rw [data1_other r 251 (by decide)]
    rfl
  · change data2 r 252=localInput3 r 10
    rw [data2_other r 252 (by decide)]
    rw [data1_other r 252 (by decide)]
    rfl
  · change data2 r 253=localInput3 r 11
    rw [data2_other r 253 (by decide)]
    rw [data1_other r 253 (by decide)]
    rfl
  · change data2 r 254=localInput3 r 12
    rw [data2_other r 254 (by decide)]
    rw [data1_other r 254 (by decide)]
    rfl
  · change data2 r 255=localInput3 r 13
    rw [data2_other r 255 (by decide)]
    rw [data1_other r 255 (by decide)]
    rfl
  · change data2 r 256=localInput3 r 14
    rw [data2_other r 256 (by decide)]
    rw [data1_other r 256 (by decide)]
    rfl
  · change data2 r 257=localInput3 r 15
    rw [data2_other r 257 (by decide)]
    rw [data1_other r 257 (by decide)]
    rfl
  · change data2 r 258=localInput3 r 16
    rw [data2_other r 258 (by decide)]
    rw [data1_other r 258 (by decide)]
    rfl
  · change data2 r 259=localInput3 r 17
    rw [data2_other r 259 (by decide)]
    rw [data1_other r 259 (by decide)]
    rfl
  · change data2 r 260=localInput3 r 18
    rw [data2_other r 260 (by decide)]
    rw [data1_other r 260 (by decide)]
    rfl
  · change data2 r 261=localInput3 r 19
    rw [data2_other r 261 (by decide)]
    rw [data1_other r 261 (by decide)]
    rfl
  · change data2 r 262=localInput3 r 20
    rw [data2_other r 262 (by decide)]
    rw [data1_other r 262 (by decide)]
    rfl
  · change data2 r 263=localInput3 r 21
    rw [data2_other r 263 (by decide)]
    rw [data1_other r 263 (by decide)]
    rfl
  · change data2 r 264=localInput3 r 22
    rw [data2_other r 264 (by decide)]
    rw [data1_other r 264 (by decide)]
    rfl
  · change data2 r 265=localInput3 r 23
    rw [data2_other r 265 (by decide)]
    rw [data1_other r 265 (by decide)]
    rfl
  · change data2 r 266=localInput3 r 24
    rw [data2_other r 266 (by decide)]
    rw [data1_other r 266 (by decide)]
    rfl
  · change data2 r 267=localInput3 r 25
    rw [data2_other r 267 (by decide)]
    rw [data1_other r 267 (by decide)]
    rfl
  · change data2 r 268=localInput3 r 26
    rw [data2_other r 268 (by decide)]
    rw [data1_other r 268 (by decide)]
    rfl
  · change data2 r 269=localInput3 r 27
    rw [data2_other r 269 (by decide)]
    rw [data1_other r 269 (by decide)]
    rfl
  · change data2 r 270=localInput3 r 28
    rw [data2_other r 270 (by decide)]
    rw [data1_other r 270 (by decide)]
    rfl
  · change data2 r 271=localInput3 r 29
    rw [data2_other r 271 (by decide)]
    rw [data1_other r 271 (by decide)]
    rfl
  · change data2 r 272=localInput3 r 30
    rw [data2_other r 272 (by decide)]
    rw [data1_other r 272 (by decide)]
    rfl
  · change data2 r 273=localInput3 r 31
    rw [data2_other r 273 (by decide)]
    rw [data1_other r 273 (by decide)]
    rfl
  · change data2 r 274=localInput3 r 32
    rw [data2_other r 274 (by decide)]
    rw [data1_other r 274 (by decide)]
    rfl
  · change data2 r 275=localInput3 r 33
    rw [data2_other r 275 (by decide)]
    rw [data1_other r 275 (by decide)]
    rfl
  · change data2 r 276=localInput3 r 34
    rw [data2_other r 276 (by decide)]
    rw [data1_other r 276 (by decide)]
    rfl
  · change data2 r 277=localInput3 r 35
    rw [data2_other r 277 (by decide)]
    rw [data1_other r 277 (by decide)]
    rfl
  · change data2 r 278=localInput3 r 36
    rw [data2_other r 278 (by decide)]
    rw [data1_other r 278 (by decide)]
    rfl
  · change data2 r 279=localInput3 r 37
    rw [data2_other r 279 (by decide)]
    rw [data1_other r 279 (by decide)]
    rfl
  · change data2 r 280=localInput3 r 38
    rw [data2_other r 280 (by decide)]
    rw [data1_other r 280 (by decide)]
    rfl
  · change data2 r 281=localInput3 r 39
    rw [data2_other r 281 (by decide)]
    rw [data1_other r 281 (by decide)]
    rfl
  · change data2 r 282=localInput3 r 40
    rw [data2_other r 282 (by decide)]
    rw [data1_other r 282 (by decide)]
    rfl
  · change data2 r 283=localInput3 r 41
    rw [data2_other r 283 (by decide)]
    rw [data1_other r 283 (by decide)]
    rfl
  · change data2 r 284=localInput3 r 42
    rw [data2_other r 284 (by decide)]
    rw [data1_other r 284 (by decide)]
    rfl
  · change data2 r 285=localInput3 r 43
    rw [data2_other r 285 (by decide)]
    rw [data1_other r 285 (by decide)]
    rfl
  · change data2 r 286=localInput3 r 44
    rw [data2_other r 286 (by decide)]
    rw [data1_other r 286 (by decide)]
    rfl
  · change data2 r 287=localInput3 r 45
    rw [data2_other r 287 (by decide)]
    rw [data1_other r 287 (by decide)]
    rfl
  · change data2 r 288=localInput3 r 46
    rw [data2_other r 288 (by decide)]
    rw [data1_other r 288 (by decide)]
    rfl
  · change data2 r 289=localInput3 r 47
    rw [data2_other r 289 (by decide)]
    rw [data1_other r 289 (by decide)]
    rfl
  · change data2 r 290=localInput3 r 48
    rw [data2_other r 290 (by decide)]
    rw [data1_other r 290 (by decide)]
    rfl
  · change data2 r 291=localInput3 r 49
    rw [data2_other r 291 (by decide)]
    rw [data1_other r 291 (by decide)]
    rfl
  · change data2 r 292=localInput3 r 50
    rw [data2_other r 292 (by decide)]
    rw [data1_other r 292 (by decide)]
    rfl
  · change data2 r 293=localInput3 r 51
    rw [data2_other r 293 (by decide)]
    rw [data1_other r 293 (by decide)]
    rfl
  · change data2 r 294=localInput3 r 52
    rw [data2_other r 294 (by decide)]
    rw [data1_other r 294 (by decide)]
    rfl
  · change data2 r 295=localInput3 r 53
    rw [data2_other r 295 (by decide)]
    rw [data1_other r 295 (by decide)]
    rfl
  · change data2 r 296=localInput3 r 54
    rw [data2_other r 296 (by decide)]
    rw [data1_other r 296 (by decide)]
    rfl
  · change data2 r 297=localInput3 r 55
    rw [data2_other r 297 (by decide)]
    rw [data1_other r 297 (by decide)]
    rfl
  · change data2 r 298=localInput3 r 56
    rw [data2_other r 298 (by decide)]
    rw [data1_other r 298 (by decide)]
    rfl
  · change data2 r 299=localInput3 r 57
    rw [data2_other r 299 (by decide)]
    rw [data1_other r 299 (by decide)]
    rfl
  · change data2 r 300=localInput3 r 58
    rw [data2_other r 300 (by decide)]
    rw [data1_other r 300 (by decide)]
    rfl
  · change data2 r 301=localInput3 r 59
    rw [data2_other r 301 (by decide)]
    rw [data1_other r 301 (by decide)]
    rfl
  · change data2 r 302=localInput3 r 60
    rw [data2_other r 302 (by decide)]
    rw [data1_other r 302 (by decide)]
    rfl
  · change data2 r 303=localInput3 r 61
    rw [data2_other r 303 (by decide)]
    rw [data1_other r 303 (by decide)]
    rfl
  · change data2 r 304=localInput3 r 62
    rw [data2_other r 304 (by decide)]
    rw [data1_other r 304 (by decide)]
    rfl
  · change data2 r 305=localInput3 r 63
    rw [data2_other r 305 (by decide)]
    rw [data1_other r 305 (by decide)]
    rfl
  · change data2 r 306=localInput3 r 64
    rw [data2_other r 306 (by decide)]
    rw [data1_other r 306 (by decide)]
    rfl
  · change data2 r 307=localInput3 r 65
    rw [data2_other r 307 (by decide)]
    rw [data1_other r 307 (by decide)]
    rfl
  · change data2 r 308=localInput3 r 66
    rw [data2_other r 308 (by decide)]
    rw [data1_other r 308 (by decide)]
    rfl
  · change data2 r 309=localInput3 r 67
    rw [data2_other r 309 (by decide)]
    rw [data1_other r 309 (by decide)]
    rfl
  · change data2 r 310=localInput3 r 68
    rw [data2_other r 310 (by decide)]
    rw [data1_other r 310 (by decide)]
    rfl
  · change data2 r 311=localInput3 r 69
    rw [data2_other r 311 (by decide)]
    rw [data1_other r 311 (by decide)]
    rfl
  · change data2 r 312=localInput3 r 70
    rw [data2_other r 312 (by decide)]
    rw [data1_other r 312 (by decide)]
    rfl
  · change data2 r 313=localInput3 r 71
    rw [data2_other r 313 (by decide)]
    rw [data1_other r 313 (by decide)]
    rfl
  · change data2 r 314=localInput3 r 72
    rw [data2_other r 314 (by decide)]
    rw [data1_other r 314 (by decide)]
    rfl
  · change data2 r 315=localInput3 r 73
    rw [data2_other r 315 (by decide)]
    rw [data1_other r 315 (by decide)]
    rfl
  · change data2 r 316=localInput3 r 74
    rw [data2_other r 316 (by decide)]
    rw [data1_other r 316 (by decide)]
    rfl
  · change data2 r 317=localInput3 r 75
    rw [data2_other r 317 (by decide)]
    rw [data1_other r 317 (by decide)]
    rfl
  · change data2 r 318=localInput3 r 76
    rw [data2_other r 318 (by decide)]
    rw [data1_other r 318 (by decide)]
    rfl
  · change data2 r 319=localInput3 r 77
    rw [data2_other r 319 (by decide)]
    rw [data1_other r 319 (by decide)]
    rfl
  · change data2 r 320=localInput3 r 78
    rw [data2_other r 320 (by decide)]
    rw [data1_other r 320 (by decide)]
    rfl
  · change data2 r 321=localInput3 r 79
    rw [data2_other r 321 (by decide)]
    rw [data1_other r 321 (by decide)]
    rfl
  · change data2 r 322=localInput3 r 80
    rw [data2_other r 322 (by decide)]
    rw [data1_other r 322 (by decide)]
    rfl
  · change data2 r 323=localInput3 r 81
    rw [data2_other r 323 (by decide)]
    rw [data1_other r 323 (by decide)]
    rfl
  · change data2 r 324=localInput3 r 82
    rw [data2_other r 324 (by decide)]
    rw [data1_other r 324 (by decide)]
    rfl
  · change data2 r 325=localInput3 r 83
    rw [data2_other r 325 (by decide)]
    rw [data1_other r 325 (by decide)]
    rfl
  · change data2 r 326=localInput3 r 84
    rw [data2_other r 326 (by decide)]
    rw [data1_other r 326 (by decide)]
    rfl
  · change data2 r 327=localInput3 r 85
    rw [data2_other r 327 (by decide)]
    rw [data1_other r 327 (by decide)]
    rfl
  · change data2 r 328=localInput3 r 86
    rw [data2_other r 328 (by decide)]
    rw [data1_other r 328 (by decide)]
    rfl
  · change data2 r 329=localInput3 r 87
    rw [data2_other r 329 (by decide)]
    rw [data1_other r 329 (by decide)]
    rfl

theorem step3 (r : Args q) : Step phase3 (localBudget3 r)
    (heads2 r) (data2 r) (heads3 r) (data3 r) :=
  (localStep3 r).dock slots3 slots3_inj (heads2 r) (data2 r) (heads3_input r) (data3_input r)
noncomputable def joined3 := Composition.machine joined2 phase3
def budget3 (r : Args q) := budget2 r+1+localBudget3 r
theorem joined3_run (r : Args q) : Step joined3 (budget3 r) (heads0 r) (data0 r) (heads3 r) (data3 r) :=
  (joined2_run r).seq (step3 r)

def slots4 : Fin 11→Fin 372 := ![262,330,331,332,223,333,334,335,104,336,337]
theorem slots4_inj : Function.Injective slots4 := by decide
noncomputable def phase4 := RecoveryFocus.machine slots4 BinaryCacheColdControl.binaryMachine
noncomputable def data4 (r : Args q) := install slots4 (data3 r) (localOutput4 r)
noncomputable def heads4 (r : Args q) := dockH slots4 (heads3 r) (localHeadsOut4 r)
theorem data4_slot (r : Args q) (j : Fin 11) : data4 r (slots4 j)=localOutput4 r j :=
  install_slot slots4 slots4_inj _ _ j
theorem data4_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots4 j≠k) : data4 r k=data3 r k :=
  install_other slots4 _ _ k hk
theorem heads4_slot (r : Args q) (j : Fin 11) : heads4 r (slots4 j)=localHeadsOut4 r j :=
  dockH_slot slots4 slots4_inj _ _ j
theorem heads4_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots4 j≠k) : heads4 r k=heads3 r k :=
  dockH_other slots4 _ _ k hk

theorem heads4_input (r : Args q) : ∀ j,heads3 r (slots4 j)=localHeadsIn4 r j := by
  intro j
  fin_cases j
  · change heads3 r 262=localHeadsIn4 r 0
    rw [show heads3 r 262=localHeadsOut3 r 20 from heads3_slot r 20]
    rfl
  · change heads3 r 330=localHeadsIn4 r 1
    rw [heads3_other r 330 (by decide)]
    rw [heads2_other r 330 (by decide)]
    rw [heads1_other r 330 (by decide)]
    rfl
  · change heads3 r 331=localHeadsIn4 r 2
    rw [heads3_other r 331 (by decide)]
    rw [heads2_other r 331 (by decide)]
    rw [heads1_other r 331 (by decide)]
    rfl
  · change heads3 r 332=localHeadsIn4 r 3
    rw [heads3_other r 332 (by decide)]
    rw [heads2_other r 332 (by decide)]
    rw [heads1_other r 332 (by decide)]
    rfl
  · change heads3 r 223=localHeadsIn4 r 4
    rw [heads3_other r 223 (by decide)]
    rw [heads2_other r 223 (by decide)]
    rw [heads1_other r 223 (by decide)]
    rfl
  · change heads3 r 333=localHeadsIn4 r 5
    rw [heads3_other r 333 (by decide)]
    rw [heads2_other r 333 (by decide)]
    rw [heads1_other r 333 (by decide)]
    rfl
  · change heads3 r 334=localHeadsIn4 r 6
    rw [heads3_other r 334 (by decide)]
    rw [heads2_other r 334 (by decide)]
    rw [heads1_other r 334 (by decide)]
    rfl
  · change heads3 r 335=localHeadsIn4 r 7
    rw [heads3_other r 335 (by decide)]
    rw [heads2_other r 335 (by decide)]
    rw [heads1_other r 335 (by decide)]
    rfl
  · change heads3 r 104=localHeadsIn4 r 8
    rw [heads3_other r 104 (by decide)]
    rw [heads2_other r 104 (by decide)]
    rw [heads1_other r 104 (by decide)]
    rfl
  · change heads3 r 336=localHeadsIn4 r 9
    rw [heads3_other r 336 (by decide)]
    rw [heads2_other r 336 (by decide)]
    rw [heads1_other r 336 (by decide)]
    rfl
  · change heads3 r 337=localHeadsIn4 r 10
    rw [heads3_other r 337 (by decide)]
    rw [heads2_other r 337 (by decide)]
    rw [heads1_other r 337 (by decide)]
    rfl

theorem data4_input (r : Args q) : ∀ j,data3 r (slots4 j)=localInput4 r j := by
  intro j
  fin_cases j
  · change data3 r 262=localInput4 r 0
    rw [show data3 r 262=localOutput3 r 20 from data3_slot r 20]
    rw [projection3_20]
    rfl
  · change data3 r 330=localInput4 r 1
    rw [data3_other r 330 (by decide)]
    rw [data2_other r 330 (by decide)]
    rw [data1_other r 330 (by decide)]
    rfl
  · change data3 r 331=localInput4 r 2
    rw [data3_other r 331 (by decide)]
    rw [data2_other r 331 (by decide)]
    rw [data1_other r 331 (by decide)]
    rfl
  · change data3 r 332=localInput4 r 3
    rw [data3_other r 332 (by decide)]
    rw [data2_other r 332 (by decide)]
    rw [data1_other r 332 (by decide)]
    rfl
  · change data3 r 223=localInput4 r 4
    rw [data3_other r 223 (by decide)]
    rw [data2_other r 223 (by decide)]
    rw [data1_other r 223 (by decide)]
    rfl
  · change data3 r 333=localInput4 r 5
    rw [data3_other r 333 (by decide)]
    rw [data2_other r 333 (by decide)]
    rw [data1_other r 333 (by decide)]
    rfl
  · change data3 r 334=localInput4 r 6
    rw [data3_other r 334 (by decide)]
    rw [data2_other r 334 (by decide)]
    rw [data1_other r 334 (by decide)]
    rfl
  · change data3 r 335=localInput4 r 7
    rw [data3_other r 335 (by decide)]
    rw [data2_other r 335 (by decide)]
    rw [data1_other r 335 (by decide)]
    rfl
  · change data3 r 104=localInput4 r 8
    rw [data3_other r 104 (by decide)]
    rw [data2_other r 104 (by decide)]
    rw [data1_other r 104 (by decide)]
    rfl
  · change data3 r 336=localInput4 r 9
    rw [data3_other r 336 (by decide)]
    rw [data2_other r 336 (by decide)]
    rw [data1_other r 336 (by decide)]
    rfl
  · change data3 r 337=localInput4 r 10
    rw [data3_other r 337 (by decide)]
    rw [data2_other r 337 (by decide)]
    rw [data1_other r 337 (by decide)]
    rfl

theorem step4 (r : Args q) : Step phase4 (localBudget4 r)
    (heads3 r) (data3 r) (heads4 r) (data4 r) :=
  (localStep4 r).dock slots4 slots4_inj (heads3 r) (data3 r) (heads4_input r) (data4_input r)
noncomputable def joined4 := Composition.machine joined3 phase4
def budget4 (r : Args q) := budget3 r+1+localBudget4 r
theorem joined4_run (r : Args q) : Step joined4 (budget4 r) (heads0 r) (data0 r) (heads4 r) (data4 r) :=
  (joined3_run r).seq (step4 r)

def slots5 : Fin 1→Fin 372 := ![223]
theorem slots5_inj : Function.Injective slots5 := by decide
noncomputable def phase5 := RecoveryFocus.machine slots5 lower
noncomputable def data5 (r : Args q) := install slots5 (data4 r) (localOutput5 r)
noncomputable def heads5 (r : Args q) := dockH slots5 (heads4 r) (localHeadsOut5 r)
theorem data5_slot (r : Args q) (j : Fin 1) : data5 r (slots5 j)=localOutput5 r j :=
  install_slot slots5 slots5_inj _ _ j
theorem data5_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots5 j≠k) : data5 r k=data4 r k :=
  install_other slots5 _ _ k hk
theorem heads5_slot (r : Args q) (j : Fin 1) : heads5 r (slots5 j)=localHeadsOut5 r j :=
  dockH_slot slots5 slots5_inj _ _ j
theorem heads5_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots5 j≠k) : heads5 r k=heads4 r k :=
  dockH_other slots5 _ _ k hk

theorem heads5_input (r : Args q) : ∀ j,heads4 r (slots5 j)=localHeadsIn5 r j := by
  intro j
  fin_cases j
  · change heads4 r 223=localHeadsIn5 r 0
    rw [show heads4 r 223=localHeadsOut4 r 4 from heads4_slot r 4]
    rfl

theorem data5_input (r : Args q) : ∀ j,data4 r (slots5 j)=localInput5 r j := by
  intro j
  fin_cases j
  · change data4 r 223=localInput5 r 0
    rw [show data4 r 223=localOutput4 r 4 from data4_slot r 4]
    rw [projection4_4]
    rfl

theorem step5 (r : Args q) : Step phase5 (localBudget5 r)
    (heads4 r) (data4 r) (heads5 r) (data5 r) :=
  (localStep5 r).dock slots5 slots5_inj (heads4 r) (data4 r) (heads5_input r) (data5_input r)
noncomputable def joined5 := Composition.machine joined4 phase5
def budget5 (r : Args q) := budget4 r+1+localBudget5 r
theorem joined5_run (r : Args q) : Step joined5 (budget5 r) (heads0 r) (data0 r) (heads5 r) (data5 r) :=
  (joined4_run r).seq (step5 r)

def slots6 : Fin 17→Fin 372 := ![223,236,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352]
theorem slots6_inj : Function.Injective slots6 := by decide
noncomputable def phase6 := RecoveryFocus.machine slots6 BinaryCacheColdPoolCount.machine
noncomputable def data6 (r : Args q) := install slots6 (data5 r) (localOutput6 r)
noncomputable def heads6 (r : Args q) := dockH slots6 (heads5 r) (localHeadsOut6 r)
theorem data6_slot (r : Args q) (j : Fin 17) : data6 r (slots6 j)=localOutput6 r j :=
  install_slot slots6 slots6_inj _ _ j
theorem data6_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots6 j≠k) : data6 r k=data5 r k :=
  install_other slots6 _ _ k hk
theorem heads6_slot (r : Args q) (j : Fin 17) : heads6 r (slots6 j)=localHeadsOut6 r j :=
  dockH_slot slots6 slots6_inj _ _ j
theorem heads6_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots6 j≠k) : heads6 r k=heads5 r k :=
  dockH_other slots6 _ _ k hk

theorem heads6_input (r : Args q) : ∀ j,heads5 r (slots6 j)=localHeadsIn6 r j := by
  intro j
  fin_cases j
  · change heads5 r 223=localHeadsIn6 r 0
    rw [show heads5 r 223=localHeadsOut5 r 0 from heads5_slot r 0]
    rfl
  · change heads5 r 236=localHeadsIn6 r 1
    rw [heads5_other r 236 (by decide)]
    rw [heads4_other r 236 (by decide)]
    rw [show heads3 r 236=localHeadsOut3 r 2 from heads3_slot r 2]
    rfl
  · change heads5 r 338=localHeadsIn6 r 2
    rw [heads5_other r 338 (by decide)]
    rw [heads4_other r 338 (by decide)]
    rw [heads3_other r 338 (by decide)]
    rw [heads2_other r 338 (by decide)]
    rw [heads1_other r 338 (by decide)]
    rfl
  · change heads5 r 339=localHeadsIn6 r 3
    rw [heads5_other r 339 (by decide)]
    rw [heads4_other r 339 (by decide)]
    rw [heads3_other r 339 (by decide)]
    rw [heads2_other r 339 (by decide)]
    rw [heads1_other r 339 (by decide)]
    rfl
  · change heads5 r 340=localHeadsIn6 r 4
    rw [heads5_other r 340 (by decide)]
    rw [heads4_other r 340 (by decide)]
    rw [heads3_other r 340 (by decide)]
    rw [heads2_other r 340 (by decide)]
    rw [heads1_other r 340 (by decide)]
    rfl
  · change heads5 r 341=localHeadsIn6 r 5
    rw [heads5_other r 341 (by decide)]
    rw [heads4_other r 341 (by decide)]
    rw [heads3_other r 341 (by decide)]
    rw [heads2_other r 341 (by decide)]
    rw [heads1_other r 341 (by decide)]
    rfl
  · change heads5 r 342=localHeadsIn6 r 6
    rw [heads5_other r 342 (by decide)]
    rw [heads4_other r 342 (by decide)]
    rw [heads3_other r 342 (by decide)]
    rw [heads2_other r 342 (by decide)]
    rw [heads1_other r 342 (by decide)]
    rfl
  · change heads5 r 343=localHeadsIn6 r 7
    rw [heads5_other r 343 (by decide)]
    rw [heads4_other r 343 (by decide)]
    rw [heads3_other r 343 (by decide)]
    rw [heads2_other r 343 (by decide)]
    rw [heads1_other r 343 (by decide)]
    rfl
  · change heads5 r 344=localHeadsIn6 r 8
    rw [heads5_other r 344 (by decide)]
    rw [heads4_other r 344 (by decide)]
    rw [heads3_other r 344 (by decide)]
    rw [heads2_other r 344 (by decide)]
    rw [heads1_other r 344 (by decide)]
    rfl
  · change heads5 r 345=localHeadsIn6 r 9
    rw [heads5_other r 345 (by decide)]
    rw [heads4_other r 345 (by decide)]
    rw [heads3_other r 345 (by decide)]
    rw [heads2_other r 345 (by decide)]
    rw [heads1_other r 345 (by decide)]
    rfl
  · change heads5 r 346=localHeadsIn6 r 10
    rw [heads5_other r 346 (by decide)]
    rw [heads4_other r 346 (by decide)]
    rw [heads3_other r 346 (by decide)]
    rw [heads2_other r 346 (by decide)]
    rw [heads1_other r 346 (by decide)]
    rfl
  · change heads5 r 347=localHeadsIn6 r 11
    rw [heads5_other r 347 (by decide)]
    rw [heads4_other r 347 (by decide)]
    rw [heads3_other r 347 (by decide)]
    rw [heads2_other r 347 (by decide)]
    rw [heads1_other r 347 (by decide)]
    rfl
  · change heads5 r 348=localHeadsIn6 r 12
    rw [heads5_other r 348 (by decide)]
    rw [heads4_other r 348 (by decide)]
    rw [heads3_other r 348 (by decide)]
    rw [heads2_other r 348 (by decide)]
    rw [heads1_other r 348 (by decide)]
    rfl
  · change heads5 r 349=localHeadsIn6 r 13
    rw [heads5_other r 349 (by decide)]
    rw [heads4_other r 349 (by decide)]
    rw [heads3_other r 349 (by decide)]
    rw [heads2_other r 349 (by decide)]
    rw [heads1_other r 349 (by decide)]
    rfl
  · change heads5 r 350=localHeadsIn6 r 14
    rw [heads5_other r 350 (by decide)]
    rw [heads4_other r 350 (by decide)]
    rw [heads3_other r 350 (by decide)]
    rw [heads2_other r 350 (by decide)]
    rw [heads1_other r 350 (by decide)]
    rfl
  · change heads5 r 351=localHeadsIn6 r 15
    rw [heads5_other r 351 (by decide)]
    rw [heads4_other r 351 (by decide)]
    rw [heads3_other r 351 (by decide)]
    rw [heads2_other r 351 (by decide)]
    rw [heads1_other r 351 (by decide)]
    rfl
  · change heads5 r 352=localHeadsIn6 r 16
    rw [heads5_other r 352 (by decide)]
    rw [heads4_other r 352 (by decide)]
    rw [heads3_other r 352 (by decide)]
    rw [heads2_other r 352 (by decide)]
    rw [heads1_other r 352 (by decide)]
    rfl

theorem data6_input (r : Args q) : ∀ j,data5 r (slots6 j)=localInput6 r j := by
  intro j
  fin_cases j
  · change data5 r 223=localInput6 r 0
    rw [show data5 r 223=localOutput5 r 0 from data5_slot r 0]
    rw [projection5_0]
    rfl
  · change data5 r 236=localInput6 r 1
    rw [data5_other r 236 (by decide)]
    rw [data4_other r 236 (by decide)]
    rw [show data3 r 236=localOutput3 r 2 from data3_slot r 2]
    rw [projection3_2]
    rfl
  · change data5 r 338=localInput6 r 2
    rw [data5_other r 338 (by decide)]
    rw [data4_other r 338 (by decide)]
    rw [data3_other r 338 (by decide)]
    rw [data2_other r 338 (by decide)]
    rw [data1_other r 338 (by decide)]
    rfl
  · change data5 r 339=localInput6 r 3
    rw [data5_other r 339 (by decide)]
    rw [data4_other r 339 (by decide)]
    rw [data3_other r 339 (by decide)]
    rw [data2_other r 339 (by decide)]
    rw [data1_other r 339 (by decide)]
    rfl
  · change data5 r 340=localInput6 r 4
    rw [data5_other r 340 (by decide)]
    rw [data4_other r 340 (by decide)]
    rw [data3_other r 340 (by decide)]
    rw [data2_other r 340 (by decide)]
    rw [data1_other r 340 (by decide)]
    rfl
  · change data5 r 341=localInput6 r 5
    rw [data5_other r 341 (by decide)]
    rw [data4_other r 341 (by decide)]
    rw [data3_other r 341 (by decide)]
    rw [data2_other r 341 (by decide)]
    rw [data1_other r 341 (by decide)]
    rfl
  · change data5 r 342=localInput6 r 6
    rw [data5_other r 342 (by decide)]
    rw [data4_other r 342 (by decide)]
    rw [data3_other r 342 (by decide)]
    rw [data2_other r 342 (by decide)]
    rw [data1_other r 342 (by decide)]
    rfl
  · change data5 r 343=localInput6 r 7
    rw [data5_other r 343 (by decide)]
    rw [data4_other r 343 (by decide)]
    rw [data3_other r 343 (by decide)]
    rw [data2_other r 343 (by decide)]
    rw [data1_other r 343 (by decide)]
    rfl
  · change data5 r 344=localInput6 r 8
    rw [data5_other r 344 (by decide)]
    rw [data4_other r 344 (by decide)]
    rw [data3_other r 344 (by decide)]
    rw [data2_other r 344 (by decide)]
    rw [data1_other r 344 (by decide)]
    rfl
  · change data5 r 345=localInput6 r 9
    rw [data5_other r 345 (by decide)]
    rw [data4_other r 345 (by decide)]
    rw [data3_other r 345 (by decide)]
    rw [data2_other r 345 (by decide)]
    rw [data1_other r 345 (by decide)]
    rfl
  · change data5 r 346=localInput6 r 10
    rw [data5_other r 346 (by decide)]
    rw [data4_other r 346 (by decide)]
    rw [data3_other r 346 (by decide)]
    rw [data2_other r 346 (by decide)]
    rw [data1_other r 346 (by decide)]
    rfl
  · change data5 r 347=localInput6 r 11
    rw [data5_other r 347 (by decide)]
    rw [data4_other r 347 (by decide)]
    rw [data3_other r 347 (by decide)]
    rw [data2_other r 347 (by decide)]
    rw [data1_other r 347 (by decide)]
    rfl
  · change data5 r 348=localInput6 r 12
    rw [data5_other r 348 (by decide)]
    rw [data4_other r 348 (by decide)]
    rw [data3_other r 348 (by decide)]
    rw [data2_other r 348 (by decide)]
    rw [data1_other r 348 (by decide)]
    rfl
  · change data5 r 349=localInput6 r 13
    rw [data5_other r 349 (by decide)]
    rw [data4_other r 349 (by decide)]
    rw [data3_other r 349 (by decide)]
    rw [data2_other r 349 (by decide)]
    rw [data1_other r 349 (by decide)]
    rfl
  · change data5 r 350=localInput6 r 14
    rw [data5_other r 350 (by decide)]
    rw [data4_other r 350 (by decide)]
    rw [data3_other r 350 (by decide)]
    rw [data2_other r 350 (by decide)]
    rw [data1_other r 350 (by decide)]
    rfl
  · change data5 r 351=localInput6 r 15
    rw [data5_other r 351 (by decide)]
    rw [data4_other r 351 (by decide)]
    rw [data3_other r 351 (by decide)]
    rw [data2_other r 351 (by decide)]
    rw [data1_other r 351 (by decide)]
    rfl
  · change data5 r 352=localInput6 r 16
    rw [data5_other r 352 (by decide)]
    rw [data4_other r 352 (by decide)]
    rw [data3_other r 352 (by decide)]
    rw [data2_other r 352 (by decide)]
    rw [data1_other r 352 (by decide)]
    rfl

theorem step6 (r : Args q) : Step phase6 (localBudget6 r)
    (heads5 r) (data5 r) (heads6 r) (data6 r) :=
  (localStep6 r).dock slots6 slots6_inj (heads5 r) (data5 r) (heads6_input r) (data6_input r)
noncomputable def joined6 := Composition.machine joined5 phase6
def budget6 (r : Args q) := budget5 r+1+localBudget6 r
theorem joined6_run (r : Args q) : Step joined6 (budget6 r) (heads0 r) (data0 r) (heads6 r) (data6 r) :=
  (joined5_run r).seq (step6 r)

def slots7 : Fin 4→Fin 372 := ![224,225,353,354]
theorem slots7_inj : Function.Injective slots7 := by decide
noncomputable def phase7 := RecoveryFocus.machine slots7 MatrixUnaryDifference.resetMachine
noncomputable def data7 (r : Args q) := install slots7 (data6 r) (localOutput7 r)
noncomputable def heads7 (r : Args q) := dockH slots7 (heads6 r) (localHeadsOut7 r)
theorem data7_slot (r : Args q) (j : Fin 4) : data7 r (slots7 j)=localOutput7 r j :=
  install_slot slots7 slots7_inj _ _ j
theorem data7_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots7 j≠k) : data7 r k=data6 r k :=
  install_other slots7 _ _ k hk
theorem heads7_slot (r : Args q) (j : Fin 4) : heads7 r (slots7 j)=localHeadsOut7 r j :=
  dockH_slot slots7 slots7_inj _ _ j
theorem heads7_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots7 j≠k) : heads7 r k=heads6 r k :=
  dockH_other slots7 _ _ k hk

theorem heads7_input (r : Args q) : ∀ j,heads6 r (slots7 j)=localHeadsIn7 r j := by
  intro j
  fin_cases j
  · change heads6 r 224=localHeadsIn7 r 0
    rw [heads6_other r 224 (by decide)]
    rw [heads5_other r 224 (by decide)]
    rw [heads4_other r 224 (by decide)]
    rw [show heads3 r 224=localHeadsOut3 r 1 from heads3_slot r 1]
    rfl
  · change heads6 r 225=localHeadsIn7 r 1
    rw [heads6_other r 225 (by decide)]
    rw [heads5_other r 225 (by decide)]
    rw [heads4_other r 225 (by decide)]
    rw [show heads3 r 225=localHeadsOut3 r 3 from heads3_slot r 3]
    rfl
  · change heads6 r 353=localHeadsIn7 r 2
    rw [heads6_other r 353 (by decide)]
    rw [heads5_other r 353 (by decide)]
    rw [heads4_other r 353 (by decide)]
    rw [heads3_other r 353 (by decide)]
    rw [heads2_other r 353 (by decide)]
    rw [heads1_other r 353 (by decide)]
    rfl
  · change heads6 r 354=localHeadsIn7 r 3
    rw [heads6_other r 354 (by decide)]
    rw [heads5_other r 354 (by decide)]
    rw [heads4_other r 354 (by decide)]
    rw [heads3_other r 354 (by decide)]
    rw [heads2_other r 354 (by decide)]
    rw [heads1_other r 354 (by decide)]
    rfl

theorem data7_input (r : Args q) : ∀ j,data6 r (slots7 j)=localInput7 r j := by
  intro j
  fin_cases j
  · change data6 r 224=localInput7 r 0
    rw [data6_other r 224 (by decide)]
    rw [data5_other r 224 (by decide)]
    rw [data4_other r 224 (by decide)]
    rw [show data3 r 224=localOutput3 r 1 from data3_slot r 1]
    rw [projection3_1]
    rfl
  · change data6 r 225=localInput7 r 1
    rw [data6_other r 225 (by decide)]
    rw [data5_other r 225 (by decide)]
    rw [data4_other r 225 (by decide)]
    rw [show data3 r 225=localOutput3 r 3 from data3_slot r 3]
    rw [projection3_3]
    rfl
  · change data6 r 353=localInput7 r 2
    rw [data6_other r 353 (by decide)]
    rw [data5_other r 353 (by decide)]
    rw [data4_other r 353 (by decide)]
    rw [data3_other r 353 (by decide)]
    rw [data2_other r 353 (by decide)]
    rw [data1_other r 353 (by decide)]
    rfl
  · change data6 r 354=localInput7 r 3
    rw [data6_other r 354 (by decide)]
    rw [data5_other r 354 (by decide)]
    rw [data4_other r 354 (by decide)]
    rw [data3_other r 354 (by decide)]
    rw [data2_other r 354 (by decide)]
    rw [data1_other r 354 (by decide)]
    rfl

theorem step7 (r : Args q) : Step phase7 (localBudget7 r)
    (heads6 r) (data6 r) (heads7 r) (data7 r) :=
  (localStep7 r).dock slots7 slots7_inj (heads6 r) (data6 r) (heads7_input r) (data7_input r)
noncomputable def joined7 := Composition.machine joined6 phase7
def budget7 (r : Args q) := budget6 r+1+localBudget7 r
theorem joined7_run (r : Args q) : Step joined7 (budget7 r) (heads0 r) (data0 r) (heads7 r) (data7 r) :=
  (joined6_run r).seq (step7 r)

def slots8 : Fin 2→Fin 372 := ![223,353]
theorem slots8_inj : Function.Injective slots8 := by decide
noncomputable def phase8 := RecoveryFocus.machine slots8 raise
noncomputable def data8 (r : Args q) := install slots8 (data7 r) (localOutput8 r)
noncomputable def heads8 (r : Args q) := dockH slots8 (heads7 r) (localHeadsOut8 r)
theorem data8_slot (r : Args q) (j : Fin 2) : data8 r (slots8 j)=localOutput8 r j :=
  install_slot slots8 slots8_inj _ _ j
theorem data8_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots8 j≠k) : data8 r k=data7 r k :=
  install_other slots8 _ _ k hk
theorem heads8_slot (r : Args q) (j : Fin 2) : heads8 r (slots8 j)=localHeadsOut8 r j :=
  dockH_slot slots8 slots8_inj _ _ j
theorem heads8_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots8 j≠k) : heads8 r k=heads7 r k :=
  dockH_other slots8 _ _ k hk

theorem heads8_input (r : Args q) : ∀ j,heads7 r (slots8 j)=localHeadsIn8 r j := by
  intro j
  fin_cases j
  · change heads7 r 223=localHeadsIn8 r 0
    rw [heads7_other r 223 (by decide)]
    rw [show heads6 r 223=localHeadsOut6 r 0 from heads6_slot r 0]
    rfl
  · change heads7 r 353=localHeadsIn8 r 1
    rw [show heads7 r 353=localHeadsOut7 r 2 from heads7_slot r 2]
    rfl

theorem data8_input (r : Args q) : ∀ j,data7 r (slots8 j)=localInput8 r j := by
  intro j
  fin_cases j
  · change data7 r 223=localInput8 r 0
    rw [data7_other r 223 (by decide)]
    rw [show data6 r 223=localOutput6 r 0 from data6_slot r 0]
    rw [projection6_0]
    rfl
  · change data7 r 353=localInput8 r 1
    rw [show data7 r 353=localOutput7 r 2 from data7_slot r 2]
    rw [projection7_2]
    rfl

theorem step8 (r : Args q) : Step phase8 (localBudget8 r)
    (heads7 r) (data7 r) (heads8 r) (data8 r) :=
  (localStep8 r).dock slots8 slots8_inj (heads7 r) (data7 r) (heads8_input r) (data8_input r)
noncomputable def joined8 := Composition.machine joined7 phase8
def budget8 (r : Args q) := budget7 r+1+localBudget8 r
theorem joined8_run (r : Args q) : Step joined8 (budget8 r) (heads0 r) (data0 r) (heads8 r) (data8 r) :=
  (joined7_run r).seq (step8 r)

def slots9 : Fin 19→Fin 372 := ![344,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,34,353]
theorem slots9_inj : Function.Injective slots9 := by decide
noncomputable def phase9 := RecoveryFocus.machine slots9 BinaryCachePrefix.machine
noncomputable def data9 (r : Args q) := install slots9 (data8 r) (localOutput9 r)
noncomputable def heads9 (r : Args q) := dockH slots9 (heads8 r) (localHeadsOut9 r)
theorem data9_slot (r : Args q) (j : Fin 19) : data9 r (slots9 j)=localOutput9 r j :=
  install_slot slots9 slots9_inj _ _ j
theorem data9_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots9 j≠k) : data9 r k=data8 r k :=
  install_other slots9 _ _ k hk
theorem heads9_slot (r : Args q) (j : Fin 19) : heads9 r (slots9 j)=localHeadsOut9 r j :=
  dockH_slot slots9 slots9_inj _ _ j
theorem heads9_other (r : Args q) (k : Fin 372) (hk : ∀ j,slots9 j≠k) : heads9 r k=heads8 r k :=
  dockH_other slots9 _ _ k hk

theorem heads9_input (r : Args q) : ∀ j,heads8 r (slots9 j)=localHeadsIn9 r j := by
  intro j
  fin_cases j
  · change heads8 r 344=localHeadsIn9 r 0
    rw [heads8_other r 344 (by decide)]
    rw [heads7_other r 344 (by decide)]
    rw [show heads6 r 344=localHeadsOut6 r 8 from heads6_slot r 8]
    rfl
  · change heads8 r 355=localHeadsIn9 r 1
    rw [heads8_other r 355 (by decide)]
    rw [heads7_other r 355 (by decide)]
    rw [heads6_other r 355 (by decide)]
    rw [heads5_other r 355 (by decide)]
    rw [heads4_other r 355 (by decide)]
    rw [heads3_other r 355 (by decide)]
    rw [heads2_other r 355 (by decide)]
    rw [heads1_other r 355 (by decide)]
    rfl
  · change heads8 r 356=localHeadsIn9 r 2
    rw [heads8_other r 356 (by decide)]
    rw [heads7_other r 356 (by decide)]
    rw [heads6_other r 356 (by decide)]
    rw [heads5_other r 356 (by decide)]
    rw [heads4_other r 356 (by decide)]
    rw [heads3_other r 356 (by decide)]
    rw [heads2_other r 356 (by decide)]
    rw [heads1_other r 356 (by decide)]
    rfl
  · change heads8 r 357=localHeadsIn9 r 3
    rw [heads8_other r 357 (by decide)]
    rw [heads7_other r 357 (by decide)]
    rw [heads6_other r 357 (by decide)]
    rw [heads5_other r 357 (by decide)]
    rw [heads4_other r 357 (by decide)]
    rw [heads3_other r 357 (by decide)]
    rw [heads2_other r 357 (by decide)]
    rw [heads1_other r 357 (by decide)]
    rfl
  · change heads8 r 358=localHeadsIn9 r 4
    rw [heads8_other r 358 (by decide)]
    rw [heads7_other r 358 (by decide)]
    rw [heads6_other r 358 (by decide)]
    rw [heads5_other r 358 (by decide)]
    rw [heads4_other r 358 (by decide)]
    rw [heads3_other r 358 (by decide)]
    rw [heads2_other r 358 (by decide)]
    rw [heads1_other r 358 (by decide)]
    rfl
  · change heads8 r 359=localHeadsIn9 r 5
    rw [heads8_other r 359 (by decide)]
    rw [heads7_other r 359 (by decide)]
    rw [heads6_other r 359 (by decide)]
    rw [heads5_other r 359 (by decide)]
    rw [heads4_other r 359 (by decide)]
    rw [heads3_other r 359 (by decide)]
    rw [heads2_other r 359 (by decide)]
    rw [heads1_other r 359 (by decide)]
    rfl
  · change heads8 r 360=localHeadsIn9 r 6
    rw [heads8_other r 360 (by decide)]
    rw [heads7_other r 360 (by decide)]
    rw [heads6_other r 360 (by decide)]
    rw [heads5_other r 360 (by decide)]
    rw [heads4_other r 360 (by decide)]
    rw [heads3_other r 360 (by decide)]
    rw [heads2_other r 360 (by decide)]
    rw [heads1_other r 360 (by decide)]
    rfl
  · change heads8 r 361=localHeadsIn9 r 7
    rw [heads8_other r 361 (by decide)]
    rw [heads7_other r 361 (by decide)]
    rw [heads6_other r 361 (by decide)]
    rw [heads5_other r 361 (by decide)]
    rw [heads4_other r 361 (by decide)]
    rw [heads3_other r 361 (by decide)]
    rw [heads2_other r 361 (by decide)]
    rw [heads1_other r 361 (by decide)]
    rfl
  · change heads8 r 362=localHeadsIn9 r 8
    rw [heads8_other r 362 (by decide)]
    rw [heads7_other r 362 (by decide)]
    rw [heads6_other r 362 (by decide)]
    rw [heads5_other r 362 (by decide)]
    rw [heads4_other r 362 (by decide)]
    rw [heads3_other r 362 (by decide)]
    rw [heads2_other r 362 (by decide)]
    rw [heads1_other r 362 (by decide)]
    rfl
  · change heads8 r 363=localHeadsIn9 r 9
    rw [heads8_other r 363 (by decide)]
    rw [heads7_other r 363 (by decide)]
    rw [heads6_other r 363 (by decide)]
    rw [heads5_other r 363 (by decide)]
    rw [heads4_other r 363 (by decide)]
    rw [heads3_other r 363 (by decide)]
    rw [heads2_other r 363 (by decide)]
    rw [heads1_other r 363 (by decide)]
    rfl
  · change heads8 r 364=localHeadsIn9 r 10
    rw [heads8_other r 364 (by decide)]
    rw [heads7_other r 364 (by decide)]
    rw [heads6_other r 364 (by decide)]
    rw [heads5_other r 364 (by decide)]
    rw [heads4_other r 364 (by decide)]
    rw [heads3_other r 364 (by decide)]
    rw [heads2_other r 364 (by decide)]
    rw [heads1_other r 364 (by decide)]
    rfl
  · change heads8 r 365=localHeadsIn9 r 11
    rw [heads8_other r 365 (by decide)]
    rw [heads7_other r 365 (by decide)]
    rw [heads6_other r 365 (by decide)]
    rw [heads5_other r 365 (by decide)]
    rw [heads4_other r 365 (by decide)]
    rw [heads3_other r 365 (by decide)]
    rw [heads2_other r 365 (by decide)]
    rw [heads1_other r 365 (by decide)]
    rfl
  · change heads8 r 366=localHeadsIn9 r 12
    rw [heads8_other r 366 (by decide)]
    rw [heads7_other r 366 (by decide)]
    rw [heads6_other r 366 (by decide)]
    rw [heads5_other r 366 (by decide)]
    rw [heads4_other r 366 (by decide)]
    rw [heads3_other r 366 (by decide)]
    rw [heads2_other r 366 (by decide)]
    rw [heads1_other r 366 (by decide)]
    rfl
  · change heads8 r 367=localHeadsIn9 r 13
    rw [heads8_other r 367 (by decide)]
    rw [heads7_other r 367 (by decide)]
    rw [heads6_other r 367 (by decide)]
    rw [heads5_other r 367 (by decide)]
    rw [heads4_other r 367 (by decide)]
    rw [heads3_other r 367 (by decide)]
    rw [heads2_other r 367 (by decide)]
    rw [heads1_other r 367 (by decide)]
    rfl
  · change heads8 r 368=localHeadsIn9 r 14
    rw [heads8_other r 368 (by decide)]
    rw [heads7_other r 368 (by decide)]
    rw [heads6_other r 368 (by decide)]
    rw [heads5_other r 368 (by decide)]
    rw [heads4_other r 368 (by decide)]
    rw [heads3_other r 368 (by decide)]
    rw [heads2_other r 368 (by decide)]
    rw [heads1_other r 368 (by decide)]
    rfl
  · change heads8 r 369=localHeadsIn9 r 15
    rw [heads8_other r 369 (by decide)]
    rw [heads7_other r 369 (by decide)]
    rw [heads6_other r 369 (by decide)]
    rw [heads5_other r 369 (by decide)]
    rw [heads4_other r 369 (by decide)]
    rw [heads3_other r 369 (by decide)]
    rw [heads2_other r 369 (by decide)]
    rw [heads1_other r 369 (by decide)]
    rfl
  · change heads8 r 370=localHeadsIn9 r 16
    rw [heads8_other r 370 (by decide)]
    rw [heads7_other r 370 (by decide)]
    rw [heads6_other r 370 (by decide)]
    rw [heads5_other r 370 (by decide)]
    rw [heads4_other r 370 (by decide)]
    rw [heads3_other r 370 (by decide)]
    rw [heads2_other r 370 (by decide)]
    rw [heads1_other r 370 (by decide)]
    rfl
  · change heads8 r 34=localHeadsIn9 r 17
    rw [heads8_other r 34 (by decide)]
    rw [heads7_other r 34 (by decide)]
    rw [heads6_other r 34 (by decide)]
    rw [heads5_other r 34 (by decide)]
    rw [heads4_other r 34 (by decide)]
    rw [heads3_other r 34 (by decide)]
    rw [heads2_other r 34 (by decide)]
    rw [heads1_other r 34 (by decide)]
    rfl
  · change heads8 r 353=localHeadsIn9 r 18
    rw [show heads8 r 353=localHeadsOut8 r 1 from heads8_slot r 1]
    rfl

theorem data9_input (r : Args q) : ∀ j,data8 r (slots9 j)=localInput9 r j := by
  intro j
  fin_cases j
  · change data8 r 344=localInput9 r 0
    rw [data8_other r 344 (by decide)]
    rw [data7_other r 344 (by decide)]
    rw [show data6 r 344=localOutput6 r 8 from data6_slot r 8]
    rw [projection6_8]
    rfl
  · change data8 r 355=localInput9 r 1
    rw [data8_other r 355 (by decide)]
    rw [data7_other r 355 (by decide)]
    rw [data6_other r 355 (by decide)]
    rw [data5_other r 355 (by decide)]
    rw [data4_other r 355 (by decide)]
    rw [data3_other r 355 (by decide)]
    rw [data2_other r 355 (by decide)]
    rw [data1_other r 355 (by decide)]
    rfl
  · change data8 r 356=localInput9 r 2
    rw [data8_other r 356 (by decide)]
    rw [data7_other r 356 (by decide)]
    rw [data6_other r 356 (by decide)]
    rw [data5_other r 356 (by decide)]
    rw [data4_other r 356 (by decide)]
    rw [data3_other r 356 (by decide)]
    rw [data2_other r 356 (by decide)]
    rw [data1_other r 356 (by decide)]
    rfl
  · change data8 r 357=localInput9 r 3
    rw [data8_other r 357 (by decide)]
    rw [data7_other r 357 (by decide)]
    rw [data6_other r 357 (by decide)]
    rw [data5_other r 357 (by decide)]
    rw [data4_other r 357 (by decide)]
    rw [data3_other r 357 (by decide)]
    rw [data2_other r 357 (by decide)]
    rw [data1_other r 357 (by decide)]
    rfl
  · change data8 r 358=localInput9 r 4
    rw [data8_other r 358 (by decide)]
    rw [data7_other r 358 (by decide)]
    rw [data6_other r 358 (by decide)]
    rw [data5_other r 358 (by decide)]
    rw [data4_other r 358 (by decide)]
    rw [data3_other r 358 (by decide)]
    rw [data2_other r 358 (by decide)]
    rw [data1_other r 358 (by decide)]
    rfl
  · change data8 r 359=localInput9 r 5
    rw [data8_other r 359 (by decide)]
    rw [data7_other r 359 (by decide)]
    rw [data6_other r 359 (by decide)]
    rw [data5_other r 359 (by decide)]
    rw [data4_other r 359 (by decide)]
    rw [data3_other r 359 (by decide)]
    rw [data2_other r 359 (by decide)]
    rw [data1_other r 359 (by decide)]
    rfl
  · change data8 r 360=localInput9 r 6
    rw [data8_other r 360 (by decide)]
    rw [data7_other r 360 (by decide)]
    rw [data6_other r 360 (by decide)]
    rw [data5_other r 360 (by decide)]
    rw [data4_other r 360 (by decide)]
    rw [data3_other r 360 (by decide)]
    rw [data2_other r 360 (by decide)]
    rw [data1_other r 360 (by decide)]
    rfl
  · change data8 r 361=localInput9 r 7
    rw [data8_other r 361 (by decide)]
    rw [data7_other r 361 (by decide)]
    rw [data6_other r 361 (by decide)]
    rw [data5_other r 361 (by decide)]
    rw [data4_other r 361 (by decide)]
    rw [data3_other r 361 (by decide)]
    rw [data2_other r 361 (by decide)]
    rw [data1_other r 361 (by decide)]
    rfl
  · change data8 r 362=localInput9 r 8
    rw [data8_other r 362 (by decide)]
    rw [data7_other r 362 (by decide)]
    rw [data6_other r 362 (by decide)]
    rw [data5_other r 362 (by decide)]
    rw [data4_other r 362 (by decide)]
    rw [data3_other r 362 (by decide)]
    rw [data2_other r 362 (by decide)]
    rw [data1_other r 362 (by decide)]
    rfl
  · change data8 r 363=localInput9 r 9
    rw [data8_other r 363 (by decide)]
    rw [data7_other r 363 (by decide)]
    rw [data6_other r 363 (by decide)]
    rw [data5_other r 363 (by decide)]
    rw [data4_other r 363 (by decide)]
    rw [data3_other r 363 (by decide)]
    rw [data2_other r 363 (by decide)]
    rw [data1_other r 363 (by decide)]
    rfl
  · change data8 r 364=localInput9 r 10
    rw [data8_other r 364 (by decide)]
    rw [data7_other r 364 (by decide)]
    rw [data6_other r 364 (by decide)]
    rw [data5_other r 364 (by decide)]
    rw [data4_other r 364 (by decide)]
    rw [data3_other r 364 (by decide)]
    rw [data2_other r 364 (by decide)]
    rw [data1_other r 364 (by decide)]
    rfl
  · change data8 r 365=localInput9 r 11
    rw [data8_other r 365 (by decide)]
    rw [data7_other r 365 (by decide)]
    rw [data6_other r 365 (by decide)]
    rw [data5_other r 365 (by decide)]
    rw [data4_other r 365 (by decide)]
    rw [data3_other r 365 (by decide)]
    rw [data2_other r 365 (by decide)]
    rw [data1_other r 365 (by decide)]
    rfl
  · change data8 r 366=localInput9 r 12
    rw [data8_other r 366 (by decide)]
    rw [data7_other r 366 (by decide)]
    rw [data6_other r 366 (by decide)]
    rw [data5_other r 366 (by decide)]
    rw [data4_other r 366 (by decide)]
    rw [data3_other r 366 (by decide)]
    rw [data2_other r 366 (by decide)]
    rw [data1_other r 366 (by decide)]
    rfl
  · change data8 r 367=localInput9 r 13
    rw [data8_other r 367 (by decide)]
    rw [data7_other r 367 (by decide)]
    rw [data6_other r 367 (by decide)]
    rw [data5_other r 367 (by decide)]
    rw [data4_other r 367 (by decide)]
    rw [data3_other r 367 (by decide)]
    rw [data2_other r 367 (by decide)]
    rw [data1_other r 367 (by decide)]
    rfl
  · change data8 r 368=localInput9 r 14
    rw [data8_other r 368 (by decide)]
    rw [data7_other r 368 (by decide)]
    rw [data6_other r 368 (by decide)]
    rw [data5_other r 368 (by decide)]
    rw [data4_other r 368 (by decide)]
    rw [data3_other r 368 (by decide)]
    rw [data2_other r 368 (by decide)]
    rw [data1_other r 368 (by decide)]
    rfl
  · change data8 r 369=localInput9 r 15
    rw [data8_other r 369 (by decide)]
    rw [data7_other r 369 (by decide)]
    rw [data6_other r 369 (by decide)]
    rw [data5_other r 369 (by decide)]
    rw [data4_other r 369 (by decide)]
    rw [data3_other r 369 (by decide)]
    rw [data2_other r 369 (by decide)]
    rw [data1_other r 369 (by decide)]
    rfl
  · change data8 r 370=localInput9 r 16
    rw [data8_other r 370 (by decide)]
    rw [data7_other r 370 (by decide)]
    rw [data6_other r 370 (by decide)]
    rw [data5_other r 370 (by decide)]
    rw [data4_other r 370 (by decide)]
    rw [data3_other r 370 (by decide)]
    rw [data2_other r 370 (by decide)]
    rw [data1_other r 370 (by decide)]
    rfl
  · change data8 r 34=localInput9 r 17
    rw [data8_other r 34 (by decide)]
    rw [data7_other r 34 (by decide)]
    rw [data6_other r 34 (by decide)]
    rw [data5_other r 34 (by decide)]
    rw [data4_other r 34 (by decide)]
    rw [data3_other r 34 (by decide)]
    rw [data2_other r 34 (by decide)]
    rw [data1_other r 34 (by decide)]
    rfl
  · change data8 r 353=localInput9 r 18
    rw [show data8 r 353=localOutput8 r 1 from data8_slot r 1]
    rw [projection8_1]
    rfl

theorem step9 (r : Args q) : Step phase9 (localBudget9 r)
    (heads8 r) (data8 r) (heads9 r) (data9 r) :=
  (localStep9 r).dock slots9 slots9_inj (heads8 r) (data8 r) (heads9_input r) (data9_input r)
noncomputable def joined9 := Composition.machine joined8 phase9
def budget9 (r : Args q) := budget8 r+1+localBudget9 r
theorem joined9_run (r : Args q) : Step joined9 (budget9 r) (heads0 r) (data0 r) (heads9 r) (data9 r) :=
  (joined8_run r).seq (step9 r)

end NearCubicWires.P1Closure.BinaryCacheColdJoin
