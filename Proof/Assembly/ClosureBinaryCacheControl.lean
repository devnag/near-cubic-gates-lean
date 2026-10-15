import Proof.Assembly.ClosureBinaryCachePrefix
import Proof.Assembly.ClosureBinaryInitialize
import Proof.MachineModel.OrdinaryMatrixUnaryDifference

/-! Paid small control producers for the cold cache: the binary initializer's
fixed empty frame is written physically, and the prefix accepts the unary
template produced by the existing residual-dimension subtraction. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdControl
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairSource.VerifierDecoding

def seedSlots : Fin 2→Fin 11 := ![7,10]
noncomputable def seed := RecoveryFocus.machine seedSlots (HierarchyFixedWord.machine [false])
noncomputable def binaryMachine := Composition.machine seed (TapeEmbedding.machine 1 BinaryInitialize.machine)
def binaryInput (K : Nat) : Fin 11→List Bool := fun i=>if i=0 then CompareMachine.word K else []
def seeded (K : Nat) : Fin 11→List Bool :=
  fun i=>Fin.addCases (BinaryInitialize.input K) (fun _ : Fin 1=>[false]) i
def binaryOutput (K : Nat) (scratch : Fin 5→List Bool) : Fin 11→List Bool :=
  fun i=>Fin.addCases (BinaryInitialize.output K scratch) (fun _ : Fin 1=>[false]) i
def binaryHeads : Fin 11→Nat := fun i=>Fin.addCases BinaryInitialize.heads (fun _ : Fin 1=>0) i

theorem seed_run (K : Nat) : Step seed 4 (fun _=>0) (binaryInput K) (fun _=>0) (seeded K) := by
  obtain ⟨r,hr,ht,hh,_⟩ := HierarchyFixedWord.word_ready [false]
  have h := (Step.of_run hr (funext hh) ht).focus seedSlots (by decide) (fun _=>0) (binaryInput K)
  refine (h.congr_in (dockH_existing _ _ _ (by intros;rfl))
    (install_existing _ _ _ (by intro j;fin_cases j <;>rfl))).congr
    (dockH_existing _ _ _ (by intros;rfl)) ?_
  apply HierarchyAllocation.install_eq seedSlots (by decide)
  · intro j;fin_cases j <;>rfl
  · intro i hi
    fin_cases i <;>first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)

theorem binary_run (K : Nat) : ∃ scratch : Fin 5→List Bool,
    Step binaryMachine (BinaryInitialize.budget K+5) (fun _=>0) (binaryInput K)
      binaryHeads (binaryOutput K scratch) := by
  obtain ⟨scratch,h⟩ := BinaryInitialize.initialize_run K
  have hz : (fun i : Fin 11=>Fin.addCases (motive:=fun _=>Nat) (fun _ : Fin 10=>0) (fun _ : Fin 1=>0) i)=
      (fun _ : Fin 11=>0) := by
    funext i;fin_cases i <;>rfl
  have final := (h.embed (fun _ : Fin 1=>0) (fun _ : Fin 1=>[false])).congr_in hz rfl
  have joined := (seed_run K).seq final
  have hb : 4+1+BinaryInitialize.budget K=BinaryInitialize.budget K+5 := by omega
  rw [hb] at joined
  exact ⟨scratch,joined⟩

noncomputable def differenceOutput (q K : Nat) (hK : K≤q) :=
  (Classical.choose (MatrixUnaryDifference.reset_run q K hK)).final.tapes
theorem difference_spec (q K : Nat) (hK : K≤q) :
    Step MatrixUnaryDifference.resetMachine (2*q+8) (fun _=>0)
      (MatrixUnaryDifference.resetInput q K) (fun _=>0) (differenceOutput q K hK) ∧
    differenceOutput q K hK 0=UnaryTemplate.tape q ∧
    differenceOutput q K hK 1=UnaryTemplate.tape K ∧
    differenceOutput q K hK 2=UnaryTemplate.tape (q-K) := by
  have h := Classical.choose_spec (MatrixUnaryDifference.reset_run q K hK)
  exact ⟨Step.of_run h.1 (funext h.2.2.2.2.1) rfl,h.2.1,h.2.2.1,h.2.2.2.1⟩

def prefixInput (N n : Nat) (out : List Bool) : Fin 19→List Bool :=
  fun i=>Fin.addCases (PCPPNativeNaturalAppend.data N out) (fun _ : Fin 1=>UnaryTemplate.tape n) i
def prefixCaps (n : Nat) (i : Fin 19) := if i=18 then n+2 else 0
noncomputable def prefixOutput (N n : Nat) (out : List Bool) (i : Fin 19) :=
  ZeroPadding.pad (prefixCaps n i)
    (BinaryCachePrefix.replace (BinaryCachePrefix.headerData N n out) (out++BinaryCachePrefix.prefixWord N n) i)

theorem prefix_run (N n : Nat) (out : List Bool) :
    Step BinaryCachePrefix.machine (BinaryCachePrefix.budget N n)
      (BinaryCachePrefix.inputHeads out) (prefixInput N n out)
      (BinaryCachePrefix.replace (BinaryCachePrefix.headerHeads N out)
        (out++BinaryCachePrefix.prefixWord N n).length)
      (prefixOutput N n out) := by
  have actual := (BinaryCachePrefix.run N n out).pad (prefixCaps n)
  apply actual.congr_in rfl
  funext i
  fin_cases i <;>first
    | exact ZeroPadding.pad_zero _
    | exact DecompositionSource.Records.template_pad n

end NearCubicWires.P1Closure.BinaryCacheColdControl
