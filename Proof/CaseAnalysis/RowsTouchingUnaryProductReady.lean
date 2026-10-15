import Proof.CaseAnalysis.RowsTouchingUnaryProduct

/-! Reuse the existing padded query counter directly for scalar
multiplication. Its cursor is returned to zero; no counter copy is needed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.UnaryProductReady
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advance:Fin 6→HeadMove:=![.stay,.stay,.stay,.stay,.stay,.right]
def retreat:Fin 6→HeadMove:=![.stay,.stay,.stay,.stay,.stay,.left]
noncomputable def machine:=Composition.machine
  (Composition.machine (DecompositionCountPosition.move advance) UnaryProduct.machine)
  (DecompositionCountPosition.move retreat)
def budget (w n : ℕ):=UnaryProduct.budget w n+4
def loopHeads:Fin 6→ℕ:=![0,0,0,0,0,1]
def pads (P : ℕ):Fin 6→ℕ:=![0,0,0,0,0,P]
def data (w x a n P : ℕ) (backing : List Bool):Fin 6→List Bool:=
  ![frame (binary w x),frame (binary w a),backing,List.replicate (4*w+3) false,
    List.replicate (2*w+1) false,ZeroPadding.pad P (CompareMachine.word n)]

theorem padded_data (w x a n P : ℕ) (backing : List Bool):
    (fun i=>ZeroPadding.pad (pads P i) (Fin.addCases (m:=5) (n:=1) (motive:=fun _=>List Bool)
      (MatrixScoreAccumulate.input w x a backing) (fun _=>CompareMachine.word n) i))=data w x a n P backing:=by
  funext i;fin_cases i
  · exact ZeroPadding.pad_zero _
  · exact ZeroPadding.pad_zero _
  · exact ZeroPadding.pad_zero _
  · exact ZeroPadding.pad_zero _
  · exact ZeroPadding.pad_zero _
  · rfl

theorem ready_run (w x n P : ℕ) (backing : List Bool)
    (hb:backing.length≤2*w+1) (hfit:n*x<2^w):
    Step machine (budget w n) (fun _=>0) (data w x 0 n P backing) (fun _=>0)
      (data w x (n*x) n P (UnaryProduct.scratch w x n backing)):=by
  obtain ⟨r,run,rf,_⟩:=UnaryProduct.product_run w x n backing hb hfit
  have actual:=Step.of_run run (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have padded:=actual.pad (pads P)
  have middle:Step UnaryProduct.machine (UnaryProduct.budget w n) loopHeads (data w x 0 n P backing)
      loopHeads (data w x (n*x) n P (UnaryProduct.scratch w x n backing)):=by
    have hin: data w x (0*x) n P (UnaryProduct.scratch w x 0 backing)=data w x 0 n P backing:=by
      rw [Nat.zero_mul];rfl
    refine padded.congr_in (by funext i;fin_cases i <;> rfl) ((padded_data w x (0*x) n P (UnaryProduct.scratch w x 0 backing)).trans hin) |>.congr (by funext i;fin_cases i <;> rfl)
      (padded_data w x (n*x) n P (UnaryProduct.scratch w x n backing))
  obtain ⟨r0,run0,rf0,_⟩:=DecompositionCountPosition.move_run advance (fun _=>0) (data w x 0 n P backing)
  have first:Step (DecompositionCountPosition.move advance) 1 (fun _=>0) (data w x 0 n P backing)
      loopHeads (data w x 0 n P backing):=by
    have actual:=Step.of_run run0 (congrArg Configuration.heads rf0) (congrArg Configuration.tapes rf0)
    exact actual.congr (by funext i;fin_cases i <;> rfl) rfl
  obtain ⟨r1,run1,rf1,_⟩:=DecompositionCountPosition.move_run retreat loopHeads
    (data w x (n*x) n P (UnaryProduct.scratch w x n backing))
  have last:Step (DecompositionCountPosition.move retreat) 1 loopHeads
      (data w x (n*x) n P (UnaryProduct.scratch w x n backing)) (fun _=>0)
      (data w x (n*x) n P (UnaryProduct.scratch w x n backing)):=by
    have actual:=Step.of_run run1 (congrArg Configuration.heads rf1) (congrArg Configuration.tapes rf1)
    exact actual.congr (by funext i;fin_cases i <;> rfl) rfl
  exact ((first.seq middle).seq last).enlarge (by unfold budget;omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.UnaryProductReady
