import Proof.CaseAnalysis.RowsTouchingChoicePorts
import Proof.CaseAnalysis.RowsTouchingChoiceLocal

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copy_run (mode : Bool) (w a b k h P : ℕ) (st : Store)
    (hb:(field mode st).length≤2*w+1):
    Step (copy mode) (4*w+6) (fun _=>0) (data w a b k h P st)
      (fun _=>0) (data w a b k h P (reset mode w st)):=by
  have actual:=zero_copy w (field mode st) hb
  have focused:=actual.dock (copySlots mode) (copy_injective mode) (fun _=>0)
    (data w a b k h P st) (by intro j;rfl) (by intro j;cases mode <;> fin_cases j <;> rfl)
  have installed:install (copySlots mode) (data w a b k h P st)
      ![frame (binary w 0),frame (binary w 0),List.replicate (2*w+1) true,List.replicate (4*w+3) false]=
      data w a b k h P (reset mode w st):=by
    exact copy_installed _ _ _ _ _ _ _ _ _ _ _ _ mode
  exact focused.congr (dockH_existing _ _ _ (by intro j;rfl)) installed

theorem product_run (mode : Bool) (w a b k h P : ℕ) (st : Store)
    (hz:field mode st=frame (binary w 0)) (hb:st.scratch.length≤2*w+1)
    (hfit:factor mode k h*value mode a b<2^w):
    Step (multiply mode) (UnaryProductReady.budget w (factor mode k h)) (fun _=>0)
      (data w a b k h P st) (fun _=>0) (data w a b k h P (product mode w a b k h st)):=by
  have actual:=UnaryProductReady.ready_run w (value mode a b) (factor mode k h) P st.scratch hb hfit
  have inputEq:∀ j,data w a b k h P st (productSlots mode j)=
      UnaryProductReady.data w (value mode a b) 0 (factor mode k h) P st.scratch j:=by
    intro j;cases mode <;> fin_cases j
    all_goals first | rfl | exact hz
  have focused:=actual.dock (productSlots mode) (product_injective mode) (fun _=>0)
    (data w a b k h P st) (by intro j;rfl) inputEq
  have installed:install (productSlots mode) (data w a b k h P st)
      (UnaryProductReady.data w (value mode a b) (factor mode k h*value mode a b)
        (factor mode k h) P (UnaryProduct.scratch w (value mode a b) (factor mode k h) st.scratch))=
      data w a b k h P (product mode w a b k h st):=by
    cases mode <;> exact product_installed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact focused.congr (dockH_existing _ _ _ (by intro j;rfl)) installed

theorem compare_run (w a b k h P : ℕ) (st : Store)
    (hl:st.left=frame (binary w (k*a))) (hr:st.right=frame (binary w (h*b)))
    (hleft:k*a<2^w) (hright:h*b<2^w):
    Step compare (4*w+8) (fun _=>0) (data w a b k h P st)
      (fun _=>0) (data w a b k h P (compared a b k h st)):=by
  have actual:=Step.of_ready (RecoveryPrefixCompare.compare_ready (binary w (k*a)) (binary w (h*b))
    st.flag (4*w+3) (by simp [binary_length]))
  simp only [binary_length,binary_value w (k*a) hleft,binary_value w (h*b) hright,
    Nat.max_eq_left (by omega : 2*w+3≤4*w+3)] at actual
  have focused:=actual.dock compareSlots (by decide) (fun _=>0) (data w a b k h P st)
    (by intro j;rfl) (by intro j;fin_cases j;exact hl;exact hr;rfl;rfl)
  have installed:install compareSlots (data w a b k h P st)
      ![frame (binary w (k*a)),frame (binary w (h*b)),[decide (k*a≤h*b)],List.replicate (4*w+3) false]=
      data w a b k h P (compared a b k h st):=by
    rw [←hl,←hr]
    exact compare_installed _ _ _ _ _ _ _ _ _ _ _ _ _
  exact focused.congr (dockH_existing _ _ _ (by intro j;rfl)) installed

theorem guard_run (w a b k h P : ℕ) (st : Store):
    Step guard 2 (fun _=>0) (data w a b k h P (compared a b k h st))
      (fun _=>0) (data w a b k h P (output a b k h st)):=by
  have actual:=ChoiceGuard.guard_run k P (decide (k*a≤h*b))
  have focused:=actual.dock guardSlots (by decide) (fun _=>0) (data w a b k h P (compared a b k h st))
    (by intro j;rfl) (by intro j;fin_cases j <;> rfl)
  have installed:install guardSlots (data w a b k h P (compared a b k h st))
      (ChoiceGuard.data k P (decide (0<k)&&decide (k*a≤h*b)))=data w a b k h P (output a b k h st):=by
    exact guard_installed _ _ _ _ _ _ _ _ _ _ _ _ _
  exact focused.congr (dockH_existing _ _ _ (by intro j;rfl)) installed

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
