import Proof.CaseAnalysis.RowsTouchingChoiceCalls

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem choice_run (w a b k h P : ℕ) (st : Store)
    (hl:st.left.length≤2*w+1) (hr:st.right.length≤2*w+1) (hs:st.scratch.length≤2*w+1)
    (hleft:k*a<2^w) (hright:h*b<2^w):
    Step machine (budget w k h) (fun _=>0) (data w a b k h P st)
      (fun _=>0) (data w a b k h P (after w a b k h st)):=by
  have zeroLeft:=copy_run false w a b k h P st hl
  have zeroRight:=copy_run true w a b k h P (reset false w st) hr
  have left:=product_run false w a b k h P (reset true w (reset false w st)) rfl hs hleft
  have scratch:(product false w a b k h (reset true w (reset false w st))).scratch.length≤2*w+1:=by
    cases k with
    | zero=>exact hs
    | succ k=>simp [product,UnaryProduct.scratch,value,factor,frame_length,binary_length]
  have right:=product_run true w a b k h P
    (product false w a b k h (reset true w (reset false w st))) rfl scratch hright
  have ordered:=compare_run w a b k h P (afterProducts w a b k h st) rfl rfl hleft hright
  have guarded:=guard_run w a b k h P (afterProducts w a b k h st)
  exact (((((zeroLeft.seq zeroRight).seq left).seq right).seq ordered).seq guarded).enlarge (by
    simp [budget,UnaryProductReady.budget,UnaryProduct.budget,factor,Nat.add_mul]
    omega)

theorem after_fields (w a b k h : ℕ) (st : Store):
    (after w a b k h st).left=frame (binary w (k*a)) ∧
    (after w a b k h st).right=frame (binary w (h*b)) ∧
    (after w a b k h st).flag=(decide (0<k)&&decide (k*a≤h*b)):=⟨rfl,rfl,rfl⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
