import Proof.CaseAnalysis.RowsTouchingUnaryProductReady
import Proof.CaseAnalysis.RowsTouchingChoiceGuard
import Proof.Amplification.RecoveryPrefixCompare

/-! Both small-factor products share the same scratch and logs. Their
accumulators are physically overwritten from one retained zero frame. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  left : List Bool
  right : List Bool
  scratch : List Bool
  flag : Bool

def data (w a b k h P : ℕ) (st : Store):Fin 12→List Bool:=
  ![frame (binary w a),frame (binary w b),ZeroPadding.pad P (CompareMachine.word k),
    ZeroPadding.pad P (CompareMachine.word h),st.left,st.right,st.scratch,
    List.replicate (4*w+3) false,List.replicate (2*w+1) false,[st.flag],frame (binary w 0),
    List.replicate (2*w+1) true]
def slot (right : Bool):Fin 12:=if right then 5 else 4
def value (right : Bool) (a b : ℕ):ℕ:=if right then b else a
def factor (right : Bool) (k h : ℕ):ℕ:=if right then h else k
def field (right : Bool) (st : Store):List Bool:=if right then st.right else st.left
def setField (right : Bool) (st : Store) (word : List Bool):Store:=
  { st with left:=if right then st.left else word, right:=if right then word else st.right }
def reset (right : Bool) (w : ℕ) (st : Store):Store:=setField right st (frame (binary w 0))
def product (right : Bool) (w a b k h : ℕ) (st : Store):Store:=
  let x:=value right a b
  let n:=factor right k h
  { setField right st (frame (binary w (n*x))) with scratch:=UnaryProduct.scratch w x n st.scratch }
def compared (a b k h : ℕ) (st : Store):Store:={st with flag:=decide (k*a≤h*b)}
def output (a b k h : ℕ) (st : Store):Store:={st with flag:=decide (0<k)&&decide (k*a≤h*b)}

def copySlots (right : Bool):Fin 4→Fin 12:=![10,slot right,11,7]
def productSlots (right : Bool):Fin 6→Fin 12:=![if right then 1 else 0,slot right,6,7,8,if right then 3 else 2]
def compareSlots:Fin 4→Fin 12:=![4,5,9,7]
def guardSlots:Fin 2→Fin 12:=![2,9]
theorem copy_injective (right : Bool):Function.Injective (copySlots right):=by cases right <;> decide
theorem product_injective (right : Bool):Function.Injective (productSlots right):=by cases right <;> decide
noncomputable def copy (right : Bool):=RecoveryFocus.machine (copySlots right) RecoveryBoundedTapeCopy.machine
noncomputable def multiply (right : Bool):=RecoveryFocus.machine (productSlots right) UnaryProductReady.machine
noncomputable def compare:=RecoveryFocus.machine compareSlots RecoveryPrefixCompare.machine
noncomputable def guard:=RecoveryFocus.machine guardSlots ChoiceGuard.machine
noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (copy false) (copy true)) (multiply false)) (multiply true)) compare) guard
def budget (w k h : ℕ):=(k+h)*(12*w+16)+12*w+41

def afterProducts (w a b k h : ℕ) (st : Store):Store:=
  product true w a b k h (product false w a b k h (reset true w (reset false w st)))
def after (w a b k h : ℕ) (st : Store):Store:=output a b k h (afterProducts w a b k h st)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Choice
