import Proof.CaseAnalysis.RowsTouchingLookupCounted
import Proof.CaseAnalysis.RowsTouchingScoreWiden
import Proof.CaseAnalysis.RowsTouchingScoreAdd
import Proof.CaseAnalysis.RowsTouchingSingleDock

/-! One reusable complement-score update: exact table query, physical
binary widening, and a flag-selected update of one accumulator. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ScoreBlock
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  narrow : List Bool
  wide : List Bool
  scratch : List Bool
  accumulator : ℕ

def extra (w P : ℕ) (hit cur : Bool) (st : Store):Fin 9→List Bool:=
  ![st.wide,CompareMachine.word w,List.replicate (2*w+1) true,frame (binary w st.accumulator),
    st.scratch,List.replicate (4*w+3) false,List.replicate (2*w+1) false,
    ZeroPadding.pad P [hit],ZeroPadding.pad P [cur]]
def data (q m k w P C : ℕ) (hit cur : Bool) (st : Store) (i : Fin 17):List Bool:=
  Fin.addCases (m:=8) (n:=9) (motive:=fun _=>List Bool)
    (LookupCounted.input q m k P C st.narrow) (extra w P hit cur st) i

def queried (st : Store) (q m k : ℕ):Store:={st with narrow:=frame (binary (q+1) (Nat.choose m k))}
def widened (st : Store) (w x : ℕ):Store:={st with wide:=frame (binary w x)}
def updated (st : Store) (w x : ℕ) (withCandidate hit cur : Bool):Store:=
  if ScoreAdd.skip withCandidate hit cur then st else
    {st with accumulator:=x+st.accumulator,scratch:=frame (binary w (x+st.accumulator))}

def wideSlots : Fin 5→Fin 17:=![4,8,9,7,10]
def addSlots : Fin 7→Fin 17:=![8,11,12,13,14,15,16]
noncomputable def query:=TapeEmbedding.machine 9 LookupReady.machine
noncomputable def widen:=RecoveryFocus.machine wideSlots ScoreWiden.machine
noncomputable def add (withCandidate : Bool):=RecoveryFocus.machine addSlots (ScoreAdd.machine withCandidate)
noncomputable def machine (withCandidate : Bool):=Composition.machine (Composition.machine query widen) (add withCandidate)
def budget (q m k w : ℕ):=LookupReady.budget q m k+20*w+32

theorem wide_injective:Function.Injective wideSlots:=by decide
theorem add_injective:Function.Injective addSlots:=by decide

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ScoreBlock
