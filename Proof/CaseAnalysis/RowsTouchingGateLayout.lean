import Proof.CaseAnalysis.RowsTouchingGateSummary
import Proof.CaseAnalysis.RowsTouchingScoreBlockRun

/-! One original support record feeds both exact complement sums. The
single summary count and physical flags are shared by the two queries. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey SupportScan
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  summary : Fin 3→List Bool
  narrow : List Bool
  wide : List Bool
  scratch : List Bool
  excluded : ℕ
  included : ℕ

def extra (q k w P : ℕ) (st : Store):Fin 15→List Bool:=
  ![PascalTable.table q,UnaryTemplate.tape (PascalReady.width q),ZeroPadding.pad P (CompareMachine.word k),
    st.narrow,List.replicate (PascalReady.width q) false,[],st.wide,CompareMachine.word w,
    List.replicate (2*w+1) true,frame (binary w st.excluded),frame (binary w st.included),st.scratch,
    List.replicate (4*w+3) false,List.replicate (2*w+1) false,ZeroPadding.pad P (CompareMachine.word (k-1))]
def data (q k w P C : ℕ) (source : List Bool) (xs : List Cell) (st : Store) (i : Fin 24):List Bool:=
  Fin.addCases (m:=9) (n:=15) (motive:=fun _=>List Bool)
    (GateSummary.data P C source xs st.summary) (extra q k w P st) i
def heads (pos : ℕ) (i : Fin 24):ℕ:=if i=0 then pos else 0

def summarized (st : Store) (P : ℕ) (xs : List Cell):Store:={st with summary:=GateSummary.result P xs}
def scoreStore (st : Store) (withCandidate : Bool):ScoreBlock.Store:=
  ⟨st.narrow,st.wide,st.scratch,if withCandidate then st.included else st.excluded⟩
def installScore (st : Store) (withCandidate : Bool) (score : ScoreBlock.Store):Store:=
  { st with
    narrow := score.narrow
    wide := score.wide
    scratch := score.scratch
    excluded := if withCandidate then st.excluded else score.accumulator
    included := if withCandidate then score.accumulator else st.included }
def key (withCandidate : Bool) (k : ℕ):ℕ:=if withCandidate then k-1 else k

def blockSlots (withCandidate : Bool):Fin 17→Fin 24:=
  ![9,10,4,if withCandidate then 23 else 11,12,14,13,7,15,16,17,if withCandidate then 19 else 18,20,21,22,5,6]
theorem block_injective (withCandidate : Bool):Function.Injective (blockSlots withCandidate):=by
  cases withCandidate <;> decide
noncomputable def summary:=TapeEmbedding.machine 15 GateSummary.machine
noncomputable def block (withCandidate : Bool):=RecoveryFocus.machine (blockSlots withCandidate) (ScoreBlock.machine withCandidate)
noncomputable def machine:=Composition.machine (Composition.machine summary (block false)) (block true)
def budget (q m k w P : ℕ):=2*P+4*q+13+1+ScoreBlock.budget q m k w+1+ScoreBlock.budget q m (k-1) w

def scored (st : Store) (q m k w : ℕ) (withCandidate hit cur : Bool):Store:=
  installScore st withCandidate
    (ScoreBlock.after (scoreStore st withCandidate) q m (key withCandidate k) w withCandidate hit cur)
def after (st : Store) (q k w P : ℕ) (xs : List Cell):Store:=
  let ready:=summarized st P xs
  let excluded:=scored ready q (count xs) k w false (xs.any touched) (xs.any current)
  scored excluded q (count xs) k w true (xs.any touched) (xs.any current)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
