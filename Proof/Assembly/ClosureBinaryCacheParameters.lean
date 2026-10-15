import Proof.Assembly.ClosureBinaryCachePalette

/-! Exact scalar DAG consumed by the cold fanout. These equalities certify
the finite runtime arithmetic target; they do not supply physical words. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdParameters
open RepairOrdinary RepairRepresentation RepairSource.CloseoutFinal
open RepairSource.VerifierDecoding SignedSortKey

def B (L : Nat) := L+2
def w (L : Nat) := L+1
def X (L q : Nat) := B L+q+w L+1
def C (L : Nat) := 8*w L+12
def R (L q : Nat) := 1024*X L q^2
def S (L q N K W : Nat) := (16384*N+5120)*X L q^2+4*N+9*q+7*K+2*W+133
def U (L q N K W : Nat) := S L q N K W+1
def words (L q N K W : Nat) (membership : List Bool) : Fin 9→List Bool :=
  ![List.replicate (w L) true,RepairOrdinary.frame (binary (w L) 0),List.replicate (C L) true,
    CompareMachine.word q,membership,List.replicate (R L q) true,List.replicate (B L) true,
    CompareMachine.word N,List.replicate (S L q N K W) true]

theorem reserve_eq {q : Nat} (live : Finset (Fin q)) (gs : List (ExactThresholdGate q)) (L : Nat) :
    S L q gs.length live.card (natBitLength gs.length)=BinaryCacheColdPalette.S live gs (B L) (w L) := by
  unfold S X BinaryCacheColdPalette.S HardwireAssignments.reserve HardwireAssignmentsRaw.budget
    HardwireCacheLoop.budget HardwireCacheLoop.bodyBudget HardwireBudget.R
  ring

theorem capacity_eq {q : Nat} (live : Finset (Fin q)) (gs : List (ExactThresholdGate q)) (L : Nat) :
    U L q gs.length live.card (natBitLength gs.length)=BinaryCacheColdPalette.U live gs (B L) (w L) := by
  unfold U BinaryCacheColdPalette.U
  rw [reserve_eq]

theorem words_eq {q : Nat} (live : Finset (Fin q)) (gs : List (ExactThresholdGate q)) (L : Nat) :
    words L q gs.length live.card (natBitLength gs.length) (CloseoutRowsGateSupport.gateMembers live)=
      BinaryCacheColdPalette.words live gs (B L) (w L) := by
  simp only [words,BinaryCacheColdPalette.words,C,R,X,HardwireBudget.C,HardwireBudget.R,reserve_eq]

end NearCubicWires.P1Closure.BinaryCacheColdParameters
