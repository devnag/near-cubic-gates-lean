import Proof.CaseAnalysis.RecoveryUnaryReuse

/-! Exact reusable bank for the original unary-expression call. This is the
same literal bank retained after the two child-field selectors. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUnaryReuse
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def baseHeads (out : List Bool) : Fin 36→ℕ:=
  Fin.addCases (m:=29) (n:=7) (motive:=fun _=>ℕ) (PCPPNativeClauseBank.heads out) ![0,0,0,0,0,0,1]
def heads (out : List Bool) : Fin 37→ℕ:=Fin.addCases (m:=36) (n:=1) (motive:=fun _=>ℕ) (baseHeads out) (fun _=>0)
def baseData (index base C value limit : ℕ) (flag : Bool) (out : List Bool) : Fin 36→List Bool:=
  Fin.addCases (m:=29) (n:=7) (motive:=fun _=>List Bool) (RecoveryBoundedNativeFold.oldData index base C out)
    ![ZeroPadding.pad C [flag],List.replicate C false,List.replicate C false,
      List.replicate C false,List.replicate C false,ZeroPadding.pad C (List.replicate value true),CompareMachine.word limit]
def data (index base C D value limit : ℕ) (flag : Bool) (out : List Bool) : Fin 37→List Bool:=
  Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool) (baseData index base C value limit flag out)
    (fun _=>List.replicate D false)

theorem entry_heads {n bound : ℕ} (row : Fin (bound+1))
    (start base C D value limit : ℕ) (out : List Bool) :
    (entry (n:=n) row start base C D value limit out).heads=heads out := by
  funext i
  fin_cases i <;> rfl

theorem entry_tapes {n bound : ℕ} (row : Fin (bound+1))
    (start base C D value limit : ℕ) (out : List Bool) :
    (entry (n:=n) row start base C D value limit out).tapes=
      data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) base C D value limit false out := by
  change (fun i=>ZeroPadding.pad (Rewind.Workspace.capacities 36 D i)
    (Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool)
      (fun j=>ZeroPadding.pad (caps C j)
        ((RecoveryBoundedNativeUnaryJoin.entry (n:=n) row start base C value limit out []).tapes j))
      (fun _=>[]) i))=_
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [data,Rewind.Workspace.capacities,Fin.addCases_left,ZeroPadding.pad_zero]
    fin_cases j
    all_goals first | rfl | (change ZeroPadding.pad 0 _=_; exact ZeroPadding.pad_zero _)
  · simp only [data,Rewind.Workspace.capacities,Fin.addCases_right]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedUnaryReuse
