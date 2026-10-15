import Proof.CaseAnalysis.RecoveryAddressBranch

/-! Literal projections of the retained address bank avoid repeatedly
unfolding the nested compiler bank when the common tail changes scalars. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem data_explicit (index base C D value limit : ℕ) (flag : Bool)
    (out source stack : List Bool) (retained : ℕ) :
    data index base C D value limit flag out source stack retained=
      ![[],ZeroPadding.pad C (List.replicate index true),
        List.replicate C false,List.replicate C false,List.replicate C false,
        List.replicate C false,List.replicate C false,List.replicate C false,
        List.replicate C false,List.replicate C false,List.replicate C false,
        List.replicate C false,List.replicate C false,List.replicate C false,
        List.replicate C false,List.replicate C false,List.replicate C false,
        List.replicate C false,List.replicate C false,List.replicate C false,
        out,List.replicate C false,List.replicate C true,List.replicate (C+1) false,
        [],List.replicate base true,[],[],[],ZeroPadding.pad C [flag],
        List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false,
        ZeroPadding.pad C (List.replicate value true),RepairSource.VerifierDecoding.CompareMachine.word limit,
        List.replicate D false,source,stack,List.replicate retained true] := by
  funext i
  fin_cases i <;> rfl

theorem heads_explicit (out stack : List Bool) (pos : ℕ) :
    heads out stack pos=
      ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,out.length,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,pos,stack.length,0] := by
  funext i
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
