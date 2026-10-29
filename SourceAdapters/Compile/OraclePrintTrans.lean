import SourceAdapters.Compile.OraclePrintTransLocal
import SourceAdapters.Compile.OraclePrintTransQuery

/-!
proof of `thm:short-pcp-ours`, Step 4: complete pure template for a charged oracle round.
The fixed control/read table is syntax, while all tape and clock dimensions
are runtime parameters. Equality is exact postfix equality, not evaluation.
-/
namespace NearCubicGates.Adapters.Compile.OraclePrint
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
  NearCubicWires.LocalBitMultitape OracleExecution
set_option autoImplicit false

def transitionRowU (p : OrdinaryOracleProgram) (state : Fin p.base.stateCount)
    (scans : Fin p.base.tapeCount → Bool) : U :=
  if p.base.machine.halted state then .inp (.v 4) else
    match p.query state with
    | none => match p.base.machine.rule state scans with
      | none => .ofBool false
      | some action => .and (localGuardU p action 5) (localActionU p action)
    | some rule => .and (queryGuardU p 5) (queryActionU p rule)

def Tt (p : OrdinaryOracleProgram) : U :=
  .orList (List.ofFn fun state : Fin p.base.stateCount =>
    .orList (List.ofFn fun mask : Fin (2^p.base.tapeCount) =>
      .and (rowU state (scanMask mask) 5) (transitionRowU p state (scanMask mask))))

theorem Tt_eq (p : OrdinaryOracleProgram) (width cap ell dl : ℕ) (D : List Bool)
    (index : Fin (clockBits p width cap)) :
    postR (fun i => i.val) (clockTransitionExpression p width cap index)=
      (Tt p).toks D [width,cap,ell,dl,index.val] := by
  unfold clockTransitionExpression answerTableSelection Tt
  apply postR_anyOfFn_list
  intro state
  apply postR_anyOfFn_list
  intro mask
  simp only [postR,U.toks,postR_liftClock,postR_clockView]
  rw [rowU_eq (width := width) state (scanMask mask) D [width,cap,ell,dl,index.val] rfl (by simp)]
  congr 2
  unfold transitionRowU
  split
  · simp [postR,U.toks,Tm.eval]
  · cases hq : p.query state with
    | none =>
      cases hr : p.base.machine.rule state (scanMask mask) with
      | none => rfl
      | some action =>
        simp only [postR,U.toks,postR_liftClock,
          localGuardU_eq p width cap D [width,cap,ell,dl,index.val] rfl rfl (by simp),
          localActionU_eq p width cap ell dl D action index]
        rfl
    | some rule =>
      simp only [postR,U.toks,postR_liftClock,
        queryGuardU_eq p width cap D [width,cap,ell,dl,index.val] rfl rfl (by simp),
        queryActionU_eq p width cap ell dl D rule index]
      rfl

theorem Tt_eq_nat (p : OrdinaryOracleProgram) (r : OracleCompilationRequest) (j : ℕ)
    (hj : j<clockBits p (requestWidth r) r.fuel) :
    postR (fun i => i.val) (clockTransitionExpression p (requestWidth r) r.fuel ⟨j,hj⟩)=
      (Tt p).toks (RepairOrdinary.frame r.data)
        [requestWidth r,r.fuel,r.ell,(RepairOrdinary.frame r.data).length,j] :=
  Tt_eq p (requestWidth r) r.fuel r.ell (RepairOrdinary.frame r.data).length _ ⟨j,hj⟩

end NearCubicGates.Adapters.Compile.OraclePrint
