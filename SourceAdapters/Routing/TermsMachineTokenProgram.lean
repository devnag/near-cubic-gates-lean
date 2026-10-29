import SourceAdapters.Routing.TermsMachineTokenApply
import SourceAdapters.Routing.TermsMachineExpressionData

/-! Literal dispatch and bounded postfix-expression printing. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Expression

open ShortPCP.Machines.FL

def dispatch : S :=
  .ite (.eq (.v 38) (.k 0)) (applyToken 1 (.v 39) (.k 0) 0)
    (.ite (.eq (.v 38) (.k 1)) (.seq resolveRead (applyToken 0 (.v 15) (.k 0) 0))
      (.ite (.eq (.v 38) (.k 2)) (applyToken 2 (stackAt 1) (stackAt 0) 2)
        (.ite (.eq (.v 38) (.k 3)) (applyToken 3 (stackAt 1) (stackAt 0) 2)
          (applyToken 3 (stackAt 0) (stackAt 0) 1))))

def body : S := .seq readToken
  (.ite (.eq (.v 38) (.k 5)) (.set 40 (.k 0)) dispatch)

def loopProgram : S := .whl (.v 40) body

def program : S := .seq (.set 28 (.k 0)) (.seq (.set 29 (.k 0))
  (.seq (.set 40 (.k 1)) loopProgram))

def dispatchWrites : List Var := [5, 6, 7, 8, 9, 15, 24, 28, 29, 43, 46]
def writes : List Var := [5, 6, 7, 8, 9, 14, 15, 24, 28, 29, 38, 39, 40, 43, 46]

theorem dispatch_wf (d : ℕ) (hd : d ≤ 7) : wfS dispatch d = true := by
  simp [dispatch, wfS, dE, applyToken_wf _ _ _ _ d (by omega),
    resolveRead_wf d hd, stackAt]

theorem wellFormed (d : ℕ) (hd : d ≤ 6) : wfS program d = true := by
  simp [program, loopProgram, body, wfS, dE, readToken_wf (d+1) (by omega),
    dispatch_wf (d+1) (by omega), show d < 8 by omega]

theorem depth : dpS program = 2 := by decide

theorem cost_le (G : Glob) : costS G program ≤ 8*szS program*opc G*(G.N+1)^2 := by
  simpa only [depth] using costS_le G program

theorem compiled {C : NearCubicGates.Close.Cells.Ctx} {G : Glob}
    (hg : GOk C G) (hinp : C.inp = G.inp) : SOk C G program := compS_ok hg hinp program

end NearCubicGates.Adapters.Routing.TermsMachine.Expression
