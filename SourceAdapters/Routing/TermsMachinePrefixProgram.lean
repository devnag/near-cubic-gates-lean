import SourceAdapters.Routing.TermsMachineEmit
import SourceAdapters.Routing.TermsMachinePrefixData

/-! The construction in `lem:generator`: numerical coordinate-prefix printing, in count or output mode. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Prefix

open ShortPCP.Machines.FL

/-- Prepare the three numerical gate fields and count or output that gate. -/
def emitGate (tag : ℕ) (x y : E) : S :=
  .seq (.set 7 (.k tag)) (.seq (.set 8 x) (.seq (.set 9 y) gateStep))

def coefficient : E :=
  .md (.shr (.v 22) (.mul (.add (.mul (.v 34) (.v 21)) (.v 35)) (.v 20)))
    (.shl (.k 1) (.v 20))

def squareStep : S := emitGate 3 (.add (.v 33) (.v 34)) (.add (.v 33) (.v 34))

def termStep : S :=
  .seq (emitGate 1 coefficient (.k 0))
    (.seq (emitGate 3 (.sub (.v 24) (.k 1)) (.add (.v 33) (.v 35)))
      (emitGate 2 (.add (.v 36) (.mul (.k 3) (.v 35))) (.sub (.v 24) (.k 1))))

def rowStep : S :=
  .seq (.set 36 (.v 24)) (.seq (emitGate 1 (.k 0) (.k 0)) (.loop 35 (.v 21) termStep))

/-- Save the initial gate index, emit its powers, then every coordinate row. -/
def program : S :=
  .seq (.set 33 (.v 24)) (.seq (emitGate 0 (.k 0) (.k 0))
    (.seq (.loop 34 (.sub (.v 21) (.k 1)) squareStep) (.loop 34 (.v 21) rowStep)))

def gateWrites : List Var := [5, 6, 7, 8, 9, 24]
def termWrites : List Var := gateWrites
def rowWrites : List Var := gateWrites ++ [35, 36]
def writes : List Var := gateWrites ++ [33, 34, 35, 36, 37]

theorem emitGate_wf (tag : ℕ) (x y : E) (d : ℕ) (hd : d < 8)
    (hx : dE x < 16) (hy : dE y < 16) : wfS (emitGate tag x y) d = true := by
  simp [emitGate, wfS, dE, gateStep_wf d hd, hx, hy]

theorem wellFormed (d : ℕ) (hd : d ≤ 5) : wfS program d = true := by
  simp [program, rowStep, termStep, squareStep, emitGate, coefficient, wfS, dE,
    gateStep_wf d (by omega), gateStep_wf (d+1) (by omega),
    gateStep_wf (d+1+1) (by omega), show d < 8 by omega, show d+1 < 8 by omega]

theorem depth : dpS program = 3 := by decide

theorem cost_le (G : Glob) :
    costS G program ≤ 8 * szS program * opc G * (G.N+1)^3 := by
  simpa only [depth] using costS_le G program

/-- The standard FL compiler implements this fixed program with its stated cost. -/
theorem compiled {C : NearCubicGates.Close.Cells.Ctx} {G : Glob}
    (hg : GOk C G) (hinp : C.inp = G.inp) : SOk C G program :=
  compS_ok hg hinp program

end NearCubicGates.Adapters.Routing.TermsMachine.Prefix
