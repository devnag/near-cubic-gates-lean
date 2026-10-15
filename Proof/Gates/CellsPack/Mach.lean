import Proof.Gates.CellsPack.Out

set_option autoImplicit false

namespace NearCubicGates.Close.CellsPack

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Counter
open NearCubicWires.RepairOrdinary (WordFunction)

def pkIn {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : List Bool := cellInput r ++ cellWord r.c r.p r.wt

noncomputable def pkOut {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : List Bool :=
  ratWord (certainSum r.c r.p r.wt) ++ natWord (uncCount r.c r.p r.wt)

def mainQ (mainP : St VV MM) : St VV MM := .seq mainP outP

/-- Adequate size constants. -/
def SzOK (S : SolveMachine) (B1 B2 : ℕ) (Bg : ℕ → ℕ) (z : Sz) : Prop :=
  ∀ (cT : ℕ) (r : CellReq B1 B2 cT), 3 ≤ z.W (leadOnes (pkIn r)) ∧
    wdNeed r.c r.p r.wt (Bg r.c.n) ≤ z.W (leadOnes (pkIn r)) ∧
    ∀ (y : Cells r.wt.I) (part : Option Bool) (κ : Role r.c × Fin r.p.J → ℤ), κ ∈ digitVectors r.c r.p r.wt y →
      (sysWord (sysOf r.c r.p r.wt y κ part)).length ≤ z.Lk (leadOnes (pkIn r)) ∧
        S.budget (sysOf r.c r.p r.wt y κ part) ≤ z.Bk (leadOnes (pkIn r))

/-- The run bound of `mainQ`. -/
def NOf (S : SolveMachine) (K e : ℕ) (Bg : ℕ → ℕ) (z : Sz) {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : ℕ :=
  loopCost K e (ctxOf (Callee.ofSolve S) z (pkIn r)) r.c r.p (Bg r.c.n) + outCost (z.W (leadOnes (pkIn r))) + 1

theorem run_ok (S : SolveMachine) (mainP : St VV MM) (K e : ℕ) (hL : LoopGoal mainP S K e) (B1 B2 : ℕ)
    (Bg : ℕ → ℕ) (hbits : ∀ (cT : ℕ) (r : CellReq B1 B2 cT), ∀ x ∈ CounterMachine.cellN r.c r.p r.wt,
      natBitLength x ≤ Bg r.c.n) (z : Sz) (hz : SzOK S B1 B2 Bg z) {cT : ℕ} (r : CellReq B1 B2 cT) :
    ∃ b n, Ex (ctxOf (Callee.ofSolve S) z (pkIn r)) (mainQ mainP) (a0 : DS VV MM) b n ∧ b.out = pkOut r ∧
      n ≤ NOf S K e Bg z r := by
  obtain ⟨h3, hwd, hcall⟩ := hz cT r
  obtain ⟨b, n, hex, hn, hcnt, hunc, hout, hcst⟩ := hL (ctxOf (Callee.ofSolve S) z (pkIn r)) r (Bg r.c.n) rfl rfl
    (hbits cT r) hwd hcall
  have hW1 : 1 ≤ (ctxOf (Callee.ofSolve S) z (pkIn r)).Wd := by show 1 ≤ z.W (leadOnes (pkIn r)); omega
  have hval := hex.valid hW1 (callee_hB _) (a0_valid _)
  obtain ⟨d, k, hx2, hk, hd⟩ := outP_spec (ctxOf (Callee.ofSolve S) z (pkIn r)) b hcst h3 (hval.env_lt vCnt)
    (hval.env_lt vUnc)
  refine ⟨d, n + k + 1, Ex.seq hex hx2, ?_, ?_⟩
  · rw [hd, hout, List.nil_append, pkOut]
    have hm : certainSum r.c r.p r.wt = ((b.env vCnt : ℕ) : ℚ) := hcnt.symm
    rw [hm, ratWord_natCast, hunc, List.append_assoc]
  · unfold NOf; have : k ≤ outCost (z.W (leadOnes (pkIn r))) := hk
    omega

noncomputable def machOf (S : SolveMachine) (mainP : St VV MM) (K e : ℕ) (hL : LoopGoal mainP S K e) (B1 B2 : ℕ)
    (Bg : ℕ → ℕ) (hbits : ∀ (cT : ℕ) (r : CellReq B1 B2 cT), ∀ x ∈ CounterMachine.cellN r.c r.p r.wt,
      natBitLength x ≤ Bg r.c.n) (z : Sz) (hz : SzOK S B1 B2 Bg z) (cT : ℕ) :
    WordFunction (CellReq B1 B2 cT) pkIn pkOut
      (fun r => langBudget (Callee.ofSolve S) z VV MM (pkIn r) (NOf S K e Bg z r)) :=
  wordFunction_of_lang pkIn pkOut (Callee.ofSolve S) z (mainQ mainP) (NOf S K e Bg z)
    (fun r => run_ok S mainP K e hL B1 B2 Bg hbits z hz r) (fun r => by have := (hz cT r).1; omega)

end NearCubicGates.Close.CellsPack
