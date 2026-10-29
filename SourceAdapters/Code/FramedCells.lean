import SourceAdapters.Code.CountedParsing

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": a paid cell-program transformation which frames every
output bit. It supplies the exact outer frame required by ordinary composition. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.FramedCells

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells

variable {V M : ℕ}

def state (a : DS V M) : DS V M := {a with out := Streaming.marks a.out}

def operation : Op V M → St V M
  | .emit b => .seq (.op (.emit true)) (.op (.emit b))
  | o => .op o

def script : St V M → St V M
  | .op o => operation o
  | .seq s t => .seq (script s) (script t)
  | .ite c s t => .ite c (script s) (script t)
  | .loop c s => .loop c (script s)

theorem operation_runs (C : Ctx) {o : Op V M} {a b : DS V M} {n : ℕ} (h : OpEx C o a b n) :
    Ex C (operation o) (state a) (state b) (3 * n) := by
  cases h with
  | zero x a => exact (Ex.op (OpEx.zero x (state a))).mono (by omega)
  | inc x a hc => exact (Ex.op (OpEx.inc x (state a) hc)).mono (by omega)
  | add x y a hxy hc => exact (Ex.op (OpEx.add x y (state a) hxy hc)).mono (by omega)
  | sub x y a hxy hc => exact (Ex.op (OpEx.sub x y (state a) hxy hc)).mono (by omega)
  | copy x y a hxy => exact (Ex.op (OpEx.copy x y (state a) hxy)).mono (by omega)
  | half x a => exact (Ex.op (OpEx.half x (state a))).mono (by omega)
  | shl x a hc => exact (Ex.op (OpEx.shl x (state a) hc)).mono (by omega)
  | mul x y z a hxy hxz hyz hc => exact (Ex.op (OpEx.mul x y z (state a) hxy hxz hyz hc)).mono (by omega)
  | dm x y q r a hxy hxq hxr hyq hyr hqr hp hc =>
    exact (Ex.op (OpEx.dm x y q r (state a) hxy hxq hxr hyq hyr hqr hp hc)).mono (by omega)
  | rdI x a hi => exact (Ex.op (OpEx.rdI x (state a) hi)).mono (by omega)
  | bkI a hi => exact (Ex.op (OpEx.bkI (state a) hi)).mono (by omega)
  | emit bit a =>
    have e1 := Ex.op (OpEx.emit (C := C) true (state a))
    have e2 := Ex.op (OpEx.emit (C := C) bit {state a with out := (state a).out ++ [true]})
    simpa [state, operation, Streaming.marks, List.flatMap_append, List.append_assoc] using Ex.seq e1 e2
  | rdM m x a hi => exact (Ex.op (OpEx.rdM m x (state a) hi)).mono (by omega)
  | wrM m x a hi => exact (Ex.op (OpEx.wrM m x (state a) hi)).mono (by omega)
  | rwM m a => exact (Ex.op (OpEx.rwM m (state a))).mono (by simp [state])
  | srtM m a hi => exact (Ex.op (OpEx.srtM m (state a) hi)).mono (by simp [state])
  | kem bit a hi => exact (Ex.op (OpEx.kem bit (state a) hi)).mono (by omega)
  | kcall r a hin hb => exact (Ex.op (OpEx.kcall r (state a) hin hb)).mono (by omega)
  | rdK x a hi => exact (Ex.op (OpEx.rdK x (state a) hi)).mono (by omega)

theorem runs (C : Ctx) {s : St V M} {a b : DS V M} {n : ℕ} (h : Ex C s a b n) :
    Ex C (script s) (state a) (state b) (3 * n) := by
  induction h with
  | op h => exact operation_runs C h
  | seq h1 h2 ih1 ih2 => exact (Ex.seq ih1 ih2).mono (by omega)
  | @iteT c s t a b n hc he h ih =>
    exact (Ex.iteT (c := c) (s := script s) (t := script t) hc
      (show c.eval (state a) = true from he) ih).mono (by omega)
  | @iteF c s t a b n hc he h ih =>
    exact (Ex.iteF (c := c) (s := script s) (t := script t) hc
      (show c.eval (state a) = false from he) ih).mono (by omega)
  | @loopF c s a hc he =>
    exact (Ex.loopF (c := c) (s := script s) (a := state a) hc he).mono (by omega)
  | @loopT c s a b d n k hc he h1 h2 ih1 ih2 =>
    exact (Ex.loopT (c := c) hc (show c.eval (state a) = true from he) ih1 ih2).mono (by omega)
  | mono h hnm ih => exact ih.mono (by omega)

def framed (s : St V M) : St V M := .seq (script s) (.op (.emit false))

theorem framed_runs (C : Ctx) {s : St V M} {b : DS V M} {n : ℕ} (h : Ex C s a0 b n) :
    ∃ c, Ex C (framed s) a0 c (3 * n + 2) ∧ c.out = frame b.out := by
  have e1 := runs C h
  have hinit : state (a0 : DS V M) = a0 := by rfl
  rw [hinit] at e1
  have e2 := Ex.op (OpEx.emit (C := C) false (state b))
  refine ⟨_, Ex.seq e1 e2, ?_⟩
  exact (NearCubicGates.Close.CounterMachine.CellTablesProg.frame_marks b.out).symm

end NearCubicGates.Adapters.Code.FramedCells
