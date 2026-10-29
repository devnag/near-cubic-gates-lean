import SourceAdapters.Proximity.TrimHonestAppendState
import SourceAdapters.Proximity.CoinLoop

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the numeric source-row loop retains every accumulated
auxiliary row and the exact schedule used by final restriction. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

def rowProgram (q : ℕ) : St VV MM := .seq (HonestRowTable.script q) appendRow
def rowTemps : List (Fin VV) := HonestRowTable.scratch ++ appendTemps
def loopTemps : List (Fin VV) := QueryStep.rowReg :: rowTemps
def rowCost (q n N sourceLength Lk Bk Λ : ℕ) : ℕ :=
  HonestRowTable.cost q n N sourceLength Lk Bk Λ +
    (6 * (blockVariableBound q) ^ 2 + 40 * blockVariableBound q + 11) + 1

structure LoopState {n q N : ℕ} (V : NonadaptiveVerifier n q) (C : Ctx)
    (input : BitInput n) (proof : BitInput N) (sourceLength inputCursor : ℕ)
    (a b : DS VV MM) (rows : ℕ) : Prop where
  ready : HonestRowTable.Ready C input proof q sourceLength inputCursor b
  auxiliary : AuxiliaryReady V input (finiteProofOracle proof) rows b
  out : b.out = a.out
  schedule : b.ram scheduleStore = a.ram scheduleStore
  schedule_cursor : b.rc scheduleStore = a.rc scheduleStore
  vars : Fr a b loopTemps

theorem ready_set_row {n q N L cursor : ℕ} {C : Ctx} {input : BitInput n} {proof : BitInput N}
    {a : DS VV MM} (h : HonestRowTable.Ready C input proof q L cursor a) (v : ℕ) :
    HonestRowTable.Ready C input proof q L cursor (a.set QueryStep.rowReg v) :=
  ⟨h.source.set_row v, h.oracle.set QueryStep.rowReg v (by decide) (by decide),
    h.answers_length, h.answers_cursor, h.row_length, h.row_cursor,
    by simpa [DS.set, localBound, QueryStep.rowReg] using h.local_bound⟩

theorem LoopState.set_row {n q N L cursor rows : ℕ} {V : NonadaptiveVerifier n q} {C : Ctx}
    {input : BitInput n} {proof : BitInput N} {a b : DS VV MM}
    (h : LoopState V C input proof L cursor a b rows) (v : ℕ) :
    LoopState V C input proof L cursor a (b.set QueryStep.rowReg v) rows :=
  ⟨ready_set_row h.ready v, h.auxiliary.set QueryStep.rowReg v (by decide), h.out,
    h.schedule, h.schedule_cursor, h.vars.trans (Fr.set b v (by simp [loopTemps]))⟩

end NearCubicGates.Adapters.Proximity.TrimHonest
