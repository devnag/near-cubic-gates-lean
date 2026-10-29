import SourceAdapters.Proximity.Pairing
import Proof.Gates.Cells.Loop

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": compute and append one odd auxiliary key
using the actual pairing program followed by paid copy, shift and increment. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.PairKeys

open NearCubicGates.Close.Cells NearCubicGates.Adapters.Proximity.Pairing

def step (R : Fin 4 ↪ Fin VV) (address : Fin VV) (store : Fin MM) : St VV MM :=
  .seq (pairProgram R) (.seq (.op (.copy address (R 3)))
    (.seq (.op (.shl address)) (.seq (.op (.inc address)) (.op (.wrM store address)))))

def written (R : Fin 4 ↪ Fin VV) (address : Fin VV) (store : Fin MM)
    (a : DS VV MM) (row index : ℕ) : DS VV MM :=
  (((a.set (R 2) (max row index)).set (R 3) (Nat.pair row index)).set address
    (2 * Nat.pair row index + 1)).put store (2 * Nat.pair row index + 1)

theorem step_runs (C : Ctx) (R : Fin 4 ↪ Fin VV) (address : Fin VV) (store : Fin MM)
    (ha : address ≠ R 3) (a : DS VV MM) (row index : ℕ)
    (hr : a.env (R 0) = row) (hi : a.env (R 1) = index)
    (hwidth : 2 * Nat.pair row index + 1 < 2 ^ C.Wd)
    (hcursor : a.rc store ≤ (a.ram store).length) :
    Ex C (step R address store) a (written R address store a row index) 16 := by
  let p := (a.set (R 2) (max row index)).set (R 3) (Nat.pair row index)
  have ep := pair_program C R a row index hr hi (by omega)
  have ec : Ex C (.op (.copy address (R 3))) p (p.set address (Nat.pair row index)) 1 := by
    simpa only [p, DS.set_env_self] using Ex.op (OpEx.copy (C := C) address (R 3) p ha)
  let q := p.set address (Nat.pair row index)
  have es : Ex C (.op (.shl address)) q (q.set address (2 * Nat.pair row index)) 1 := by
    have e := Ex.op (OpEx.shl (C := C) address q (by simp only [q, DS.set_env_self]; omega))
    simpa only [q, DS.set_env_self] using e
  let d := q.set address (2 * Nat.pair row index)
  have ei : Ex C (.op (.inc address)) d (d.set address (2 * Nat.pair row index + 1)) 1 := by
    have e := Ex.op (OpEx.inc (C := C) address d (by simpa only [d, DS.set_env_self] using hwidth))
    simpa only [d, DS.set_env_self] using e
  let f := d.set address (2 * Nat.pair row index + 1)
  have ew : Ex C (.op (.wrM store address)) f (f.put store (2 * Nat.pair row index + 1)) 1 := by
    simpa only [f, DS.set_env_self] using Ex.op (OpEx.wrM (C := C) store address f hcursor)
  have e := Ex.seq ep (Ex.seq ec (Ex.seq es (Ex.seq ei ew)))
  simpa only [step, written, f, d, q, p, DS.set, Function.update_idem, Nat.reduceAdd] using e

/-- Single key append with all unaffected data and channels recorded. -/
theorem step_spec (C : Ctx) (R : Fin 4 ↪ Fin VV) (address : Fin VV) (store : Fin MM)
    (ha : address ≠ R 3) (a : DS VV MM) (row index : ℕ)
    (hr : a.env (R 0) = row) (hi : a.env (R 1) = index)
    (hwidth : 2 * Nat.pair row index + 1 < 2 ^ C.Wd)
    (hcursor : a.rc store = (a.ram store).length) :
    Hs C (step R address store) a 16 (fun b =>
      b.ram = Function.update a.ram store (a.ram store ++ [2 * Nat.pair row index + 1]) ∧
      b.rc = Function.update a.rc store (a.rc store + 1) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      Fr a b [R 2, R 3, address]) := by
  refine ⟨written R address store a row index, 16,
    step_runs C R address store ha a row index hr hi hwidth hcursor.le, le_rfl,
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simp [written, DS.put, putAt, hcursor]
  · exact (Fr.set a _ (by simp)).trans
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))

end NearCubicGates.Adapters.Code.PairKeys
