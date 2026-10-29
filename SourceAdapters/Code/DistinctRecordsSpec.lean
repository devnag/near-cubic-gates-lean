import Proof.Gates.Cells.Loop
import Mathlib.Data.List.Destutter
import Mathlib.Data.Finset.Sort

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": specification for a paid scan of sorted numeric records.
Only the interface is declared here. A separate construction must provide
an actual Cells program and prove this contract. No execution is assumed. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.DistinctRecords

open NearCubicGates.Close.Cells

/-- Caller-selected registers; `c0` and `vJ` are additional fixed scratch. -/
structure Registers where
  length : Fin VV
  count : Fin VV
  current : Fin VV
  previous : Fin VV
  started : Fin VV

def scratch (r : Registers) : List (Fin VV) :=
  [c0, vJ, r.current, r.previous, r.started, r.count]

/-- The retained length and scratch registers are disjoint; constants survive. -/
def Registers.Valid (r : Registers) : Prop :=
  (r.length :: scratch r).Nodup ∧
  vZ ∉ scratch r ∧ v1 ∉ scratch r ∧ v2 ∉ scratch r

/-- Exact sorted distinct output and preservation of all other live state.
For a nondecreasing input, `dedup` equals its increasing finite-set list. -/
def Post (r : Registers) (source destination : Fin MM) (a : DS VV MM)
    (records : List ℕ) (b : DS VV MM) : Prop :=
  b.ram destination = records.dedup ∧ b.ram source = records ∧
  b.env r.count = records.dedup.length ∧ b.env r.length = records.length ∧
  b.rc source = records.length ∧ b.rc destination = records.dedup.length ∧
  Cst b ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
  (∀ m, m ≠ source → m ≠ destination → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧
  Fr a b (scratch r)

/-- A record-count linear contract. The numeric values are compared and copied,
never used as iteration bounds. The implementation must initialize a separate
first-record flag, so zero is handled as an ordinary record value. -/
def Contract (r : Registers) (source destination : Fin MM) (program : St VV MM) : Prop :=
  r.Valid → source ≠ destination →
  ∀ (C : Ctx) (a : DS VV MM) (records : List ℕ),
    Cst a → records.Pairwise (· ≤ ·) →
    a.ram source = records → a.rc source = 0 →
    a.ram destination = [] → a.rc destination = 0 →
    a.env r.length = records.length → records.length < 2 ^ C.Wd →
    (∀ value ∈ records, value < 2 ^ C.Wd) →
    Hs C program a (20 * (records.length + 1)) (Post r source destination a records)

end NearCubicGates.Adapters.Code.DistinctRecords
