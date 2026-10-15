import Proof.Gates.GateRecovery.Bundle

namespace GR

namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairRepresentation RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- Exact integer form of ceil(d_G log_2(q+2)), with fixed d_G. -/
def clauseWidth (degree q : Nat) := Nat.clog 2 ((q+2)^degree)
/-- The gate core arity `m(q) = K_amp·q₀(q)`, `q₀(q) = q + ⌈d_G lg(q+2)⌉ + log₂ P` (paper
eq:gadget-table-arity, and §11.6 "pad the function in either case to exactly m(q) = K_amp q₀(q) inputs"), written with
`ext = log₂ P − 1` so that `ext = 0` is the shared `coreWidth` (one occurrence bit). -/
def coreWidth (copies ext degree q : Nat) := copies*(q+clauseWidth degree q+(ext+1))

/-- Enumerate s=1,...,n; zero denotes the empty finite-search result. -/
def selectedIndex (width : Nat→Nat) (n : Nat) :=
  Nat.findGreatest (fun s=>1 ≤ s ∧ width s≤n/2) n

theorem selectedIndex_le (width : Nat→Nat) (n : Nat) : selectedIndex width n ≤ n :=
  Nat.findGreatest_le _

theorem selectedIndex_fits (width : Nat→Nat) (n : Nat)
    (h : selectedIndex width n≠0) :
    1 ≤ selectedIndex width n ∧ width (selectedIndex width n)≤n/2 :=
  Nat.findGreatest_of_ne_zero rfl h

/-- `m(q(N_s))`: the core arity at the dyadic source length `N_s = 2^s`. -/
def widthAt (sources : GateEightSources) (k : Nat) (_clock : OrdinaryClock (fun n=>n^(k+2)))
    (copies ext clauseDegree s : Nat) :=
  coreWidth copies ext clauseDegree (sources.width.width s)

end
end NearCubicWires.RepairSource.CloseoutLanguage

end GR
