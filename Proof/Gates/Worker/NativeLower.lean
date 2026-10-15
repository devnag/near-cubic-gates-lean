import Proof.Gates.Worker.Meaning

/-!
# The native width dominates every fixed threshold, eventually

`gate_nativeWidth_ge`: once `2^T ≤ N`, the native width `q(N)` (paper v2 §11.4,
`q(N) = ⌈log₂ T_clk(N)⌉ + A_pad⌈log₂(log₂ T_clk(N)+2)⌉ + A_pad`) is at least `T`, since `⌈log₂ N^{k+2}⌉ ≥ T`. Used for the
cutoffs `2 ≤ q` of the Case 2 producer and the worker.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicGates.Close.Transfer

theorem gate_nativeWidth_ge (s : GateSources) (g : GateParams) (T N : ℕ) (hN : 2 ^ T ≤ N) : T ≤ width s g N :=
  Outer.le_widthOf g.k _ T N hN

/-- The cutoff form: past `4`, the native width is at least `2`. -/
theorem two_le_nativeWidth (s : GateSources) (g : GateParams) (N : ℕ) (hN : 4 ≤ N) : 2 ≤ width s g N :=
  gate_nativeWidth_ge s g 2 N (by simpa using hN)

end NearCubicGates.Close.Worker
