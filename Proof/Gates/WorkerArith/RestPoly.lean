import Proof.Gates.WorkerArith.PolyE
import Proof.Gates.WorkerArith.LoopFitOf

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith.WorkerBounds

open NearCubicGates.Close.WorkerArith

section Defs
variable (Fs M qf : ℕ → ℕ) (Cω tc Kc ec Co eo Cv ev : ℕ)

/-- The size bound of an accepting run. -/
def SSf (N : ℕ) : ℕ := 2 * Fs N + Cω

/-- The loop's polynomial cost bound. -/
def Lpf (N : ℕ) : ℕ :=
  M N * (1000000000000000 * (tc + 1) * (Zof (SSf Fs Cω N) + 3 * SSf Fs Cω N + 1) ^ 4 * (Bcof (SSf Fs Cω N) + 1) + 4) +
    9 + (300 * tc + 6000) * (10 * M N * (Kc * (10 * Zof (SSf Fs Cω N) + 41) ^ ec))

/-- The verdict request's length bound. -/
def VWf (N : ℕ) : ℕ := 6 * SSf Fs Cω N + 2 * N + 24 * M N + 18 + 10 * M N * (Co * (qf N + 1) ^ eo + 43)

/-- The polynomial part of the fuel. -/
def Fpf (N : ℕ) : ℕ :=
  Fs N + Lpf Fs M Cω tc Kc ec N + 2 * (Cv * (VWf Fs M qf Cω Co eo N + 1) ^ ev) + 12 * VWf Fs M qf Cω Co eo N + 152

end Defs

theorem exp_le (EF ec ev : ℕ) :
    EF ≤ 30 * EF * (ec + ev + 1) + 2 * ev + 10 ∧
    1 + (EF * 3 * 4 + EF * 3 * 3) ≤ 30 * EF * (ec + ev + 1) + 2 * ev + 10 ∧
    1 + EF * 3 * ec ≤ 30 * EF * (ec + ev + 1) + 2 * ev + 10 ∧
    (EF + 2) * ev ≤ 30 * EF * (ec + ev + 1) + 2 * ev + 10 ∧
    EF + 2 ≤ 30 * EF * (ec + ev + 1) + 2 * ev + 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **The polynomial part of the fuel is eventually `≤ C (N+1)^a`, `a = 30 EF (e_c + e_v + 1) + 2 e_v + 10`.** -/
theorem fp_pe (Fs M qf : ℕ → ℕ) (Cω tc Kc ec Co eo Cv ev EF : ℕ) (hFs : PE Fs EF) (hM : PE M 1)
    (hq : PE (fun N => (qf N + 1) ^ eo) 1) :
    PE (Fpf Fs M qf Cω tc Kc ec Co eo Cv ev) (30 * EF * (ec + ev + 1) + 2 * ev + 10) := by
  obtain ⟨x1, x2, x3, x4, x5⟩ := exp_le EF ec ev
  set a := 30 * EF * (ec + ev + 1) + 2 * ev + 10
  have hSS : PE (SSf Fs Cω) EF := (hFs.cmul 2).add_const Cω
  have hS1 : PE (fun N => SSf Fs Cω N + 1) EF := hSS.add_const 1
  have hS2 : PE (fun N => SSf Fs Cω N + 2) EF := hSS.add_const 2
  have hZ : PE (fun N => Zof (SSf Fs Cω N)) (EF * 3) := by
    unfold Zof
    have h1 := (hS1.pow 3).cmul 40
    have h2 := ((hS2.pow 2).cmul 10).raise (show EF * 2 ≤ EF * 3 by omega)
    have h3 := ((hSS.cmul 4).add_const 4).raise (show EF ≤ EF * 3 by omega)
    exact (h1.add h2).add h3 |>.mono (fun N => by omega)
  have hW : PE (fun N => Wof (SSf Fs Cω N)) (EF * 3) := by
    unfold Wof
    exact (hZ.add ((hSS.add_const 2).raise (by omega))).mono (fun N => by omega)
  have hBc : PE (fun N => Bcof (SSf Fs Cω N) + 1) (EF * 3 * 3) := by
    unfold Bcof
    exact ((hW.pow 3).cmul 100000).add_const 1
  have hZS : PE (fun N => Zof (SSf Fs Cω N) + 3 * SSf Fs Cω N + 1) (EF * 3) :=
    ((hZ.add ((hSS.cmul 3).raise (by omega))).add_const 1).mono (fun N => by omega)
  have hL1 : PE (fun N => M N * (1000000000000000 * (tc + 1) * (Zof (SSf Fs Cω N) + 3 * SSf Fs Cω N + 1) ^ 4 *
      (Bcof (SSf Fs Cω N) + 1) + 4)) (1 + (EF * 3 * 4 + EF * 3 * 3)) := by
    have h := ((hZS.pow 4).mul hBc).cmul (1000000000000000 * (tc + 1))
    exact hM.mul (h.add_const 4) |>.mono (fun N => by rw [Nat.mul_assoc (1000000000000000 * (tc + 1))])
  have hL2 : PE (fun N => (300 * tc + 6000) * (10 * M N * (Kc * (10 * Zof (SSf Fs Cω N) + 41) ^ ec))) (1 + EF * 3 * ec) := by
    have h := ((hZ.cmul 10).add_const 41).pow ec
    have h2 := (hM.cmul 10).mul (h.cmul Kc)
    exact h2.cmul (300 * tc + 6000)
  have hLp : PE (Lpf Fs M Cω tc Kc ec) a := by
    unfold Lpf
    exact ((hL1.raise x2).add_const 9).add (hL2.raise x3)
  have hV : PE (VWf Fs M qf Cω Co eo) (EF + 2) := by
    unfold VWf
    have h1 := (hSS.cmul 6).raise (show EF ≤ EF + 2 by omega)
    have h2 : PE (fun N => 2 * N) (EF + 2) :=
      PE.mono ((PE.lin.cmul 2).raise (show 1 ≤ EF + 2 by omega)) (fun N => by omega)
    have h3 := (hM.cmul 24).raise (show 1 ≤ EF + 2 by omega)
    have h4 := ((hM.cmul 10).mul ((hq.cmul Co).add_const 43)).raise (show 1 + 1 ≤ EF + 2 by omega)
    exact (((h1.add h2).add h3).add_const 18).add h4 |>.mono (fun N => by
      show 6 * SSf Fs Cω N + 2 * N + 24 * M N + 18 + 10 * M N * (Co * (qf N + 1) ^ eo + 43) ≤ _
      rw [Nat.mul_assoc 10 (M N)])
  have hVv : PE (fun N => 2 * (Cv * (VWf Fs M qf Cω Co eo N + 1) ^ ev)) a :=
    ((((hV.add_const 1).pow ev).cmul Cv).cmul 2).raise x4
  unfold Fpf
  exact ((((hFs.raise x1).add hLp).add hVv).add ((hV.cmul 12).raise x5)).add_const 152

end NearCubicGates.Close.WorkerArith.WorkerBounds
