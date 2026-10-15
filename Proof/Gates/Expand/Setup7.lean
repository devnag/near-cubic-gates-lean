import Proof.Gates.Expand.Setup6

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

/-- The number block state during the constants: registers as in `σ` except the counter `GR 3`. -/
structure CB (Wb : ℕ) (σ τ : WState NS NR) (w : Fin 53 → ℕ) : Prop where
  mv : MV NB Wb w τ
  regs : ∀ q, q ≠ GR 3 → τ.val q = σ.val q
  strs : ∀ x, x ∉ nbList → τ.st x = σ.st x ∧ τ.sh x = σ.sh x
  cell : τ.cell = σ.cell

theorem CB.step {Wb : ℕ} {σ τ τ' : WState NS NR} {w w' : Fin 53 → ℕ} {S : List (Fin (NS + 1))} (h : CB Wb σ τ w)
    (m : MV NB Wb w' τ') (f : SameExcept τ τ' S []) (hS : ∀ x ∈ S, x ∈ nbList) : CB Wb σ τ' w' :=
  ⟨m, fun q hq => by rw [f.val (by simp), h.regs q hq], fun x hx => by
    have hxS : x ∉ S := fun h' => hx (hS x h')
    rw [f.st hxS, f.sh hxS]; exact h.strs x hx, by rw [f.cell, h.cell]⟩

theorem CB.reg {Wb : ℕ} {σ τ τ' : WState NS NR} {w : Fin 53 → ℕ} (h : CB Wb σ τ w) (f : SameExcept τ τ' [] [GR 3]) :
    CB Wb σ τ' w :=
  ⟨h.mv.frame' f (by simp), fun q hq => by rw [f.val (by simp [hq]), h.regs q hq], fun x hx => by
    rw [f.st (by simp), f.sh (by simp)]; exact h.strs x hx, by rw [f.cell, h.cell]⟩

theorem nbS (j : Fin 53) : ∀ x ∈ [NB j], x ∈ nbList := by simp [mem_nbList]
theorem nbS2 (j k : Fin 53) : ∀ x ∈ [NB j, NB k], x ∈ nbList := by simp [mem_nbList]

def constB1 : WMX NS NR :=
  .seq (BinW.inc (NB 35) (NB 0) F0 R0)
    (.seq (clrR (GR 3))
    (.seq (addR (RF 10) (GR 3) (GR 7))
    (.seq (BinW.copy (NB 37) (NB 35) F0 R0)
    (.seq (shlLoop 37 35 (GR 3) (GR 5))
    (.seq (clrR (GR 3))
    (.seq (addR (GR 1) (GR 3) (GR 7))
    (.seq (BinW.copy (NB 34) (NB 35) F0 R0)
    (.seq (shlLoop 34 35 (GR 3) (GR 5))
    (clrR (GR 3))))))))))

def constB2 : WMX NS NR :=
  .seq (BinW.mul (NB 37) (NB 34) (NB 32) (NB 21) F0 R0 (GR 5))
    (.seq (BinW.copy (NB 36) (NB 37) F0 R0)
    (.seq (BinW.sub (NB 36) (NB 35) F0 R0)
    (.seq (BinW.copy (NB 33) (NB 34) F0 R0)
    (.seq (BinW.sub (NB 33) (NB 35) F0 R0)
    (.seq (BinW.mul (NB 36) (NB 34) (NB 31) (NB 21) F0 R0 (GR 5))
    (.seq (BinW.copy (NB 51) (NB 34) F0 R0)
    (BinW.half (NB 51) R0)))))))

def constB3 : WMX NS NR :=
  .seq (BinW.copy (NB 7) (NB 35) F0 R0)
    (.seq (BinW.copy (NB 5) (NB 34) F0 R0)
    (.seq (BinW.copy (NB 6) (NB 33) F0 R0)
    (.seq (BinW.copy (NB 13) (NB 35) F0 R0)
    (.seq (BinW.copy (NB 14) (NB 37) F0 R0)
    (.seq (BinW.copy (NB 16) (NB 36) F0 R0)
    (.seq (BinW.copy (NB 48) (NB 32) F0 R0)
    (.seq (BinW.copy (NB 49) (NB 34) F0 R0)
    (BinW.copy (NB 50) (NB 35) F0 R0))))))))

def constB : WMX NS NR := .seq constB1 (.seq constB2 constB3)

def constB1Cost (Wb V W D : ℕ) : ℕ :=
  (41 * Wb + 7) + 1 + (((D + 1) * (1 + 2) + 1) + 1 + ((18 * V + 3) + 1 + ((41 * Wb + 3) + 1 + ((shlCost Wb V) + 1 + ((V * (1 + 2) + 1) + 1 + ((18 * W + 3) + 1 + ((41 * Wb + 3) + 1 + ((shlCost Wb W) + 1 + (W * (1 + 2) + 1)))))))))

def constB2Cost (Wb : ℕ) : ℕ :=
  (mulCost Wb) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 9) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 9) + 1 + ((mulCost Wb) + 1 + ((41 * Wb + 3) + 1 + (34 * Wb + 3)))))))

def constB3Cost (Wb : ℕ) : ℕ :=
  (41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + (41 * Wb + 3))))))))

def constBCost (Wb V W D : ℕ) : ℕ := constB1Cost Wb V W D + 1 + (constB2Cost Wb + 1 + constB3Cost Wb)

end NearCubicGates.Close.Expand.Layout
