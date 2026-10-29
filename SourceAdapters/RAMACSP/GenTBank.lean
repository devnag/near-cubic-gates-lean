import SourceAdapters.RAMACSP.GenBank

/-!
# Printing the variable bank as a list of numbers

Paper: `lem:generator` (the constraint circuit's input lists the neighbor offsets, whose index `1 + idxOf b` in the
bank is the input index of the read `Y_b`) and the paragraph "Neighbors" of `app:affine-embedding`.

`bankNatP = bankGP emitNatE` prints `listWord natWord (globalBank l)` (`bankNatP_spec`), with the generic bank printer
`bankGP` of `GenBank`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicWires.RepairRepresentation (natWord)

variable {G : Glob}

/-! ## The bank as a list of numbers -/

theorem natPrinter : PrinterSpec G emitNatE natWord := by
  intro s g b hg hb hK hN
  have h := emitNatE_spec (G := G) s g (by rw [hg s ⟨fun _ _ => rfl, rfl, rfl⟩]; exact hb) hN
  rwa [hg s ⟨fun _ _ => rfl, rfl, rfl⟩] at h

/-- **The bank printer**: `listWord natWord (globalBank l)`. -/
def bankNatP : S := bankGP emitNatE

theorem listWord_natWord (L : List ℕ) : listWord natWord L = natWord L.length ++ L.flatMap natWord := by
  simp [listWord, List.flatMap]

theorem bankNatP_spec (l : Routing.Layout) (s : FS) (hl : LV l s) (hK : l.m + 8 ≤ G.K) (hKN : G.K ≤ G.N)
    (hN : 16 * 2 ^ l.q + 2 * l.k ≤ G.N) :
    Em LW s (evalS G bankNatP s) (listWord natWord (Routing.globalBank l)) := by
  rw [listWord_natWord]
  exact bankGP_spec emitNatE natWord natPrinter l s hl hK hKN hN

end NearCubicGates.Adapters.RAMACSP.Gen
