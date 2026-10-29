import SourceAdapters.Code.TriplePreparationRead
import SourceAdapters.Proximity.PrefixCompilation

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": uniform triple serialization with a computed
total-length rawPrefix and an explicit polynomial budget in the actual input. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.TriplePreparation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Adapters.Proximity
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee)

abbrev Request := List Bool × List Bool × List Bool

def input (r : Request) : List Bool := inputWord r.1 r.2.1 r.2.2

def output (r : Request) : List Bool := natWord r.1.length ++ r.1 ++ frame r.2.2 ++ r.2.1

noncomputable def context (r : Request) : Ctx :=
  ctxOf noCallee ⟨16, 1, 0, 0, 0, 0⟩ (LengthPrefix.wrapped (input r))

theorem width (r : Request) : 16 * ((input r).length + 1) ≤ (context r).Wd := by
  have hp := LengthPrefix.allocation_covers_length (input r)
  simp only [context, ctxOf, Sz.W, Nat.one_mul]
  omega

def compiler : St VV MM := .seq readScript printScript

theorem compiler_runs (r : Request) :
    ∃ b n, Ex (context r) compiler (a0 : DS VV MM) b n ∧ b.out = output r ∧
      n ≤ 20000 * ((input r).length + 1) ^ 2 := by
  let C := context r
  let L := (input r).length
  have hw := width r
  change 16 * (L + 1) ≤ C.Wd at hw
  have hL : L = 2 * r.1.length + 2 * r.2.1.length + 2 + r.2.2.length := by
    simp only [L, input, inputWord, List.length_append, frame_length]
    omega
  obtain ⟨b, nb, eb, hb, loaded⟩ := read_runs C r.1 r.2.1 r.2.2 rfl hw
  have hbits := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le r.1.length
  have hsmall : L + 3 < 2 ^ C.Wd := lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  obtain ⟨d, nd, ed, hd, dout⟩ := print_runs C b loaded.constants r.1 r.2.1 r.2.2
    (rawPrefix r.1 r.2.1 r.2.2) []
    (by simp [C, context, ctxOf, LengthPrefix.wrapped, input, rawPrefix, inputWord, List.append_assoc])
    loaded.input loaded.xstore loaded.ystore loaded.xsize loaded.ysize loaded.zsize
    (le_of_eq loaded.xcursor) (le_of_eq loaded.ycursor) (by omega) (by omega) (by omega) (by omega)
  refine ⟨d, _, Ex.seq eb ed, ?_, ?_⟩
  · simpa [loaded.output, output] using dout
  · change nb + nd + 1 ≤ 20000 * (L + 1) ^ 2
    change nb ≤ 1000 * (L + 1) at hb
    nlinarith [Nat.zero_le (L ^ 2)]

noncomputable def compilerWordFunction : WordFunction Request
    (fun r => LengthPrefix.wrapped (input r)) output
    (fun r => langBudget noCallee ⟨16, 1, 0, 0, 0, 0⟩ VV MM
      (LengthPrefix.wrapped (input r)) (20000 * ((input r).length + 1) ^ 2)) :=
  wordFunction_of_lang (Req := Request) (V := VV) (M := MM)
    (fun r => LengthPrefix.wrapped (input r)) output noCallee ⟨16, 1, 0, 0, 0, 0⟩ compiler
    (fun r => 20000 * ((input r).length + 1) ^ 2) compiler_runs
    (fun r => by have h := width r; change 1 ≤ (context r).Wd; omega)

noncomputable def coefficient : ℕ := 20005 + 2 * SourcePrinting.nativeCoefficient

/-- Actual uniform serializer. The total length is computed from the physical
input frame, and all subsequent field lengths and copying costs are paid. -/
noncomputable def wordFunction : WordFunction Request input output
    (fun r => coefficient * ((input r).length + 1) ^ 4) := by
  let P : WordFunction Request input (fun r => frame (LengthPrefix.wrapped (input r)))
      (fun r => 10000 * ((input r).length + 1) ^ 2) := {
    program := LengthPrefix.polynomialWordFunction.program
    realizes := fun r => LengthPrefix.polynomialWordFunction.realizes (input r) }
  let Q := compilerWordFunction.enlargeBudget (fun r => PrefixCompilation.budget_bound (input r))
  exact (Code.composeFramed P Q).enlargeBudget (fun r => by
    have hp : ((input r).length + 1) ^ 2 ≤ ((input r).length + 1) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    have h1 : 1 ≤ ((input r).length + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    dsimp [coefficient]
    nlinarith)

end NearCubicGates.Adapters.Code.TriplePreparation
