import Proof.Gates.Worker.Dock
import Proof.Gates.CheckedPCPP.Harness
import Proof.Gates.OuterM.Spec
import Proof.CaseAnalysis.WitnessOracleRun

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

/-! ## Word functions as frame donors -/

/-- The input tape of a program (tape `0`). -/
def inTape (p : Program) : Fin p.tapeCount := ⟨0, by have := p.twoTapes; omega⟩

theorem inputTapes_eq (p : Program) (w : List Bool) :
    p.inputTapes w = fun j => if j = inTape p then frame w else [] := by
  funext j
  unfold Program.inputTapes inTape
  by_cases hj : j.val = 0
  · rw [if_pos hj, if_pos (Fin.ext hj)]
  · rw [if_neg hj, if_neg (fun h => hj (by rw [h]))]

theorem outputTape_ne_inTape (p : Program) : p.outputTape ≠ inTape p := by
  intro h
  exact p.outputFresh (by rw [h]; rfl)

theorem wf_ready {Req : Type} {inp outp : Req → List Bool} {bud : Req → ℕ} (f : WordFunction Req inp outp bud)
    (r : Req) :
    ∃ out, ClockJoin.ReadyRun (Rewind.program f.program).machine (2 * bud r + 2)
        (fun j => if j = inTape (Rewind.program f.program) then frame (inp r) else []) out ∧
      out (Rewind.program f.program).outputTape = outp r := by
  obtain ⟨out, h1, h2⟩ := CheckedPCPP.wordFunction_ready f r
  rw [inputTapes_eq] at h1
  exact ⟨out, h1, h2⟩

section Width
variable {mw : Outer.MWSource} {k : ℕ} {H : RepairSource.OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  {SV : Outer.SuccinctVerifier H G}

noncomputable abbrev wdB (W : OuterM.WidthDonor mw SV) : Program := Rewind.program W.word.program

noncomputable abbrev wdU (W : OuterM.WidthDonor mw SV) : Program := Rewind.program W.unary.program

/-- `frame q.bits` from `frame x`, `q = qOf N` (paper v2 §11.4, "the exact native width"), within `2K(N+1) + 2`. -/
theorem widthB_ready (W : OuterM.WidthDonor mw SV) {N : ℕ} (x : BitInput N) :
    ∃ out, ClockJoin.ReadyRun (wdB W).machine (2 * (W.K * (N + 1) ^ 1) + 2)
        (fun j => if j = inTape (wdB W) then frame (List.ofFn x) else []) out ∧
      out (wdB W).outputTape = frame (OuterM.qOf mw SV N).bits :=
  wf_ready W.word ⟨N, x⟩

/-- `1^q` from `frame x`, `q = qOf N`, within `2K(N+1) + 2`. -/
theorem widthU_ready (W : OuterM.WidthDonor mw SV) {N : ℕ} (x : BitInput N) :
    ∃ out, ClockJoin.ReadyRun (wdU W).machine (2 * (W.K * (N + 1) ^ 1) + 2)
        (fun j => if j = inTape (wdU W) then frame (List.ofFn x) else []) out ∧
      out (wdU W).outputTape = List.replicate (OuterM.qOf mw SV N) true :=
  wf_ready W.unary ⟨N, x⟩

end Width

section Cold
open RepairOrdinary.CloseoutWitness.Oracle RepairOrdinary.RadixSemantics ExecutableInterfaces CanonicalWitnessCodec

/-- The oracle decoder's input bank: `frame x`, `frame bits`, `frame arityBits`, `1^{value arityBits}`, blanks. -/
def coldIn (x bits ab : List Bool) : Fin (tapes + 1) → List Bool := fun j =>
  if j.val = 0 then frame x else if j.val = 1 then frame bits else if j.val = 2 then frame ab
  else if j.val = 3 then List.replicate (value ab) true else []

theorem coldInput_eq (x bits ab : List Bool) : coldInput x bits ab = coldIn x bits ab := by
  funext j
  refine Fin.addCases (m := tapes) (n := 1) (fun i => ?_) (fun i => ?_) j
  · simp only [coldInput, Fin.addCases_left, coldIn, Fin.val_castAdd]
    rfl
  · simp only [coldInput, Fin.addCases_right, coldIn, Fin.val_natAdd]
    have : tapes + i.val ≠ 0 ∧ tapes + i.val ≠ 1 ∧ tapes + i.val ≠ 2 ∧ tapes + i.val ≠ 3 := by
      unfold tapes; omega
    simp

theorem cold_ready (x bits ab : List Bool) (hN : 2 ≤ x.length) (hcap : 16 * bits.length ≤ x.length)
    (hb : ab.length ≤ x.length + 1) :
    ∃ out, ClockJoin.ReadyRun machine (budget x bits ab) (coldIn x bits ab) out ∧
      out flagSlot = [(decodeBooleanCircuit (value ab) (value bits)).isSome] ∧
      (∀ c : BooleanCircuit (value ab), decodeBooleanCircuit (value ab) (value bits) = some c →
        out descriptorSlot = PCPPNative.descriptor c) := by
  obtain ⟨out, hr, hf, hd⟩ := cold_run x bits ab hN hcap hb
  exact ⟨out, by rw [← coldInput_eq]; exact hr, hf, hd⟩

end Cold

end NearCubicGates.Close.Worker
