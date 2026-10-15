import Proof.Gates.CheckedPCPP.WMXReady

set_option autoImplicit false

namespace NearCubicGates.Close.Interfaces

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP

variable {ns nr : ℕ}

/-- The cold start of a word function on a WMX layout: `frame word` on stream 0, all else empty or zero. -/
def startState (ns nr : ℕ) (word : List Bool) : WState ns nr :=
  ⟨fun _ => 0, fun i => if i.val = 0 then frame word else [], fun _ => 0, false⟩

/-- The program of a WMX program with output stream `OUT ≠ 0`. -/
noncomputable def wmxProgram (P : WMX ns nr) (OUT : Fin (ns + 1)) (hOUT : OUT.val ≠ 0) : Program where
  tapeCount := ns + 2 + nr
  stateCount := P.size
  twoTapes := by omega
  machine := P.compile
  outputTape := sTape OUT
  outputFresh := by simp [sTape, hOUT]

theorem coldBank_startState (word : List Bool) :
    coldBank (startState ns nr word) = fun j => if j.val = 0 then frame word else [] := by
  funext j
  rcases PrimAsm.DockW.tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
  · rw [coldBank_s]
    show (if i.val = 0 then frame word else []) = if (sTape (nr := nr) i).val = 0 then frame word else []
    by_cases hi : i.val = 0
    · have h0 : (sTape (nr := nr) i).val = 0 := by simp [sTape, hi]
      rw [if_pos hi, if_pos h0]
    · have h0 : (sTape (nr := nr) i).val ≠ 0 := by simp [sTape, hi]
      rw [if_neg hi, if_neg h0]
  · rw [coldBank_c]; simp [cTape]
  · rw [coldBank_r]
    have h0 : (rTape (ns := ns) q).val ≠ 0 := by simp [rTape]
    rw [if_neg h0]

/-- **The packaging lemma.** A WMX program meeting its word-level spec from the cold start is a `WordFunction`. -/
noncomputable def wordFunction_of_wmx {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (P : WMX ns nr) (OUT : Fin (ns + 1)) (hOUT : OUT.val ≠ 0) (cap : Request → ℕ)
    (h : ∀ r, ∃ τ : WState ns nr, WXExec (cap r) P (startState ns nr (input r)) τ (budget r) ∧
      τ.st OUT = output r ∧ (∀ i, τ.sh i = 0) ∧ ∀ q, τ.val q = 0) :
    WordFunction Request input output budget where
  program := wmxProgram P OUT hOUT
  realizes := by
    intro r
    obtain ⟨τ, hrun, hout, hsh, hval⟩ := h r
    obtain ⟨out, ⟨rc, hrc, htapes, _, _⟩, hst⟩ :=
      WXExec.ready hrun (fun _ => rfl) (fun _ => rfl) rfl hsh hval
    refine ⟨rc, ?_, ?_⟩
    · have hin : (wmxProgram P OUT hOUT).inputTapes (input r) = coldBank (startState ns nr (input r)) := by
        rw [coldBank_startState]; rfl
      rw [hin]; exact hrc
    · show rc.final.tapes (sTape OUT) = output r
      rw [htapes, hst, hout]

end NearCubicGates.Close.Interfaces
