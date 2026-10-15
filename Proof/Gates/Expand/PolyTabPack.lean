import Proof.Gates.Interfaces.WordFn
import Proof.Gates.CheckedPCPP.WMXSim

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW NearCubicWires.WireExponent3_5.PrimT.ReadEq

variable {ns nr : ℕ}

/-- The ideal start: `frame w` on stream `0`, `lens i` blanks on every other stream `i`. -/
def idealStart (ns nr : ℕ) (w : List Bool) (lens : Fin (ns + 1) → ℕ) : WState ns nr :=
  ⟨fun _ => 0, fun i => if i.val = 0 then frame w else List.replicate (lens i) false, fun _ => 0, false⟩

/-- The rewound compiled program of a WMX program with output stream `OUT ≠ 0`. -/
noncomputable def idealProgram (P : WMX ns nr) (OUT : Fin (ns + 1)) (hOUT : OUT.val ≠ 0) : Program where
  tapeCount := ns + 2 + nr + 1
  stateCount := _
  twoTapes := by omega
  machine := Rewind.machine P.compile
  outputTape := (sTape (nr := nr) OUT).castAdd 1
  outputFresh := by
    show ((sTape (nr := nr) OUT).castAdd 1).val ≠ 0
    rw [Fin.val_castAdd, sTape_val, if_neg hOUT]; omega

theorem ideal_bank (w : List Bool) (lens : Fin (ns + 1) → ℕ) (j : Fin (ns + 2 + nr + 1)) :
    Fin.addCases (motive := fun _ => List Bool) (coldBank (idealStart ns nr w lens)) (fun _ : Fin 1 => []) j =
      (if j.val = 0 then frame w else []) ∨
    ((if j.val = 0 then frame w else []) = ([] : List Bool) ∧ ∃ m, Fin.addCases (motive := fun _ => List Bool)
      (coldBank (idealStart ns nr w lens)) (fun _ : Fin 1 => []) j = List.replicate m false) := by
  refine Fin.addCases (fun j' => ?_) (fun _ => ?_) j
  · rw [Fin.addCases_left, Fin.val_castAdd]
    rcases tape_cases j' with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
    · rw [coldBank_s, sTape_val]
      by_cases hi : i.val = 0
      · left; rw [if_pos hi, if_pos rfl]; show (if i.val = 0 then _ else _) = _; rw [if_pos hi]
      · right
        have h1 : i.val + 1 ≠ 0 := by omega
        refine ⟨by rw [if_neg hi, if_neg h1], lens i, ?_⟩
        show (if i.val = 0 then _ else _) = _; rw [if_neg hi]
    · rw [coldBank_c]; left; rw [cTape_val, if_neg (by omega)]
    · rw [coldBank_r]; left; rw [rTape_val, if_neg (by omega)]
  · rw [Fin.addCases_right]; left
    rw [if_neg (by simp)]

/-- **Packaging from the ideal start.** -/
noncomputable def wordFunction_of_ideal {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (P : WMX ns nr) (OUT : Fin (ns + 1)) (hOUT : OUT.val ≠ 0) (cap : Request → ℕ)
    (lens : Request → Fin (ns + 1) → ℕ) (c : Request → ℕ) (hb : ∀ r, 2 * c r + 2 ≤ budget r)
    (h : ∀ r, lens r OUT = 0 ∧ ∃ τ : WState ns nr, WXExec (cap r) P (idealStart ns nr (input r) (lens r)) τ (c r) ∧
      τ.st OUT = output r) :
    WordFunction Request input output budget where
  program := idealProgram P OUT hOUT
  realizes := by
    intro r
    obtain ⟨hl, τ, hrun, hout⟩ := h r
    obtain ⟨out, ⟨rc, hrc, htapes, _, _⟩, hst⟩ := WXExec.readyRewound hrun (fun _ => rfl) (fun _ => rfl) rfl
    set tin' := Fin.addCases (motive := fun _ => List Bool) (coldBank (idealStart ns nr (input r) (lens r)))
      (fun _ : Fin 1 => []) with htin'
    set tin := (idealProgram P OUT hOUT).inputTapes (input r) with htin
    have hcase : ∀ j, tin' j = tin j ∨ (tin j = [] ∧ ∃ m, tin' j = List.replicate m false) := by
      intro j
      exact ideal_bank (nr := nr) (input r) (lens r) j
    let E : Fin (ns + 2 + nr + 1) → Prop := fun j => tin' j = tin j
    have hrel : ConfRel E (initialConfiguration (Rewind.machine P.compile) tin')
        (initialConfiguration (Rewind.machine P.compile) tin) := by
      refine ⟨rfl, rfl, fun j => ?_, fun j hj => hj⟩
      rcases hcase j with h1 | ⟨h1, m, h2⟩
      · show RdEq (tin' j) (tin j); rw [h1]; exact RdEq.refl _
      · show RdEq (tin' j) (tin j); rw [h1, h2]; exact rdEq_blank _ (by simp)
    obtain ⟨r', hr', hrel', _⟩ := runFrom_rel (Rewind.machine P.compile) E _ hrel rc hrc
    refine ⟨r', ?_, ?_⟩
    · have := run_moreFuel (Rewind.machine P.compile) (2 * c r + 2) (budget r - (2 * c r + 2)) tin r' hr'
      rw [Nat.add_sub_of_le (hb r)] at this
      exact this
    · show r'.final.tapes ((sTape (nr := nr) OUT).castAdd 1) = output r
      have hE : E ((sTape (nr := nr) OUT).castAdd 1) := by
        show tin' _ = tin _
        rw [htin', Fin.addCases_left, coldBank_s]
        show (if OUT.val = 0 then _ else _) = (if ((sTape (nr := nr) OUT).castAdd 1).val = 0 then _ else _)
        rw [if_neg hOUT, Fin.val_castAdd, sTape_val, if_neg hOUT, if_neg (by omega), hl]; rfl
      rw [← hrel'.exact _ hE, htapes, hst, hout]

end NearCubicGates.Close.Expand.PolyTab
