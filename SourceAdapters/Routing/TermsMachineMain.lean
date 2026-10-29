import SourceAdapters.Routing.TermsMachinePass
import SourceAdapters.Routing.TermsMachineInitialize

/-! # Two-pass printing of the exact serialized terms circuit -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Main

open NearCubicWires NearCubicWires.RepairRepresentation
open Joins ShortPCP.Machines.FL CoordinateMachine

/-- Count the circuit, emit its count, then emit the same ordered gates. -/
def program : S := .seq initializeProgram (.seq (.set 31 (.k 0))
  (.seq pass (.seq passSwitch pass)))

/-- Initialization supplies precisely the retained data of both passes. -/
theorem initialized (p : TermsReq) (h : TermsOk p) :
    let inp := preparedInput (termsInput p h)
    let a := evalS (globOf inp) initializeProgram (s0 inp)
    Parameters p h a ∧ a.env 14 = Items.firstItem p h ∧ a.out = [] ∧ a.bad = false := by
  obtain ⟨h10, _, _, h20, h21, h22, h23, h26, h27, h14, h30, _, hout, hbad, _⟩ :=
    initialize_spec p h
  exact ⟨⟨h10, h20, h21, h22, h23, h26, h27, h30⟩, h14, hout, hbad⟩

/-- The actual prepared request is printed with its exact list header and gate words. -/
theorem main_spec (p : TermsReq) (h : TermsOk p) :
    let inp := preparedInput (termsInput p h)
    let t := evalS (globOf inp) program (s0 inp)
    t.out = termsOutput p h ∧ t.bad = false := by
  let inp := preparedInput (termsInput p h)
  let G := globOf inp
  let start := s0 inp
  obtain ⟨ap, a14, aout, abad⟩ := initialized p h
  generalize ea : evalS (globOf (preparedInput (termsInput p h))) initializeProgram
    (s0 (preparedInput (termsInput p h))) = a at ap a14 aout abad
  let b := a.setv 31 0
  have bA : Appends [31] a b [] := Appends.setv [31] a 31 (by decide) 0
  have bp : Parameters p h b := ap.transfer bA (by decide)
  have b14 : b.env 14 = Items.firstItem p h := (bA.env 14 (by decide)).trans a14
  have b31 : b.env 31 = 0 := by simp [b]
  have bout : b.out = [] := aout
  obtain ⟨cA, cp, _, c24⟩ := pass_spec p h b bp b14
  generalize ec : evalS (globOf (preparedInput (termsInput p h))) pass b = c at cA cp c24
  have cout : c.out = [] := by simpa [Prefix.words, b31, bout] using cA.out
  obtain ⟨dA, _, d31, d14⟩ := passSwitch_spec p h c c24
  generalize ed : evalS (globOf (preparedInput (termsInput p h))) passSwitch c = d at dA d31 d14
  have dp : Parameters p h d := cp.transfer dA (by decide)
  have d14' : d.env 14 = Items.firstItem p h := d14.trans cp.firstItem
  obtain ⟨eA, _, _, _⟩ := pass_spec p h d dp d14'
  generalize ee : evalS (globOf (preparedInput (termsInput p h))) pass d = e at eA
  have eout : e.out = termsOutput p h := by
    rw [eA.out, dA.out, cout, d31]
    simp only [List.nil_append, Prefix.words, one_ne_zero, if_false,
      termsOutput, listWord, List.flatMap_def]
  have ebad : e.bad = false := eA.bad.trans (dA.bad.trans (cA.bad.trans abad))
  have he : evalS G program start = e := by
    have ea' : evalS G initializeProgram start = a := ea
    simp only [program, evalS_seq, ea', evalS_set, evalE, Nat.zero_min]
    change evalS G pass (evalS G passSwitch (evalS G pass b)) = e
    rw [ec, ed, ee]
  change (evalS G program start).out = _ ∧ _
  rw [he]
  exact ⟨eout, ebad⟩

theorem wellFormed (d : ℕ) (hd : d ≤ 5) : wfS program d = true := by
  simp [program, wfS, dE, initialize_wf d (by omega), pass_wf d hd,
    passSwitch_wf d (by omega)]

theorem program_wf : wfS program 0 = true := wellFormed 0 (by decide)

end NearCubicGates.Adapters.Routing.TermsMachine.Main
