import SourceAdapters.Routing.TermsMachinePrefixStart

/-! The construction in `lem:generator`: emit the counted list header and rewind the packed item cursor. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicWires Joins ShortPCP.Machines.FL CoordinateMachine

def passSwitch : S :=
  .seq (.set 32 (.v 24)) (.seq (natOut 32)
    (.seq (.set 31 (.k 1)) (.set 14 (.v 27))))

def passSwitchWrites : List Var := [5, 6, 14, 31, 32]

theorem passSwitch_spec_generic (G : Glob) (s : FS)
    (hbits : natBitLength (s.env 24) + 2 ≤ G.K) (hN : G.K ≤ G.N) :
    Appends passSwitchWrites s (evalS G passSwitch s) (RepairRepresentation.natWord (s.env 24)) ∧
      (evalS G passSwitch s).env 32 = s.env 24 ∧
      (evalS G passSwitch s).env 31 = 1 ∧
      (evalS G passSwitch s).env 14 = s.env 27 := by
  let a := s.setv 32 (s.env 24)
  have hout := natOut_spec G a 32 (by decide) (by decide) (by simpa [a] using hbits) hN
  generalize eb : evalS G (natOut 32) a = b at hout
  have hb32 : b.env 32 = s.env 24 := by simpa [a] using hout.env 32 (by decide)
  have hb27 : b.env 27 = s.env 27 := by simpa [a] using hout.env 27 (by decide)
  let c := (b.setv 31 1).setv 14 (s.env 27)
  have h1 : 1 ≤ G.cap := by have := cap_ge G; omega
  have he : evalS G passSwitch s = c := by
    simp only [passSwitch, evalS_seq, evalS_set, evalE, min_eq_left h1]
    change ((evalS G (natOut 32) a).setv 31 1).setv 14
      (((evalS G (natOut 32) a).setv 31 1).env 27) = c
    rw [eb]
    simp [c, hb27]
  have ha : Appends passSwitchWrites s a [] := Appends.setv _ _ 32 (by simp [passSwitchWrites]) _
  have hb : Appends passSwitchWrites a b (RepairRepresentation.natWord (s.env 24)) := by
    simpa [a] using hout.mono (by simp [passSwitchWrites])
  have hc : Appends passSwitchWrites b c [] := by
    simpa [c] using (Appends.setv passSwitchWrites b 31 (by simp [passSwitchWrites]) 1).trans
      (Appends.setv passSwitchWrites (b.setv 31 1) 14 (by simp [passSwitchWrites]) (s.env 27))
  rw [he]
  exact ⟨by simpa using (ha.trans hb).trans hc,
    by simpa [c] using hb32, by simp [c], by simp [c]⟩

theorem passSwitch_spec (p : TermsReq) (h : TermsOk p) (s : FS)
    (h24 : s.env 24 = (termsCircuit p h).length) :
    let G := globOf (preparedInput (termsInput p h))
    Appends passSwitchWrites s (evalS G passSwitch s)
      (RepairRepresentation.natWord (termsCircuit p h).length) ∧
      (evalS G passSwitch s).env 32 = (termsCircuit p h).length ∧
      (evalS G passSwitch s).env 31 = 1 ∧
      (evalS G passSwitch s).env 14 = s.env 27 := by
  have hn := Bounds.prepared_numeric_bounds p h
  have hc := (Bounds.request_arithmetic p h).2.2.2.2.2.2.1
  have hb : natBitLength (s.env 24) + 2 ≤ (globOf (preparedInput (termsInput p h))).K := by
    apply hn.2.1
    rw [h24]
    exact (by omega : (termsCircuit p h).length ≤ Bounds.arithmeticBound (termsInput p h).length).trans
      (Nat.le_max_left _ _)
  simpa only [h24] using passSwitch_spec_generic _ s hb hn.2.2.2

theorem passSwitch_wf (d : ℕ) (hd : d < 8) : wfS passSwitch d = true := by
  simp [passSwitch, wfS, dE, natOut_wf 32 d hd]

end NearCubicGates.Adapters.Routing.TermsMachine
