import SourceAdapters.Routing.TermsMachineBoundsRequest

/-! # Reading and initializing an actual prepared terms request -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicWires NearCubicWires.CanonicalBinary NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Routing.CoordinateMachine
open NearCubicGates.Close.Cells (leadOnes)

/-- Retain the raw frame and calculate the entry width from its physical length. -/
def saveFrame : S :=
  .seq (.set 10 (.v 0)) (.seq (.set 11 (.v 1))
    (.seq (.set 12 (.mul (.k 16) (.add (.v 11) (.k 1)))) (.set 14 (.k 0))))

def initializeProgram : S := .seq rdFrame (.seq saveFrame parseInput)

def initializeWrites : List Var := rdFrameW ++ [10, 11, 12, 14] ++ inputWrites

theorem prepared_end (word : List Bool) :
    (s0 (preparedInput word)).ip + 2 * word.length + 1 = (preparedInput word).length := by
  change leadOnes (preparedInput word) + 1 + 2 * word.length + 1 = _
  rw [prepared_lead]
  simp only [preparedInput, ShortPCP.Time.prefixWord, List.length_append,
    List.length_replicate, List.length_cons, frame_length]
  omega

/-- The complete frontend, at its actual prepared input and allocated capacities. -/
theorem initialize_spec (p : TermsReq) (h : TermsOk p) :
    let word := termsInput p h
    let inp := preparedInput word
    let t := evalS (globOf inp) initializeProgram (s0 inp)
    let width := Bounds.wordWidth word.length
    let pos := (RepairRepresentation.natWord p.f).length + (RepairRepresentation.natWord p.l.m).length +
      (termsCoordWord p h).length + (listWord RepairRepresentation.natWord (globalBank p.l)).length
    t.env 10 = bitsValue word ∧ t.env 11 = word.length ∧ t.env 12 = width ∧
      t.env 20 = p.f ∧ t.env 21 = p.l.m ∧ t.env 22 = bitsValue (termsCoordWord p h) ∧
      t.env 23 = packW width (globalBank p.l) ∧ t.env 26 = (globalBank p.l).length ∧
      t.env 27 = pos ∧ t.env 14 = pos ∧ t.env 30 = width ∧
      Wr initializeWrites (s0 inp) t ∧ t.out = [] ∧ t.bad = false ∧ t.ip = inp.length := by
  let word := termsInput p h
  let inp := preparedInput word
  let G := globOf inp
  let start := s0 inp
  let width := Bounds.wordWidth word.length
  have hB : BdOk G word.length := prepared_BdOk word
  have htail : G.inp.drop start.ip = frame word ++ [] := by
    simpa only [List.append_nil] using prepared_tail word
  obtain ⟨a0, a1, aip, aW⟩ := rdFrame_spec G start word [] htail
    (by have hh := hB.1; omega) hB.2
  generalize ea : evalS G rdFrame start = a at a0 a1 aip aW
  have hwidth : width ≤ G.cap := by
    have hk : width + 2 ≤ G.K := Bounds.prepared_width word
    have hc := cap_ge G
    omega
  have h16 : 16 ≤ G.cap := by dsimp [width, Bounds.wordWidth] at hwidth; omega
  have hlen : word.length + 1 ≤ G.cap := by dsimp [width, Bounds.wordWidth] at hwidth; omega
  have h1 : 1 ≤ G.cap := by omega
  let b := (((a.setv 10 (bitsValue word)).setv 11 word.length).setv 12 width).setv 14 0
  have eb : evalS G saveFrame a = b := by
    simp [saveFrame, evalE, a0, a1, min_eq_left h16, min_eq_left h1,
      min_eq_left hlen, show 16 * (word.length + 1) = width from rfl, min_eq_left hwidth, b]
  have bW : Wr [10, 11, 12, 14] a b :=
    (((Wr.setv a (by simp) _).trans (Wr.setv _ (by simp) _)).trans
      (Wr.setv _ (by simp) _)).trans (Wr.setv _ (by simp) _)
  have hp := Bounds.prepared_parser_bounds p h
  obtain ⟨c20, c21, c22, c23, c26, c27, c14, c30, cW, cip⟩ := parseInput_spec G b p.f p.l.m
    (termsCoordWord p h) (globalBank p.l)
    (p.items.flatMap (itemWord (termsMask p h)) ++ RepairRepresentation.natWord 0) width
    (by simp only [b, FS.setv_env, Function.update_of_ne (show (10 : Var) ≠ 14 by decide),
        Function.update_of_ne (show (10 : Var) ≠ 12 by decide),
        Function.update_of_ne (show (10 : Var) ≠ 11 by decide), Function.update_self]
        exact congrArg bitsValue (Bounds.input_eq_headerInput p h))
    (by simp [b]) (by simp [b]) (Bounds.coord_length p h)
    (by simpa only [← Bounds.input_eq_headerInput p h] using hp.1)
    hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  generalize ec : evalS G parseInput b = c at c20 c21 c22 c23 c26 c27 c14 c30 cW cip
  have he : evalS G initializeProgram start = c := by simp only [initializeProgram, evalS_seq, ea, eb, ec]
  have hw : Wr initializeWrites start c :=
    ((aW.mono (by decide)).trans (bW.mono (by decide))).trans (cW.mono (by decide))
  have hc10 : c.env 10 = bitsValue word := (cW.env 10 (by decide)).trans (by simp [b])
  have hc11 : c.env 11 = word.length := (cW.env 11 (by decide)).trans (by simp [b])
  have hc12 : c.env 12 = width := (cW.env 12 (by decide)).trans (by simp [b])
  have hcip : c.ip = inp.length := by
    calc c.ip = b.ip := cip
      _ = a.ip := rfl
      _ = start.ip + 2 * word.length + 1 := aip
      _ = inp.length := prepared_end word
  change (evalS G initializeProgram start).env 10 = _ ∧ _
  rw [he]
  exact ⟨hc10, hc11, hc12, c20, c21, c22, c23, c26, c27, c14, c30, hw,
    hw.out.trans rfl, hw.bad.trans rfl, hcip⟩

theorem initialize_wf (d : ℕ) (hd : d ≤ 6) : wfS initializeProgram d = true := by
  simp [initializeProgram, saveFrame, rdFrame, wfS, dE, parseInput_wf d hd]
  omega

end NearCubicGates.Adapters.Routing.TermsMachine
