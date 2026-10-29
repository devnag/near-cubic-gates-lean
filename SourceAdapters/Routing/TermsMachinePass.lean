import SourceAdapters.Routing.TermsMachinePassSwitch
import SourceAdapters.Routing.TermsMachineItemsCircuit

/-! The construction in `lem:generator`: one complete count or output pass on the actual terms request. -/
set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicWires.CanonicalBinary Joins ShortPCP.Machines.FL CoordinateMachine

/-- The retained request data used by both passes. -/
structure Parameters (p : TermsReq) (h : TermsOk p) (s : FS) : Prop where
  input : s.env 10 = bitsValue (termsInput p h)
  degree : s.env 20 = p.f
  dimension : s.env 21 = p.l.m
  coordinates : s.env 22 = bitsValue (termsCoordWord p h)
  bank : s.env 23 = packW (Bounds.wordWidth (termsInput p h).length) (globalBank p.l)
  bankLength : s.env 26 = (globalBank p.l).length
  firstItem : s.env 27 = Items.firstItem p h
  width : s.env 30 = Bounds.wordWidth (termsInput p h).length

theorem Parameters.transfer {p : TermsReq} {h : TermsOk p} {s t : FS}
    {W : List Var} {word : List Bool} (hp : Parameters p h s) (ha : Appends W s t word)
    (hw : ∀ i ∈ [10, 20, 21, 22, 23, 26, 27, 30], i ∉ W) : Parameters p h t :=
  ⟨(ha.env 10 (hw 10 (by decide))).trans hp.input,
    (ha.env 20 (hw 20 (by decide))).trans hp.degree,
    (ha.env 21 (hw 21 (by decide))).trans hp.dimension,
    (ha.env 22 (hw 22 (by decide))).trans hp.coordinates,
    (ha.env 23 (hw 23 (by decide))).trans hp.bank,
    (ha.env 26 (hw 26 (by decide))).trans hp.bankLength,
    (ha.env 27 (hw 27 (by decide))).trans hp.firstItem,
    (ha.env 30 (hw 30 (by decide))).trans hp.width⟩

def pass : S := .seq prefixStart Items.itemsPrint

def passWrites : List Var := prefixStartWrites ++ Items.itemWrites

theorem pass_spec (p : TermsReq) (h : TermsOk p) (s : FS)
    (hp : Parameters p h s) (h14 : s.env 14 = Items.firstItem p h) :
    let G := globOf (preparedInput (termsInput p h))
    Appends passWrites s (evalS G pass s) (Prefix.words (s.env 31) (termsCircuit p h)) ∧
      Parameters p h (evalS G pass s) ∧
      (evalS G pass s).env 14 = (termsInput p h).length ∧
      (evalS G pass s).env 24 = (termsCircuit p h).length := by
  letI : Fact (Irreducible p.irr) := ⟨h.1⟩
  obtain ⟨hpre, hpre24, hpre25⟩ := prefixStart_spec p h s hp.degree hp.dimension hp.coordinates
  generalize eb : evalS (globOf (preparedInput (termsInput p h))) prefixStart s = b at hpre hpre24 hpre25
  have hbp : Parameters p h b := hp.transfer hpre (by decide)
  have hb14 : b.env 14 = Items.firstItem p h :=
    (hpre.env 14 (by decide)).trans h14
  have hb31 : b.env 31 = s.env 31 := hpre.env 31 (by decide)
  obtain ⟨hitem, hend, hcount, hlast, hactive⟩ := Items.request_spec p h b
    hbp.input hb14 hbp.dimension hbp.bank hbp.bankLength hbp.width
    (by convert hpre24 using 1; ring) (by convert hpre25 using 1; ring)
  generalize ec : evalS (globOf (preparedInput (termsInput p h))) Items.itemsPrint b = c
    at hitem hend hcount hlast hactive
  have he : evalS (globOf (preparedInput (termsInput p h))) pass s = c := by
    change evalS (globOf (preparedInput (termsInput p h))) Items.itemsPrint
      (evalS (globOf (preparedInput (termsInput p h))) prefixStart s) = c
    rw [eb, ec]
  have hw : Appends passWrites s c
      (Prefix.words (s.env 31) (termsCircuit p h)) := by
    have hh := (hpre.mono (fun i hi => List.mem_append_left _ hi)).trans
      (hitem.mono (fun i hi => List.mem_append_right _ hi))
    rw [hb31, ← Prefix.words_append, ← Items.request_gates p h] at hh
    exact hh
  change Appends passWrites s (evalS (globOf (preparedInput (termsInput p h))) pass s) _ ∧ _
  rw [he]
  exact ⟨hw, hp.transfer hw (by decide), hend, hcount⟩

theorem pass_wf (d : ℕ) (hd : d ≤ 5) : wfS pass d = true := by
  simp only [pass, wfS, prefixStart_wf d hd, Items.itemsPrint_wf d hd, Bool.and_self]

end NearCubicGates.Adapters.Routing.TermsMachine
