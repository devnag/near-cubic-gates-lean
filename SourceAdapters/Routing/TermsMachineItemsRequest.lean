import SourceAdapters.Routing.TermsMachineItemsLoop
import SourceAdapters.Routing.TermsMachineExpressionRequest
import SourceAdapters.Routing.TermsMachineEncoding

/-! # The complete item pass at the actual terms-request allocation -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Items

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.CanonicalBinary
open ShortPCP.Machines.FL CoordinateMachine Joins ACSP Circuit Circuit.PrefixFormula

/-- Packed-input position immediately after the request's translation bank. -/
noncomputable def firstItem (p : TermsReq) (h : TermsOk p) : ℕ :=
  (natWord p.f).length + (natWord p.l.m).length + (termsCoordWord p h).length +
    (listWord natWord (globalBank p.l)).length

theorem request_items_at (p : TermsReq) (h : TermsOk p) :
    At (bitsValue (termsInput p h)) (firstItem p h) (itemsWord (termsMask p h) p.items) := by
  have hh := (At.append (At.self (termsInput p h))).2
  simpa only [termsInput, List.length_append, Nat.zero_add, firstItem, itemsWord] using hh

theorem request_items_end (p : TermsReq) (h : TermsOk p) :
    firstItem p h + (itemsWord (termsMask p h) p.items).length = (termsInput p h).length := by
  simp only [firstItem, itemsWord, termsInput, List.length_append]

theorem request_gate_count (p : TermsReq) (h : TermsOk p) :
    (termsCircuit p h).length =
      3 * p.l.m ^ 2 + 2 * p.l.m + 1 + (p.items.map itemCost).sum := by
  letI : Fact (Irreducible p.irr) := ⟨h.1⟩
  simp only [termsCircuit, List.length_map, Encoding.compileTerms_length]

/-- All item capacities and the complete suffix read follow from the request. -/
theorem request_spec_of_circuit (p : TermsReq) (h : TermsOk p) (s : FS)
    (hnext : s.env 24 + (p.items.map itemCost).sum ≤ (termsCircuit p h).length)
    (hlast : s.env 25 + 1 = s.env 24)
    (h10 : s.env 10 = bitsValue (termsInput p h)) (h14 : s.env 14 = firstItem p h)
    (h21 : s.env 21 = p.l.m)
    (h23 : s.env 23 = packW (Bounds.wordWidth (termsInput p h).length) (globalBank p.l))
    (h26 : s.env 26 = (globalBank p.l).length)
    (h30 : s.env 30 = Bounds.wordWidth (termsInput p h).length) :
    letI : Fact (Irreducible p.irr) := ⟨h.1⟩
    let G := globOf (preparedInput (termsInput p h))
    let t := evalS G itemsPrint s
    Appends itemWrites s t (Prefix.words (s.env 31)
      ((itemsGates p.l (rowIds p.l.m p.l.m p.l.m) p.items (s.env 25) (s.env 24)).map
        (codeGate (termsMask p h)))) ∧
      t.env 14 = (termsInput p h).length ∧
      t.env 24 = s.env 24 + (p.items.map itemCost).sum ∧
      t.env 25 = s.env 24 + (p.items.map itemCost).sum - 1 ∧ t.env 40 = 0 := by
  letI : Fact (Irreducible p.irr) := ⟨h.1⟩
  have ha := expression_item_arithmetic p h
  have hm : p.l.m ≤ (globOf (preparedInput (termsInput p h))).N := by
    have hm := (Bounds.request_size p h).2.1
    have hn := (prepared_BdOk (termsInput p h)).2
    omega
  have hh := itemsPrint_spec (globOf (preparedInput (termsInput p h))) s p.l
    (termsMask p h) (termsMask_one p h) p.items (Bounds.wordWidth (termsInput p h).length)
    (10 * ((termsInput p h).length + 1)) (termsInput p h).length
    (max (Bounds.arithmeticBound (termsInput p h).length) (2 ^ p.f))
    (firstItem p h) (termsInput p h).length
    (prepared_expression_bounds p h) (prepared_BdOk (termsInput p h))
    (hnext.trans (Bounds.circuit_length_le p h)) (expression_gateCount_le p h)
    (expression_constants_le p h) hlast ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 hm
    (by rw [h10]; exact request_items_at p h) h14 (request_items_end p h).le h21 h23 h26 h30
  simpa only [request_items_end] using hh

/-- Following the exact prefix and zero gate, the pass finishes the full circuit count. -/
theorem request_spec (p : TermsReq) (h : TermsOk p) (s : FS)
    (h10 : s.env 10 = bitsValue (termsInput p h)) (h14 : s.env 14 = firstItem p h)
    (h21 : s.env 21 = p.l.m)
    (h23 : s.env 23 = packW (Bounds.wordWidth (termsInput p h).length) (globalBank p.l))
    (h26 : s.env 26 = (globalBank p.l).length)
    (h30 : s.env 30 = Bounds.wordWidth (termsInput p h).length)
    (h24 : s.env 24 = 3 * p.l.m ^ 2 + 2 * p.l.m + 1)
    (h25 : s.env 25 = 3 * p.l.m ^ 2 + 2 * p.l.m) :
    letI : Fact (Irreducible p.irr) := ⟨h.1⟩
    let G := globOf (preparedInput (termsInput p h))
    let t := evalS G itemsPrint s
    Appends itemWrites s t (Prefix.words (s.env 31)
      ((itemsGates p.l (rowIds p.l.m p.l.m p.l.m) p.items
        (3 * p.l.m ^ 2 + 2 * p.l.m) (3 * p.l.m ^ 2 + 2 * p.l.m + 1)).map
          (codeGate (termsMask p h)))) ∧
      t.env 14 = (termsInput p h).length ∧ t.env 24 = (termsCircuit p h).length ∧
      t.env 25 = (termsCircuit p h).length - 1 ∧ t.env 40 = 0 := by
  letI : Fact (Irreducible p.irr) := ⟨h.1⟩
  have hh := request_spec_of_circuit p h s (by rw [h24, request_gate_count])
    (by rw [h25, h24]) h10 h14 h21 h23 h26 h30
  simpa only [h24, h25, request_gate_count] using hh

end NearCubicGates.Adapters.Routing.TermsMachine.Items
