import SourceAdapters.Routing.TermsMachineItemsLoopProgram
import SourceAdapters.Routing.TermsMachineBoundsLengths

/-! # Exact execution of the bounded item-flag loop -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Items

open NearCubicWires NearCubicWires.RepairRepresentation
open ShortPCP.Machines.FL CoordinateMachine Joins ACSP Circuit Circuit.PrefixFormula

variable {F : Type} [Field F]

theorem runWhile_spec (G : Glob) (l : Layout) (encode : F → ℕ) (hone : encode 1 = 1)
    (w E D B Bd : ℕ) (hB : Expression.Bounds G l w E D B) (hBd : BdOk G Bd)
    (hconst : ∀ c, encode c ≤ B) (hguard : E + 2 * l.m + 3 ≤ B)
    (hcoord : patternCoord l.m l.m ≤ B) (h4 : 4 ≤ B) (hcap : B ≤ G.cap) (hmN : l.m ≤ G.N)
    (items : List (Item l.m F)) (s : FS) (fuel pos : ℕ)
    (hfuel : items.length + 1 ≤ fuel) (h40 : s.env 40 ≠ 0)
    (hnext : s.env 24 + (items.map itemCost).sum ≤ E)
    (hdepth : ∀ i ∈ items, gateCount i.2 ≤ D) (hlast : s.env 25 + 1 = s.env 24)
    (hat : At (s.env 10) pos (itemsWord encode items)) (h14 : s.env 14 = pos)
    (hend : pos + (itemsWord encode items).length ≤ Bd)
    (h21 : s.env 21 = l.m) (h23 : s.env 23 = packW w (globalBank l))
    (h26 : s.env 26 = (globalBank l).length) (h30 : s.env 30 = w) :
    let u := whileN (fun t => t.env 40 != 0) (evalS G itemBody) fuel s
    u.env 14 = pos + (itemsWord encode items).length ∧
      u.env 24 = s.env 24 + (items.map itemCost).sum ∧
      u.env 25 = s.env 24 + (items.map itemCost).sum - 1 ∧ u.env 40 = 0 ∧
      Appends itemWrites s u (Prefix.words (s.env 31)
        ((itemsGates l (rowIds l.m l.m l.m) items (s.env 25) (s.env 24)).map (codeGate encode))) := by
  induction items generalizing s fuel pos with
  | nil =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          obtain ⟨a40, a14, aA⟩ := readFlag_spec G s 0 pos Bd
            (by simpa [itemsWord] using hat) h14 (by simpa [itemsWord] using hend) hBd
          generalize ea : evalS G readFlag s = a at a40 a14 aA
          have hbody : evalS G itemBody s = a := by
            simp only [itemBody, evalS_seq, ea, evalS_ite, evalE, a40, if_true, evalS_skip]
          have hrun : whileN (fun t => t.env 40 != 0) (evalS G itemBody) (fuel + 1) s = a := by
            simp only [whileN, show (s.env 40 != 0) = true by simpa using h40, if_true, hbody]
            exact while_stopped G fuel a a40
          dsimp only
          rw [hrun]
          simp only [itemsWord, List.flatMap_nil, List.nil_append, List.map_nil, List.sum_nil,
            Nat.add_zero, itemsGates, Prefix.words_nil]
          refine ⟨a14, aA.env 24 (by decide), ?_, a40, aA.mono (by decide)⟩
          rw [aA.env 25 (by decide)]
          omega
  | cons i items ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hword := itemsWord_cons encode i items
          have hats := At.append (hword ▸ hat)
          have hlen : pos + (natWord 1).length +
              (patternWord i.1 ++ exprWord encode i.2).length + (itemsWord encode items).length ≤ Bd := by
            simpa only [hword, List.length_append, Nat.add_assoc] using hend
          simp only [List.map_cons, List.sum_cons] at hnext
          obtain ⟨a40, a14, aA⟩ := readFlag_spec G s 1 pos Bd hats.1 h14 (by omega) hBd
          generalize ea : evalS G readFlag s = a at a40 a14 aA
          have a10 : a.env 10 = s.env 10 := aA.env 10 (by decide)
          have a21 : a.env 21 = l.m := (aA.env 21 (by decide)).trans h21
          have a23 : a.env 23 = packW w (globalBank l) := (aA.env 23 (by decide)).trans h23
          have a26 : a.env 26 = (globalBank l).length := (aA.env 26 (by decide)).trans h26
          have a30 : a.env 30 = w := (aA.env 30 (by decide)).trans h30
          have a24 : a.env 24 = s.env 24 := aA.env 24 (by decide)
          have a25 : a.env 25 = s.env 25 := aA.env 25 (by decide)
          have a31 : a.env 31 = s.env 31 := aA.env 31 (by decide)
          obtain ⟨bA, b14, b24, b25⟩ := itemPrint_spec G a l encode hone i w E D B
            (pos + (natWord 1).length) Bd hB hBd (by omega) (hdepth i (by simp)) hconst
            (by omega) hguard hcoord h4 hcap hmN
            (by simpa only [a10] using (At.append hats.2).1) a14 (by omega) a21 a23 a26 a30
          generalize eb : evalS G itemPrint a = b at bA b14 b24 b25
          let c := b.setv 40 1
          have hc1 : min 1 G.cap = 1 := min_eq_left (by have := hB.five; omega)
          have hbody : evalS G itemBody s = c := by
            simp only [itemBody, evalS_seq, ea, evalS_ite, evalE, a40, one_ne_zero,
              if_false, eb, evalS_set, hc1]
            rfl
          have cA : Appends itemWrites s c (Prefix.words (s.env 31)
              ((itemGates l (rowIds l.m l.m l.m) i (s.env 25) (s.env 24)).map (codeGate encode))) := by
            have hh := ((aA.mono (W' := itemWrites) (by decide)).trans bA).trans
              (Appends.setv itemWrites b 40 (by decide) 1)
            simpa only [List.nil_append, List.append_nil, a31, a25, a24] using hh
          have c10 : c.env 10 = s.env 10 := cA.env 10 (by decide)
          have c21 : c.env 21 = l.m := (cA.env 21 (by decide)).trans h21
          have c23 : c.env 23 = packW w (globalBank l) := (cA.env 23 (by decide)).trans h23
          have c26 : c.env 26 = (globalBank l).length := (cA.env 26 (by decide)).trans h26
          have c30 : c.env 30 = w := (cA.env 30 (by decide)).trans h30
          have c31 : c.env 31 = s.env 31 := cA.env 31 (by decide)
          have c24 : c.env 24 = s.env 24 + itemCost i := by
            simpa [c, a24] using b24
          have c25 : c.env 25 = s.env 24 + itemCost i - 1 := by
            simpa [c, a24] using b25
          have c14 : c.env 14 = pos + (natWord 1).length +
              (patternWord i.1 ++ exprWord encode i.2).length := by
            simpa [c] using b14
          have hcost : 3 ≤ itemCost i := by unfold itemCost; omega
          have hr := ih c fuel (pos + (natWord 1).length + (patternWord i.1 ++ exprWord encode i.2).length)
            (by simp only [List.length_cons] at hfuel; omega) (by simp [c])
            (by omega) (fun j hj => hdepth j (by simp [hj])) (by omega)
            (by simpa only [c10] using (At.append hats.2).2) c14 hlen c21 c23 c26 c30
          have hrun : whileN (fun t => t.env 40 != 0) (evalS G itemBody) (fuel + 1) s =
              whileN (fun t => t.env 40 != 0) (evalS G itemBody) fuel c := by
            simp only [whileN, show (s.env 40 != 0) = true by simpa using h40, if_true, hbody]
          dsimp only
          rw [hrun]
          refine ⟨?_, ?_, ?_, hr.2.2.2.1, ?_⟩
          · rw [hr.1, hword]
            simp only [List.length_append]
            omega
          · simp only [List.map_cons, List.sum_cons]
            rw [hr.2.1, c24]
            omega
          · simp only [List.map_cons, List.sum_cons]
            rw [hr.2.2.1, c24]
            omega
          · have hh := cA.trans hr.2.2.2.2
            rw [itemsGates, List.map_append, Prefix.words_append]
            simpa only [c31, c25, c24] using hh

/-- Full flag loop, with its iteration count derived from the input encoding. -/
theorem itemsPrint_spec (G : Glob) (s : FS) (l : Layout) (encode : F → ℕ) (hone : encode 1 = 1)
    (items : List (Item l.m F)) (w E D B pos Bd : ℕ)
    (hB : Expression.Bounds G l w E D B) (hBd : BdOk G Bd)
    (hnext : s.env 24 + (items.map itemCost).sum ≤ E)
    (hdepth : ∀ i ∈ items, gateCount i.2 ≤ D) (hconst : ∀ c, encode c ≤ B)
    (hlast : s.env 25 + 1 = s.env 24)
    (hguard : E + 2 * l.m + 3 ≤ B) (hcoord : patternCoord l.m l.m ≤ B)
    (h4 : 4 ≤ B) (hcap : B ≤ G.cap) (hmN : l.m ≤ G.N)
    (hat : At (s.env 10) pos (itemsWord encode items)) (h14 : s.env 14 = pos)
    (hend : pos + (itemsWord encode items).length ≤ Bd)
    (h21 : s.env 21 = l.m) (h23 : s.env 23 = packW w (globalBank l))
    (h26 : s.env 26 = (globalBank l).length) (h30 : s.env 30 = w) :
    let t := evalS G itemsPrint s
    Appends itemWrites s t (Prefix.words (s.env 31)
      ((itemsGates l (rowIds l.m l.m l.m) items (s.env 25) (s.env 24)).map (codeGate encode))) ∧
      t.env 14 = pos + (itemsWord encode items).length ∧
      t.env 24 = s.env 24 + (items.map itemCost).sum ∧
      t.env 25 = s.env 24 + (items.map itemCost).sum - 1 ∧ t.env 40 = 0 := by
  let a := s.setv 40 1
  have ha : Appends itemWrites s a [] := Appends.setv itemWrites s 40 (by decide) 1
  have hfuel : items.length + 1 ≤ G.N := by
    have hi := Bounds.items_length_le_word encode items
    have h0 := natWord_pos 0
    have hn := hBd.2
    simp only [itemsWord, List.length_append] at hend
    omega
  have hr := runWhile_spec G l encode hone w E D B Bd hB hBd hconst hguard hcoord h4 hcap hmN
    items a G.N pos hfuel (by simp [a]) (by simpa [a] using hnext) hdepth
    (by simpa [a] using hlast) (by simpa [a] using hat) (by simpa [a] using h14) hend
    (by simpa [a] using h21) (by simpa [a] using h23) (by simpa [a] using h26) (by simpa [a] using h30)
  have he : evalS G itemsPrint s = whileN (fun t => t.env 40 != 0) (evalS G itemBody) G.N a := by
    have h1 : min 1 G.cap = 1 := min_eq_left (by have := hB.five; omega)
    simp only [itemsPrint, evalS_seq, evalE, h1, itemLoop, evalS]
    rfl
  dsimp only
  rw [he]
  refine ⟨?_, hr.1, ?_, ?_, hr.2.2.2.1⟩
  · simpa [a] using ha.trans hr.2.2.2.2
  · simpa [a] using hr.2.1
  · simpa [a] using hr.2.2.1

end NearCubicGates.Adapters.Routing.TermsMachine.Items
