import SourceAdapters.Routing.TermsMachineItemsData
import SourceAdapters.Routing.TermsMachineItemsFinish
import SourceAdapters.Routing.TermsMachineExpression

/-! # Actual printing of one guard, equation, product, and accumulator -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Items

open NearCubicWires
open ShortPCP.Machines.FL CoordinateMachine Joins ACSP
open Circuit Circuit.Encoding Circuit.PrefixFormula

/-- The item flag has already been consumed. -/
def itemPrint : S := .seq patternPrint (.seq Expression.program finishItem)

def itemWrites : List Var :=
  [5, 6, 7, 8, 9, 14, 15, 24, 25, 28, 29, 33, 34, 35, 36, 37, 38, 39, 40, 43, 46]

theorem itemPrint_spec {F : Type} [Field F] (G : Glob) (s : FS) (l : Layout)
    (encode : F → ℕ) (hone : encode 1 = 1) (item : Item l.m F)
    (w E D B pos Bd : ℕ) (hB : Expression.Bounds G l w E D B) (hBd : BdOk G Bd)
    (hnext : s.env 24 + itemCost item ≤ E) (hdepth : gateCount item.2 ≤ D)
    (hconst : ∀ c, encode c ≤ B) (hacc : s.env 25 ≤ B)
    (hguard : E + 2 * l.m + 3 ≤ B) (hcoord : patternCoord l.m l.m ≤ B)
    (h4 : 4 ≤ B) (hcap : B ≤ G.cap) (hmN : l.m ≤ G.N)
    (hat : At (s.env 10) pos (patternWord item.1 ++ exprWord encode item.2))
    (h14 : s.env 14 = pos) (hend : pos + (patternWord item.1 ++ exprWord encode item.2).length ≤ Bd)
    (h21 : s.env 21 = l.m) (h23 : s.env 23 = packW w (globalBank l))
    (h26 : s.env 26 = (globalBank l).length) (h30 : s.env 30 = w) :
    let t := evalS G itemPrint s
    Appends itemWrites s t
      (Prefix.words (s.env 31)
        ((itemGates l (rowIds l.m l.m l.m) item (s.env 25) (s.env 24)).map (codeGate encode))) ∧
      t.env 14 = pos + (patternWord item.1 ++ exprWord encode item.2).length ∧
      t.env 24 = s.env 24 + itemCost item ∧ t.env 25 = s.env 24 + itemCost item - 1 := by
  have hcost : itemCost item = 3 + ((List.finRange l.m).map (patternCost item.1)).sum + gateCount item.2 := rfl
  have hL (v : ℕ) (hv : v ≤ B) : natBitLength v + 2 ≤ G.K := hB.bits.mono hv
  have hats := At.append hat
  have hend' : pos + (patternWord item.1).length + (exprWord encode item.2).length ≤ Bd := by
    simpa only [List.length_append, Nat.add_assoc] using hend
  obtain ⟨aA, a14, a24, a35, _⟩ := patternPrint_spec G s encode hone item.1 pos Bd B
    hats.1 h14 (by omega) hBd h21 (by omega) hcoord h4 hcap hL hB.K_N hmN
  generalize ea : evalS G patternPrint s = a at aA a14 a24 a35
  have a10 : a.env 10 = s.env 10 := aA.env 10 (by decide)
  have a23 : a.env 23 = packW w (globalBank l) := (aA.env 23 (by decide)).trans h23
  have a26 : a.env 26 = (globalBank l).length := (aA.env 26 (by decide)).trans h26
  have a30 : a.env 30 = w := (aA.env 30 (by decide)).trans h30
  have a31 : a.env 31 = s.env 31 := aA.env 31 (by decide)
  have a25 : a.env 25 = s.env 25 := aA.env 25 (by decide)
  obtain ⟨bA, b14, b24, b28, _, _⟩ := Expression.program_spec_of_constants G a l encode item.2
    w E D B (pos + (patternWord item.1).length) Bd hB hBd (by omega) hdepth hconst
    (by simpa only [a10] using hats.2) a14 hend' a23 a26 a30
  generalize eb : evalS G Expression.program a = b at bA b14 b24 b28
  have b35 : b.env 35 = s.env 24 + ((List.finRange l.m).map (patternCost item.1)).sum :=
    (bA.env 35 (by decide)).trans a35
  have b25 : b.env 25 = s.env 25 := (bA.env 25 (by decide)).trans a25
  have b31 : b.env 31 = s.env 31 := (bA.env 31 (by decide)).trans a31
  obtain ⟨cA, c24, c25⟩ := finishItem_spec G b B (by omega) (by omega) (by omega)
    (by omega) (by omega) hcap hL hB.K_N
  generalize ec : evalS G finishItem b = c at cA c24 c25
  have h24 : c.env 24 = s.env 24 + itemCost item := by omega
  have h25 : c.env 25 = s.env 24 + itemCost item - 1 := by omega
  have h14' : c.env 14 = pos + (patternWord item.1 ++ exprWord encode item.2).length := by
    rw [cA.env 14 (by decide), b14, List.length_append]
    omega
  let pg := patternGates (F := F) (rowIds l.m l.m l.m) item.1 (s.env 24)
  have hp : a.env 24 = s.env 24 + pg.length := by
    simp only [pg, patternGates_length]
    omega
  have hg : b.env 35 = s.env 24 + pg.length - 1 := by
    simp only [pg, patternGates_length]
    omega
  have heq : (itemGates l (rowIds l.m l.m l.m) item (s.env 25) (s.env 24)).map (codeGate encode) =
      pg.map (codeGate encode) ++
        (expressionGates l (a.env 24) item.2).map (codeGate encode) ++
        [CodeGate.mul (b.env 35) (b.env 28), .add (b.env 25) (b.env 24)] := by
    simp only [itemGates, List.map_append, List.map_cons, List.map_nil, codeGate]
    simp only [b24, b28, hg, b25, hp]
    rfl
  have hwa : Appends itemWrites s a (Prefix.words (s.env 31) (pg.map (codeGate encode))) := by
    exact aA.mono (by decide)
  have hw := (hwa.trans (bA.mono (W' := itemWrites) (by decide))).trans
    (cA.mono (W' := itemWrites) (by decide))
  have hh : Appends itemWrites s c
      (Prefix.words (s.env 31)
        ((itemGates l (rowIds l.m l.m l.m) item (s.env 25) (s.env 24)).map (codeGate encode))) := by
    rw [heq, Prefix.words_append, Prefix.words_append]
    simpa only [a31, b31] using hw
  have he : evalS G itemPrint s = c := by simp only [itemPrint, evalS_seq, ea, eb, ec]
  dsimp only
  rw [he]
  exact ⟨hh, h14', h24, h25⟩

theorem itemPrint_wf (d : ℕ) (hd : d ≤ 6) : wfS itemPrint d = true := by
  simp only [itemPrint, wfS, patternPrint_wf d (by omega), Expression.wellFormed d hd,
    finishItem_wf d (by omega), Bool.true_and]

end NearCubicGates.Adapters.Routing.TermsMachine.Items
