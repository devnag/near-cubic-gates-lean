import SourceAdapters.Routing.TermsMachinePattern

/-! # The product and accumulation gates at the end of an item -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Items

open NearCubicWires NearCubicWires.RepairRepresentation
open ShortPCP.Machines.FL CoordinateMachine Joins

def finishItem : S :=
  .seq (patternSend 3 (.v 35) (.v 28))
    (.seq (patternSend 2 (.v 25) (.sub (.v 24) (.k 1)))
      (.set 25 (.sub (.v 24) (.k 1))))

def finishWrites : List Var := [5, 6, 7, 8, 9, 24, 25]

theorem finishItem_spec (G : Glob) (s : FS) (B : ℕ)
    (hguard : s.env 35 ≤ B) (hexpr : s.env 28 ≤ B) (hacc : s.env 25 ≤ B)
    (hcounter : s.env 24 + 2 ≤ B) (h3 : 3 ≤ B) (hcap : B ≤ G.cap)
    (hL : ∀ v ≤ B, natBitLength v + 2 ≤ G.K) (hN : G.K ≤ G.N) :
    let t := evalS G finishItem s
    Appends finishWrites s t
      (Prefix.words (s.env 31) [.mul (s.env 35) (s.env 28), .add (s.env 25) (s.env 24)]) ∧
      t.env 24 = s.env 24 + 2 ∧ t.env 25 = s.env 24 + 1 := by
  have h1 : min 1 G.cap = 1 := min_eq_left (by omega)
  obtain ⟨aA, a24⟩ := patternSend_spec G s 3 (s.env 35) (s.env 28) (.v 35) (.v 28)
    (by omega) (by simp [evalE]) (by simp [evalE]) (hL 3 h3)
    (hL _ hguard) (hL _ hexpr) hN (by omega)
  generalize ea : evalS G (patternSend 3 (.v 35) (.v 28)) s = a at aA a24
  have a25 : a.env 25 = s.env 25 := aA.env 25 (by decide)
  have a31 : a.env 31 = s.env 31 := aA.env 31 (by decide)
  obtain ⟨bA, b24⟩ := patternSend_spec G a 2 (s.env 25) (s.env 24)
    (.v 25) (.sub (.v 24) (.k 1)) (by omega)
    (by simpa [evalE] using a25)
    (by simp [evalE, a24, h1]) (hL 2 (by omega)) (hL _ hacc) (hL _ (by omega)) hN (by omega)
  generalize eb : evalS G (patternSend 2 (.v 25) (.sub (.v 24) (.k 1))) a = b at bA b24
  let t := b.setv 25 (s.env 24 + 1)
  have he : evalS G finishItem s = t := by
    simp only [finishItem, evalS_seq, ea, eb, evalS_set, evalE, b24, a24, h1]
    congr 1
  have ht : Appends finishWrites b t [] := Appends.setv finishWrites b 25 (by decide) _
  have ha := ((aA.mono (W' := finishWrites) (by decide)).trans
    (bA.mono (W' := finishWrites) (by decide))).trans ht
  rw [he]
  refine ⟨?_, ?_, by simp [t]⟩
  · by_cases hm : s.env 31 = 0 <;>
      simpa only [Prefix.words, patternModeWord, a31, hm, if_true, if_false, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.nil_append, gateWord, List.append_assoc] using ha
  · simp only [t, FS.setv_env, Function.update_of_ne (by decide : (24 : Var) ≠ 25), b24, a24]

theorem finishItem_wf (d : ℕ) (hd : d ≤ 7) : wfS finishItem d = true := by
  simp only [finishItem, wfS]
  have ha := patternSend_wf 3 (.v 35) (.v 28) d (by omega) (by decide) (by decide)
  have hb := patternSend_wf 2 (.v 25) (.sub (.v 24) (.k 1)) d (by omega) (by decide) (by decide)
  simp [ha, hb, dE]

end NearCubicGates.Adapters.Routing.TermsMachine.Items
