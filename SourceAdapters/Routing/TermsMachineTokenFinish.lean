import SourceAdapters.Routing.TermsMachineStack
import SourceAdapters.Routing.TermsMachineEmit

/-!
# Completing one postfix token

The construction in `lem:generator`: after its operands are selected, each expression token removes
those operands, pushes the new absolute gate reference, and emits the gate.
The same program updates its stack and counter in the counting pass.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open CoordinateMachine

def finishToken : S := .seq pushNext gateStep

theorem finishToken_spec (G : Glob) (s : FS) (w n : ℕ) (st : List ℕ)
    (h28 : s.env 28 = packW w st) (h29 : s.env 29 = st.length)
    (h30 : s.env 30 = w) (h24 : s.env 24 = n)
    (hp : packW w (n :: st) ≤ G.cap) (hd : st.length + 1 ≤ G.cap)
    (h7 : natBitLength (s.env 7) + 2 ≤ G.K)
    (h8 : natBitLength (s.env 8) + 2 ≤ G.K)
    (h9 : natBitLength (s.env 9) + 2 ≤ G.K)
    (hN : G.K ≤ G.N) (hc : n + 1 ≤ G.cap) :
    let t := evalS G finishToken s
    t.env 28 = packW w (n :: st) ∧ t.env 29 = st.length + 1 ∧ t.env 24 = n + 1 ∧
      Appends [5, 6, 24, 28, 29] s t
        (if s.env 31 = 0 then [] else
          natWord (s.env 7) ++ natWord (s.env 8) ++ natWord (s.env 9)) := by
  obtain ⟨p28, p29, hpW⟩ := pushNext_spec G s w n st h28 h29 h30 h24 hp hd
  let u := evalS G pushNext s
  have u7 : u.env 7 = s.env 7 := hpW.env 7 (by decide)
  have u8 : u.env 8 = s.env 8 := hpW.env 8 (by decide)
  have u9 : u.env 9 = s.env 9 := hpW.env 9 (by decide)
  have u24 : u.env 24 = n := (hpW.env 24 (by decide)).trans h24
  have u31 : u.env 31 = s.env 31 := hpW.env 31 (by decide)
  obtain ⟨hgW, g24⟩ := gateStep_spec G u (by simpa only [u7] using h7)
    (by simpa only [u8] using h8) (by simpa only [u9] using h9) hN
    (by simpa only [u24] using hc)
  change (evalS G gateStep u).env 28 = _ ∧ (evalS G gateStep u).env 29 = _ ∧
    (evalS G gateStep u).env 24 = _ ∧ _
  refine ⟨(hgW.env 28 (by decide)).trans p28, (hgW.env 29 (by decide)).trans p29,
    by simpa only [u24] using g24, ?_⟩
  have h := (hpW.mono (W' := [5, 6, 24, 28, 29]) (by simp)).trans
    (hgW.mono (by simp))
  change Appends [5, 6, 24, 28, 29] s (evalS G gateStep u) _
  simpa only [List.nil_append, u7, u8, u9, u31] using h

def dropFinish (k : ℕ) : S := .seq (dropStack k) finishToken

theorem dropFinish_spec (G : Glob) (s : FS) (w n k : ℕ) (st : List ℕ)
    (h28 : s.env 28 = packW w st) (h29 : s.env 29 = st.length)
    (h30 : s.env 30 = w) (h24 : s.env 24 = n)
    (hs : ∀ a ∈ st, a < 2 ^ w) (hk : k ≤ G.cap) (hkw : k * w ≤ G.cap)
    (hp : packW w (n :: st.drop k) ≤ G.cap) (hd : st.length - k + 1 ≤ G.cap)
    (h7 : natBitLength (s.env 7) + 2 ≤ G.K)
    (h8 : natBitLength (s.env 8) + 2 ≤ G.K)
    (h9 : natBitLength (s.env 9) + 2 ≤ G.K)
    (hN : G.K ≤ G.N) (hc : n + 1 ≤ G.cap) :
    let t := evalS G (dropFinish k) s
    t.env 28 = packW w (n :: st.drop k) ∧ t.env 29 = st.length - k + 1 ∧
      t.env 24 = n + 1 ∧ Appends [5, 6, 24, 28, 29] s t
        (if s.env 31 = 0 then [] else
          natWord (s.env 7) ++ natWord (s.env 8) ++ natWord (s.env 9)) := by
  obtain ⟨p28, p29, hpW⟩ := dropStack_spec G s w k st h28 h29 h30 hs hk hkw
  let u := evalS G (dropStack k) s
  have u7 : u.env 7 = s.env 7 := hpW.env 7 (by decide)
  have u8 : u.env 8 = s.env 8 := hpW.env 8 (by decide)
  have u9 : u.env 9 = s.env 9 := hpW.env 9 (by decide)
  have u24 : u.env 24 = n := (hpW.env 24 (by decide)).trans h24
  have u30 : u.env 30 = w := (hpW.env 30 (by decide)).trans h30
  have u31 : u.env 31 = s.env 31 := hpW.env 31 (by decide)
  obtain ⟨f28, f29, f24, hfW⟩ := finishToken_spec G u w n (st.drop k) p28
    (by simpa using p29) u30 u24 hp (by simpa using hd)
    (by simpa only [u7] using h7) (by simpa only [u8] using h8)
    (by simpa only [u9] using h9) hN hc
  change (evalS G finishToken u).env 28 = _ ∧ (evalS G finishToken u).env 29 = _ ∧
    (evalS G finishToken u).env 24 = _ ∧ Appends [5, 6, 24, 28, 29] s (evalS G finishToken u) _
  refine ⟨f28, by simpa using f29, f24, ?_⟩
  have h := (hpW.mono (W' := [5, 6, 24, 28, 29]) (by simp)).trans hfW
  simpa only [List.nil_append, u7, u8, u9, u31] using h

theorem finishToken_wf (d : ℕ) (hd : d < 8) : wfS finishToken d = true := by
  simp only [finishToken, wfS, pushNext_wf, gateStep_wf d hd, Bool.and_self]

theorem dropFinish_wf (k d : ℕ) (hd : d < 8) : wfS (dropFinish k) d = true := by
  simp only [dropFinish, wfS, dropStack_wf, finishToken_wf d hd, Bool.and_self]

end NearCubicGates.Adapters.Routing.TermsMachine
