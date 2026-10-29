import SourceAdapters.Routing.TermsMachineTokenFinish
import SourceAdapters.Routing.TermsMachineLookup
import SourceAdapters.Routing.TermsMachineTokens

/-!
# Gate arguments and variable resolution for postfix tokens

The construction in `lem:generator`: each token supplies the next gate's arguments, removes its
operand references, and pushes the new gate. Variable reads resolve the raw
mask against the actual bank, including the first-occurrence and absent cases.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open CoordinateMachine

def applyToken (tag : ℕ) (x y : E) (k : ℕ) : S :=
  .seq (.set 7 (.k tag)) (.seq (.set 8 x) (.seq (.set 9 y) (dropFinish k)))

def tokenWrites : List Var := [5, 6, 7, 8, 9, 24, 28, 29]

theorem applyToken_spec (G : Glob) (s : FS) (tag : ℕ) (x y : E) (xv yv w n k : ℕ)
    (st : List ℕ) (htag : tag ≤ G.cap)
    (hx : evalE G (s.setv 7 tag) x = xv)
    (hy : evalE G ((s.setv 7 tag).setv 8 xv) y = yv)
    (h28 : s.env 28 = packW w st) (h29 : s.env 29 = st.length)
    (h30 : s.env 30 = w) (h24 : s.env 24 = n)
    (hs : ∀ a ∈ st, a < 2 ^ w) (hk : k ≤ G.cap) (hkw : k * w ≤ G.cap)
    (hp : packW w (n :: st.drop k) ≤ G.cap) (hd : st.length - k + 1 ≤ G.cap)
    (h7 : natBitLength tag + 2 ≤ G.K) (h8 : natBitLength xv + 2 ≤ G.K)
    (h9 : natBitLength yv + 2 ≤ G.K) (hN : G.K ≤ G.N) (hc : n + 1 ≤ G.cap) :
    let t := evalS G (applyToken tag x y k) s
    t.env 28 = packW w (n :: st.drop k) ∧ t.env 29 = st.length - k + 1 ∧
      t.env 24 = n + 1 ∧ Appends tokenWrites s t
        (if s.env 31 = 0 then [] else natWord tag ++ natWord xv ++ natWord yv) := by
  let u := ((s.setv 7 tag).setv 8 xv).setv 9 yv
  have he : evalS G (applyToken tag x y k) s = evalS G (dropFinish k) u := by
    simp only [applyToken, evalS_seq, evalS_set, evalE, min_eq_left htag, hx, hy, u]
  have hu : Appends tokenWrites s u [] := by
    simpa using (Appends.setv tokenWrites s 7 (by simp [tokenWrites]) tag).trans
      ((Appends.setv tokenWrites _ 8 (by simp [tokenWrites]) xv).trans
        (Appends.setv tokenWrites _ 9 (by simp [tokenWrites]) yv))
  obtain ⟨f28, f29, f24, hf⟩ := dropFinish_spec G u w n k st
    (by simpa [u] using h28) (by simpa [u] using h29)
    (by simpa [u] using h30) (by simpa [u] using h24) hs hk hkw hp hd
    (by simpa [u] using h7) (by simpa [u] using h8) (by simpa [u] using h9) hN hc
  dsimp only
  rw [he]
  refine ⟨f28, f29, f24, ?_⟩
  simpa [u] using hu.trans (hf.mono (by simp [tokenWrites]))

/-- Zero encodes the main input; positive values encode one plus a raw bank mask. -/
def resolveRead : S :=
  .ite (.eq (.v 39) (.k 0)) (.set 15 (.k 0))
    (.seq (.set 46 (.sub (.v 39) (.k 1))) lookup)

def resolveIndex (bank : List ℕ) : Option ℕ → ℕ
  | none => 0
  | some b => 1 + bank.idxOf b

theorem resolveRead_spec (G : Glob) (s : FS) (bank : List ℕ) (width : ℕ) (v : Option ℕ)
    (h39 : s.env 39 = Joins.varCode v)
    (h23 : s.env 23 = packW width bank) (h26 : s.env 26 = bank.length)
    (h30 : s.env 30 = width) (hwords : ∀ x ∈ bank, x < 2 ^ width)
    (hN : bank.length ≤ G.N) (hcount : bank.length + 1 ≤ G.cap)
    (hproduct : bank.length * width ≤ G.cap) (hwidth : 2 ^ width ≤ G.cap) :
    let t := evalS G resolveRead s
    t.env 15 = resolveIndex bank v ∧ Appends [15, 43, 46] s t [] := by
  have h1 : 1 ≤ G.cap := by omega
  cases v with
  | none =>
      have he : evalS G resolveRead s = s.setv 15 0 := by
        simp [resolveRead, evalS_ite, evalE, h39, Joins.varCode]
      rw [he]
      exact ⟨by simp [resolveIndex], Appends.setv _ s 15 (by simp) 0⟩
  | some b =>
      let u := s.setv 46 b
      have he : evalS G resolveRead s = evalS G lookup u := by
        simp [resolveRead, evalS_ite, evalE, h39, Joins.varCode, min_eq_left h1, u]
      obtain ⟨r15, rw, rip⟩ := lookup_spec G u bank width b
        (by simpa [u] using h23) (by simpa [u] using h26) (by simpa [u] using h30)
        (by simp [u]) hwords hN hcount hproduct hwidth
      have hr : Appends [15, 43] u (evalS G lookup u) [] :=
        ⟨rw.env, by simpa using rw.out, rw.fl, rw.fp, rip, rw.bad⟩
      rw [he]
      refine ⟨r15, ?_⟩
      simpa only [List.nil_append] using
        (Appends.setv [15, 43, 46] s 46 (by simp) b).trans (hr.mono (by simp))

theorem applyToken_wf (tag k : ℕ) (x y : E) (d : ℕ) (hd : d < 8)
    (hx : dE x < 16) (hy : dE y < 16) : wfS (applyToken tag x y k) d = true := by
  simp [applyToken, wfS, dE, dropFinish_wf k d hd, hx, hy]

theorem resolveRead_wf (d : ℕ) (hd : d ≤ 7) : wfS resolveRead d = true := by
  simp [resolveRead, wfS, dE, lookup_wf d hd]

end NearCubicGates.Adapters.Routing.TermsMachine
