import SourceAdapters.Routing.TermsMachineExpressionBounds

/-! One parser-and-dispatch iteration, and the explicit expression terminator. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Expression

open NearCubicWires.RepairRepresentation (natWord)
open ShortPCP.Machines.FL CoordinateMachine Joins ACSP

def stepWrites : List Var := tokenReadWrites ++ dispatchWrites

def endWrites : List Var := tokenReadWrites ++ [40]

def endWord : List Bool := natWord 5 ++ natWord 0

def tokenWords (ts : List TermTok) : List Bool := ts.flatMap termTokWord ++ endWord

theorem body_step (G : Glob) (s : FS) (l : Layout) (w n pos Bd : ℕ)
    (st : List ℕ) (t : TermTok) (hb : DispatchBounds G l w)
    (hat : At (s.env 10) pos (termTokWord t)) (h14 : s.env 14 = pos)
    (hend : pos+(termTokWord t).length ≤ Bd) (hBd : BdOk G Bd)
    (h23 : s.env 23 = packW w (globalBank l)) (h26 : s.env 26 = (globalBank l).length)
    (h28 : s.env 28 = packW w st) (h29 : s.env 29 = st.length)
    (h30 : s.env 30 = w) (h24 : s.env 24 = n)
    (hs : ∀ a ∈ st, a < 2^w)
    (hp : packW w (n :: st.drop (popCount t)) ≤ G.cap)
    (hd : st.length-popCount t+1 ≤ G.cap)
    (hf : GateFits G (emittedGate l st t)) (hc : n+1 ≤ G.cap) :
    let u := evalS G body s
    u.env 28 = packW w (n :: st.drop (popCount t)) ∧
      u.env 29 = st.length-popCount t+1 ∧ u.env 24 = n+1 ∧
      u.env 14 = pos+(termTokWord t).length ∧
      Appends stepWrites s u (Prefix.words (s.env 31) [codeGate id (emittedGate l st t)]) := by
  obtain ⟨a38, a39, a14, ha⟩ := readToken_spec G s (tokenTag t) (tokenValue t) pos Bd
    (by simpa only [tokenWord_eq] using hat) h14 (by simpa only [tokenWord_eq] using hend) hBd
  let a := evalS G readToken s
  have a23 : a.env 23 = packW w (globalBank l) := (ha.env 23 (by decide)).trans h23
  have a26 : a.env 26 = (globalBank l).length := (ha.env 26 (by decide)).trans h26
  have a28 : a.env 28 = packW w st := (ha.env 28 (by decide)).trans h28
  have a29 : a.env 29 = st.length := (ha.env 29 (by decide)).trans h29
  have a30 : a.env 30 = w := (ha.env 30 (by decide)).trans h30
  have a24 : a.env 24 = n := (ha.env 24 (by decide)).trans h24
  have a31 : a.env 31 = s.env 31 := ha.env 31 (by decide)
  have h := dispatch_spec G a l w n st t hb a38 a39 a23 a26 a28 a29 a30 a24 hs hp hd hf hc
  have he : evalS G body s = evalS G dispatch a := by
    have htag := tokenTag_lt t
    simp only [body, evalS_seq, evalS_ite, evalE, min_eq_left hb.five]
    change (if (if a.env 38 = 5 then 1 else 0) = 0 then _ else _) = _
    have hn : tokenTag t ≠ 5 := by omega
    simp only [show a.env 38 = tokenTag t from a38, if_neg hn, if_true]
    rfl
  dsimp only
  rw [he]
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
  · rw [h.2.2.2.env 14 (by decide)]
    simpa only [tokenWord_eq] using a14
  · have hh := (ha.mono (W' := stepWrites) (by simp [stepWrites, tokenReadWrites, dispatchWrites])).trans
      (h.2.2.2.mono (by simp [stepWrites, tokenReadWrites, dispatchWrites]))
    simpa only [a31, List.nil_append] using hh

theorem body_end (G : Glob) (s : FS) (pos Bd : ℕ)
    (hat : At (s.env 10) pos endWord) (h14 : s.env 14 = pos)
    (hend : pos+endWord.length ≤ Bd) (hBd : BdOk G Bd) (hc : 5 ≤ G.cap) :
    let u := evalS G body s
    u.env 40 = 0 ∧ u.env 14 = pos+endWord.length ∧ Appends endWrites s u [] := by
  obtain ⟨a38, _, a14, ha⟩ := readToken_spec G s 5 0 pos Bd hat h14 hend hBd
  let a := evalS G readToken s
  have he : evalS G body s = a.setv 40 0 := by
    simp only [body, evalS_seq, evalS_ite, evalE, min_eq_left hc, a38, if_true,
      one_ne_zero, if_false, evalS_set, Nat.zero_min]
    rfl
  dsimp only
  rw [he]
  refine ⟨by simp, ?_, ?_⟩
  · change a.env 14 = pos+(natWord 5 ++ natWord 0).length
    exact a14
  · simpa using (ha.mono (W' := endWrites) (by simp [endWrites, tokenReadWrites])).trans
      (Appends.setv endWrites a 40 (by simp [endWrites]) 0)

theorem whileN_stopped (G : Glob) (fuel : ℕ) (s : FS) (h40 : s.env 40 = 0) :
    whileN (fun t => t.env 40 != 0) (evalS G body) fuel s = s := by
  cases fuel <;> simp [whileN, h40]

end NearCubicGates.Adapters.Routing.TermsMachine.Expression
