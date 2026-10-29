import SourceAdapters.Routing.TermsMachineTokenProgram

/-! Numerical contracts for the five literal postfix token branches. -/
set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine.Expression

open NearCubicWires
open ShortPCP.Machines.FL CoordinateMachine Joins ACSP

def Small (G : Glob) (n : ℕ) : Prop := natBitLength n + 2 ≤ G.K

def GateFits (G : Glob) : ArithGate ℕ → Prop
  | .input i => Small G 0 ∧ Small G i ∧ Small G 0
  | .const c => Small G 1 ∧ Small G c ∧ Small G 0
  | .add a b => Small G 2 ∧ Small G a ∧ Small G b
  | .mul a b => Small G 3 ∧ Small G a ∧ Small G b

structure DispatchBounds (G : Glob) (l : Layout) (w : ℕ) : Prop where
  five : 5 ≤ G.cap
  width_power : 2^w ≤ G.cap
  twice_width : 2*w ≤ G.cap
  bank_words : ∀ x ∈ globalBank l, x < 2^w
  bank_N : (globalBank l).length ≤ G.N
  bank_count : (globalBank l).length+1 ≤ G.cap
  bank_product : (globalBank l).length*w ≤ G.cap
  K_N : G.K ≤ G.N

def tokenProgram : TermTok → S
  | .const _ => applyToken 1 (.v 39) (.k 0) 0
  | .read _ => .seq resolveRead (applyToken 0 (.v 15) (.k 0) 0)
  | .add => applyToken 2 (stackAt 1) (stackAt 0) 2
  | .mul => applyToken 3 (stackAt 1) (stackAt 0) 2
  | .square => applyToken 3 (stackAt 0) (stackAt 0) 1

theorem dispatch_eq (G : Glob) (s : FS) (t : TermTok)
    (h38 : s.env 38 = tokenTag t) (hc : 5 ≤ G.cap) :
    evalS G dispatch s = evalS G (tokenProgram t) s := by
  have h1 : min 1 G.cap = 1 := min_eq_left (by omega)
  have h2 : min 2 G.cap = 2 := min_eq_left (by omega)
  have h3 : min 3 G.cap = 3 := min_eq_left (by omega)
  cases t <;> norm_num [dispatch, tokenProgram, tokenTag, evalS_ite, evalE, h38, h1, h2, h3]

theorem tokenProgram_spec (G : Glob) (s : FS) (l : Layout) (w n : ℕ)
    (st : List ℕ) (t : TermTok) (hb : DispatchBounds G l w)
    (h39 : s.env 39 = tokenValue t) (h23 : s.env 23 = packW w (globalBank l))
    (h26 : s.env 26 = (globalBank l).length)
    (h28 : s.env 28 = packW w st) (h29 : s.env 29 = st.length)
    (h30 : s.env 30 = w) (h24 : s.env 24 = n)
    (hs : ∀ a ∈ st, a < 2^w)
    (hp : packW w (n :: st.drop (popCount t)) ≤ G.cap)
    (hd : st.length - popCount t + 1 ≤ G.cap)
    (hf : GateFits G (emittedGate l st t)) (hc : n+1 ≤ G.cap) :
    let u := evalS G (tokenProgram t) s
    u.env 28 = packW w (n :: st.drop (popCount t)) ∧
      u.env 29 = st.length-popCount t+1 ∧ u.env 24 = n+1 ∧
      Appends dispatchWrites s u (Prefix.words (s.env 31) [codeGate id (emittedGate l st t)]) := by
  have hc5 := hb.five
  have hkw := hb.twice_width
  have hat (tag xv k : ℕ) (hk : k ≤ 1) :
      evalE G ((s.setv 7 tag).setv 8 xv) (stackAt k) = st.getD k 0 := by
    exact stackAt_spec G _ w k st (by simpa using h28) (by simpa using h30) hs
      (by omega) (by nlinarith) hb.width_power
  have hat' (tag k : ℕ) (hk : k ≤ 1) :
      evalE G (s.setv 7 tag) (stackAt k) = st.getD k 0 := by
    exact stackAt_spec G _ w k st (by simpa using h28) (by simpa using h30) hs
      (by omega) (by nlinarith) hb.width_power
  cases t with
  | const c =>
      have h := applyToken_spec G s 1 (.v 39) (.k 0) c 0 w n 0 st (by omega)
        (by simpa [evalE, tokenValue] using h39) (by simp [evalE])
        h28 h29 h30 h24 hs (by omega) (by simp) hp hd hf.1 hf.2.1 hf.2.2 hb.K_N hc
      refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
      simpa [tokenProgram, Prefix.words, codeGate, emittedGate, gateWord] using
        h.2.2.2.mono (W' := dispatchWrites) (by simp [tokenWrites, dispatchWrites])
  | read v =>
      have hr := resolveRead_spec G s (globalBank l) w v h39 h23 h26 h30
        hb.bank_words hb.bank_N hb.bank_count hb.bank_product hb.width_power
      let u := evalS G resolveRead s
      have hu15 : u.env 15 = readIndex l v := hr.1
      have hu28 : u.env 28 = packW w st := (hr.2.env 28 (by decide)).trans h28
      have hu29 : u.env 29 = st.length := (hr.2.env 29 (by decide)).trans h29
      have hu30 : u.env 30 = w := (hr.2.env 30 (by decide)).trans h30
      have hu24 : u.env 24 = n := (hr.2.env 24 (by decide)).trans h24
      have hu31 : u.env 31 = s.env 31 := hr.2.env 31 (by decide)
      have h := applyToken_spec G u 0 (.v 15) (.k 0) (readIndex l v) 0 w n 0 st (by omega)
        (by simpa [evalE] using hu15) (by simp [evalE])
        hu28 hu29 hu30 hu24 hs (by omega) (by simp) hp hd hf.1 hf.2.1 hf.2.2 hb.K_N hc
      refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
      have hall := (hr.2.mono (W' := dispatchWrites) (by simp [dispatchWrites])).trans
        (h.2.2.2.mono (by simp [tokenWrites, dispatchWrites]))
      simpa [tokenProgram, u, hu31, Prefix.words, emittedGate, codeGate, gateWord] using hall
  | add =>
      have h := applyToken_spec G s 2 (stackAt 1) (stackAt 0) (st.getD 1 0) (st.getD 0 0)
        w n 2 st (by omega) (hat' 2 1 (by omega)) (hat 2 _ 0 (by omega))
        h28 h29 h30 h24 hs (by omega) hkw hp hd hf.1 hf.2.1 hf.2.2 hb.K_N hc
      refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
      simpa [tokenProgram, Prefix.words, codeGate, emittedGate, gateWord] using
        h.2.2.2.mono (W' := dispatchWrites) (by simp [tokenWrites, dispatchWrites])
  | mul =>
      have h := applyToken_spec G s 3 (stackAt 1) (stackAt 0) (st.getD 1 0) (st.getD 0 0)
        w n 2 st (by omega) (hat' 3 1 (by omega)) (hat 3 _ 0 (by omega))
        h28 h29 h30 h24 hs (by omega) hkw hp hd hf.1 hf.2.1 hf.2.2 hb.K_N hc
      refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
      simpa [tokenProgram, Prefix.words, codeGate, emittedGate, gateWord] using
        h.2.2.2.mono (W' := dispatchWrites) (by simp [tokenWrites, dispatchWrites])
  | square =>
      have h := applyToken_spec G s 3 (stackAt 0) (stackAt 0) (st.getD 0 0) (st.getD 0 0)
        w n 1 st (by omega) (hat' 3 0 (by omega)) (hat 3 _ 0 (by omega))
        h28 h29 h30 h24 hs (by omega) (by omega) hp hd hf.1 hf.2.1 hf.2.2 hb.K_N hc
      refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
      simpa [tokenProgram, Prefix.words, codeGate, emittedGate, gateWord] using
        h.2.2.2.mono (W' := dispatchWrites) (by simp [tokenWrites, dispatchWrites])

theorem dispatch_spec (G : Glob) (s : FS) (l : Layout) (w n : ℕ)
    (st : List ℕ) (t : TermTok) (hb : DispatchBounds G l w)
    (h38 : s.env 38 = tokenTag t) (h39 : s.env 39 = tokenValue t)
    (h23 : s.env 23 = packW w (globalBank l)) (h26 : s.env 26 = (globalBank l).length)
    (h28 : s.env 28 = packW w st) (h29 : s.env 29 = st.length)
    (h30 : s.env 30 = w) (h24 : s.env 24 = n)
    (hs : ∀ a ∈ st, a < 2^w)
    (hp : packW w (n :: st.drop (popCount t)) ≤ G.cap)
    (hd : st.length-popCount t+1 ≤ G.cap)
    (hf : GateFits G (emittedGate l st t)) (hc : n+1 ≤ G.cap) :
    let u := evalS G dispatch s
    u.env 28 = packW w (n :: st.drop (popCount t)) ∧
      u.env 29 = st.length-popCount t+1 ∧ u.env 24 = n+1 ∧
      Appends dispatchWrites s u (Prefix.words (s.env 31) [codeGate id (emittedGate l st t)]) := by
  rw [dispatch_eq G s t h38 hb.five]
  exact tokenProgram_spec G s l w n st t hb h39 h23 h26 h28 h29 h30 h24 hs hp hd hf hc

end NearCubicGates.Adapters.Routing.TermsMachine.Expression
