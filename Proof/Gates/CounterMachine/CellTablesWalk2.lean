import Proof.Gates.CounterMachine.CellTablesWalk

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicGates.Close.CounterMachine.PrefixProg (Oth Oth.refl Oth.trans j1 yv yJ)

theorem WS.len {b d : DS VV MM} {L R Q : List ℕ} (h : WS b d L R Q) : d.rc sN + R.length = L.length := by
  have := congrArg List.length h.rem
  have := h.le
  simp only [List.length_drop] at *
  omega

/-! ## One circuit -/

def circW : St VV MM :=
  .seq (rdW wX) (.seq (.op (.mul wX gS wY)) (.seq (skV wY) (.seq (rdW wX) (.seq (.op (.copy wY wX))
  (.seq (.op (.add wY wX)) (.seq (skV wY) (.seq (rdW wX) (skV wX))))))))

theorem WS.circW {C : Ctx} {b d : DS VV MM} {L R Q : List ℕ} {n : ℕ} (Cc : NCircuit n)
    (h : WS b d L (circN Cc ++ R) Q) (hL : L.length < 2 ^ C.Wd) (hgS : d.env gS = 2 * n + 3) :
    Hs C circW d (5 * (circN Cc).length + 40) (fun e => WS b e L R Q ∧ Fr d e [wX, wY, wN, j1, yJ]) := by
  have hlen := circN_length Cc
  have hl0 := h.len
  have hsp : circN Cc ++ R = Cc.gates.length :: (Cc.gates.flatMap gateN ++ (Cc.coeffs.length ::
      (Cc.coeffs.flatMap intN ++ (Cc.table.length :: (Cc.table.map bitN ++ R))))) := by
    simp [circN, List.append_assoc]
  rw [hsp] at h
  have g1 := flatMap_gateN_length Cc.gates
  have g2 := flatMap_intN_length Cc.coeffs
  have g3 : (Cc.table.map bitN).length = Cc.table.length := List.length_map _
  rw [List.length_append] at hl0
  apply Hx.hs
  refine Hs.then (h.rdW hL wX (by decide) (by decide)) (fun e1 ⟨w1, v1, f1⟩ n1 hn1 => ?_)
  have e1S : e1.env gS = 2 * n + 3 := by rw [f1 gS (by decide)]; exact hgS
  refine Hs.then (hs_mul C wX gS wY e1 (by decide) (by decide) (by decide) (by rw [v1, e1S]; nlinarith))
    (fun e2 he2 n2 hn2 => ?_)
  subst he2
  have w2 := w1.set wY (e1.env wX * e1.env gS) (by decide) (by decide)
  refine Hs.then (w2.skV hL wY (by decide) (by decide) (by rw [DS.set_env_self, v1, e1S, g1])) (fun e3 ⟨w3, f3⟩ n3 hn3 => ?_)
  refine Hs.then (w3.rdW hL wX (by decide) (by decide)) (fun e4 ⟨w4, v4, f4⟩ n4 hn4 => ?_)
  refine Hs.then (hs_copy C wY wX e4 (by decide)) (fun e5 he5 n5 hn5 => ?_)
  subst he5
  refine Hs.then (hs_add C wY wX _ (by decide) (by vsimp [v4]; omega)) (fun e6 he6 n6 hn6 => ?_)
  subst he6
  have w6 := (w4.set wY (e4.env wX) (by decide) (by decide)).set wY ((e4.set wY (e4.env wX)).env wY +
    (e4.set wY (e4.env wX)).env wX) (by decide) (by decide)
  refine Hs.then (w6.skV hL wY (by decide) (by decide) (by vsimp [v4, g2]; omega)) (fun e7 ⟨w7, f7⟩ n7 hn7 => ?_)
  refine Hs.then (w7.rdW hL wX (by decide) (by decide)) (fun e8 ⟨w8, v8, f8⟩ n8 hn8 => ?_)
  refine Hs.last (w8.skV hL wX (by decide) (by decide) (by rw [v8, g3])) (fun e9 ⟨w9, f9⟩ n9 hn9 => ?_)
  refine ⟨⟨w9, ?_⟩, ?_⟩
  · refine Fr.trans (Fr.weaken f1 (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.weaken f3 (by decide))
      (Fr.trans (Fr.weaken f4 (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.weaken f7 (by decide)) (Fr.trans (Fr.weaken f8 (by decide)) (Fr.weaken f9 (by decide)))))))))
  · rw [g1] at hn3; rw [g2] at hn7; rw [g3] at hn9
    omega

/-! ## The call -/

def callW : St VV MM :=
  .seq (skW 2) (.seq circW (.seq circW (.seq (rdW wX) (.seq (skV wX) (skW 3)))))

theorem WS.callW {C : Ctx} {b d : DS VV MM} {L R Q : List ℕ} (c : Call)
    (h : WS b d L (callN c ++ R) Q) (hL : L.length < 2 ^ C.Wd) (hgS : d.env gS = 2 * c.n + 3) :
    Hs C callW d (5 * (callN c).length + 120) (fun e => WS b e L R Q ∧ Fr d e [wX, wY, wN, j1, yJ]) := by
  have hl0 := h.len
  have hsp : callN c ++ R = [c.n, kindTag c.kind] ++ (circN c.first ++ (circN c.second ++
      (c.parity.length :: (c.parity ++ (ratN c.radius ++ R))))) := by
    simp [callN, List.append_assoc]
  have hlen : (callN c).length = 2 + (circN c.first).length + (circN c.second).length + 1 + c.parity.length + 3 := by
    simp [callN, ratN_length]; omega
  rw [hsp] at h
  apply Hx.hs
  refine Hs.then (WS.skW 2 h hL rfl) (fun e1 ⟨w1, f1⟩ n1 hn1 => ?_)
  refine Hs.then (w1.circW c.first hL (by rw [f1 gS (by decide)]; exact hgS)) (fun e2 ⟨w2, f2⟩ n2 hn2 => ?_)
  refine Hs.then (w2.circW c.second hL (by rw [f2 gS (by decide), f1 gS (by decide)]; exact hgS))
    (fun e3 ⟨w3, f3⟩ n3 hn3 => ?_)
  refine Hs.then (w3.rdW hL wX (by decide) (by decide)) (fun e4 ⟨w4, v4, f4⟩ n4 hn4 => ?_)
  refine Hs.then (w4.skV hL wX (by decide) (by decide) v4) (fun e5 ⟨w5, f5⟩ n5 hn5 => ?_)
  refine Hs.last (WS.skW 3 w5 hL (by simp [ratN_length])) (fun e6 ⟨w6, f6⟩ n6 hn6 => ?_)
  refine ⟨⟨w6, ?_⟩, by omega⟩
  exact Fr.trans (Fr.weaken f1 (by decide)) (Fr.trans f2 (Fr.trans f3 (Fr.trans (Fr.weaken f4 (by decide))
    (Fr.trans (Fr.weaken f5 (by decide)) (Fr.weaken f6 (by decide))))))

/-! ## The parameter record -/

/-- `wF := Σ` of `x` records. -/
def sumW (x : Fin VV) : St VV MM :=
  .seq (.op (.zero wF)) (forS wI x (.seq (rdW wX) (.op (.add wF wX))))

theorem WS.sumW {C : Ctx} {b d : DS VV MM} {L A R Q : List ℕ} (h : WS b d L (A ++ R) Q)
    (hL : L.length < 2 ^ C.Wd) (x : Fin VV) (hx : x ∉ [wF, wI, wX, wN])
    (hlen : d.env x = A.length) (hS : A.sum < 2 ^ C.Wd) :
    Hs C (sumW x) d (A.length * 9 + 6) (fun e => WS b e L R Q ∧ e.env wF = A.sum ∧ Fr d e [wF, wI, wX, wN]) := by
  have hl0 := h.len
  rw [List.length_append] at hl0
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := A.length * (5 + 4) + 4) (hs_zero C wF d) (fun d1 hd1 => ?_)) (by omega)
    (fun _ h => h)
  subst hd1
  let I : ℕ → DS VV MM → Prop := fun k e => WS b e L (A.drop k ++ R) Q ∧ e.env wF = (A.take k).sum ∧
    Fr d e [wF, wI, wX, wN]
  have hx' : x ≠ wI := fun e => hx (by simp [e])
  refine Hs.mono (forS_spec' (C := C) wI x (Ne.symm hx') _ (d.set wF 0) A.length (by omega) I 5
    (fun k e v ⟨i1, i2, i3⟩ => ⟨i1.set wI v (by decide) (by decide), by rw [DS.set_env_ne _ _ (by decide)]; exact i2,
      Fr.trans i3 (Fr.set e v (by decide))⟩)
    ⟨by simpa using h.set wF 0 (by decide) (by decide), by simp, Fr.set d 0 (by decide)⟩
    (by rw [DS.set_env_ne _ _ (fun e => hx (by simp [e]))]; exact hlen) ?_) le_rfl ?_
  · intro k hk e ⟨i1, i2, i3⟩ hek hex
    have hcons : A.drop k ++ R = A[k] :: (A.drop (k + 1) ++ R) := by
      rw [List.drop_eq_getElem_cons hk]; rfl
    rw [hcons] at i1
    refine Hs.seq (t1 := 3) (t2 := 1) (i1.rdW hL wX (by decide) (by decide)) (fun e1 ⟨w1, v1, f1⟩ => ?_)
    have hsum : (A.take (k + 1)).sum = (A.take k).sum + A[k] := by
      rw [List.take_add_one, List.sum_append]; simp [List.getElem?_eq_getElem hk]
    have hle : (A.take (k + 1)).sum ≤ A.sum := by
      have h2 := congrArg List.sum (List.take_append_drop (k + 1) A)
      rw [List.sum_append] at h2; omega
    have e1F : e1.env wF = (A.take k).sum := by rw [f1 wF (by decide)]; exact i2
    refine Hs.mono (hs_add C wF wX e1 (by decide) (by rw [e1F, v1]; omega)) le_rfl ?_
    rintro e2 rfl
    refine ⟨⟨w1.set wF _ (by decide) (by decide), by rw [DS.set_env_self, e1F, v1, hsum],
      Fr.trans i3 (Fr.trans (Fr.weaken f1 (by decide)) (Fr.set _ _ (by decide)))⟩, ?_, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide), f1 wI (by decide)]; exact hek
    · have hxF : x ≠ wF := fun h' => hx (by simp [h'])
      have hxX : x ≠ wX := fun h' => hx (by simp [h'])
      have hxN : x ≠ wN := fun h' => hx (by simp [h'])
      rw [DS.set_env_ne _ _ hxF, f1 x (by simp [hxX, hxN])]; exact hex
  · rintro e ⟨⟨i1, i2, i3⟩, _, _⟩
    exact ⟨by simpa using i1, by rw [i2, List.take_of_length_le le_rfl], i3⟩

def parW : St VV MM :=
  .seq (skW 2) (.seq (rdW wW) (.seq (skW 3) (.seq (rdW wK) (.seq (skW 3) (.seq (rdW wP) (.seq (rdW wE)
  (.seq (rdW wNP) (.seq (cpQ wNP) (.seq (skW 9) (.seq (rdW wM1) (.seq (skW 1) (.seq (rdW wNF) (.seq (sumW wNF)
  (.seq (rdW wA) (skW 1)))))))))))))))

def parT : List (Fin VV) := [wX, wY, wN, wI, wF, j1, yJ, yv, wW, wK, wP, wE, wNP, wM1, wNF, wA]

/-- The values `parW` reads. -/
structure ParV (e : DS VV MM) (p : Params) : Prop where
  W : e.env wW = p.W
  k : e.env wK = p.k
  P : e.env wP = p.P
  ex : e.env wE = p.e
  np : e.env wNP = (p.primes.sort (· ≤ ·)).length
  M1 : e.env wM1 = p.M1
  F : e.env wF = p.factors.sum
  A : e.env wA = p.A

theorem WS.parW {C : Ctx} {b d : DS VV MM} {L R Q : List ℕ} (p : Params)
    (h : WS b d L (paramsN p ++ R) Q) (hL : L.length < 2 ^ C.Wd) (hS : p.factors.sum < 2 ^ C.Wd) :
    Hs C parW d (9 * (paramsN p).length + 120) (fun e => WS b e L R (Q ++ p.primes.sort (· ≤ ·)) ∧ ParV e p ∧
      Fr d e parT) := by
  have hl0 := h.len
  have hsp : paramsN p ++ R = [p.n, bitN p.pair] ++ (p.W :: (ratN p.beta ++ (p.k :: ([p.T, p.m, p.Dmax] ++
      (p.P :: p.e :: (p.primes.sort (· ≤ ·)).length :: (p.primes.sort (· ≤ ·) ++
      ([p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++ (p.M1 :: ([p.J] ++ (p.factors.length ::
      (p.factors ++ (p.A :: ([p.Lambda] ++ R))))))))))))) := by
    simp only [paramsN, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
  have hlen : (paramsN p).length = 27 + (p.primes.sort (· ≤ ·)).length + p.factors.length := by
    simp [paramsN, ratN_length]; omega
  rw [hsp] at h
  apply Hx.hs
  refine Hs.then (WS.skW 2 h hL rfl) (fun e1 ⟨w1, f1⟩ n1 hn1 => ?_)
  refine Hs.then (w1.rdW hL wW (by decide) (by decide)) (fun e2 ⟨w2, v2, f2⟩ n2 hn2 => ?_)
  refine Hs.then (WS.skW 3 w2 hL (by simp [ratN_length])) (fun e3 ⟨w3, f3⟩ n3 hn3 => ?_)
  refine Hs.then (w3.rdW hL wK (by decide) (by decide)) (fun e4 ⟨w4, v4, f4⟩ n4 hn4 => ?_)
  refine Hs.then (WS.skW 3 w4 hL rfl) (fun e5 ⟨w5, f5⟩ n5 hn5 => ?_)
  refine Hs.then (w5.rdW hL wP (by decide) (by decide)) (fun e6 ⟨w6, v6, f6⟩ n6 hn6 => ?_)
  refine Hs.then (w6.rdW hL wE (by decide) (by decide)) (fun e7 ⟨w7, v7, f7⟩ n7 hn7 => ?_)
  refine Hs.then (w7.rdW hL wNP (by decide) (by decide)) (fun e8 ⟨w8, v8, f8⟩ n8 hn8 => ?_)
  refine Hs.then (w8.cpQ hL wNP (by decide) (by decide) v8) (fun e9 ⟨w9, f9⟩ n9 hn9 => ?_)
  refine Hs.then (WS.skW 9 w9 hL (by simp [ratN_length])) (fun e10 ⟨w10, f10⟩ n10 hn10 => ?_)
  refine Hs.then (w10.rdW hL wM1 (by decide) (by decide)) (fun e11 ⟨w11, v11, f11⟩ n11 hn11 => ?_)
  refine Hs.then (WS.skW 1 w11 hL rfl) (fun e12 ⟨w12, f12⟩ n12 hn12 => ?_)
  refine Hs.then (w12.rdW hL wNF (by decide) (by decide)) (fun e13 ⟨w13, v13, f13⟩ n13 hn13 => ?_)
  refine Hs.then (w13.sumW hL wNF (by decide) v13 hS) (fun e14 ⟨w14, v14, f14⟩ n14 hn14 => ?_)
  refine Hs.then (w14.rdW hL wA (by decide) (by decide)) (fun e15 ⟨w15, v15, f15⟩ n15 hn15 => ?_)
  refine Hs.last (WS.skW 1 w15 hL rfl) (fun e16 ⟨w16, f16⟩ n16 hn16 => ?_)
  refine ⟨⟨w16, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [f16 wW (by decide), f15 wW (by decide), f14 wW (by decide), f13 wW (by decide), f12 wW (by decide),
      f11 wW (by decide), f10 wW (by decide), f9 wW (by decide), f8 wW (by decide), f7 wW (by decide),
      f6 wW (by decide), f5 wW (by decide), f4 wW (by decide), f3 wW (by decide), v2]
  · rw [f16 wK (by decide), f15 wK (by decide), f14 wK (by decide), f13 wK (by decide), f12 wK (by decide),
      f11 wK (by decide), f10 wK (by decide), f9 wK (by decide), f8 wK (by decide), f7 wK (by decide),
      f6 wK (by decide), f5 wK (by decide), v4]
  · rw [f16 wP (by decide), f15 wP (by decide), f14 wP (by decide), f13 wP (by decide), f12 wP (by decide),
      f11 wP (by decide), f10 wP (by decide), f9 wP (by decide), f8 wP (by decide), f7 wP (by decide), v6]
  · rw [f16 wE (by decide), f15 wE (by decide), f14 wE (by decide), f13 wE (by decide), f12 wE (by decide),
      f11 wE (by decide), f10 wE (by decide), f9 wE (by decide), f8 wE (by decide), v7]
  · rw [f16 wNP (by decide), f15 wNP (by decide), f14 wNP (by decide), f13 wNP (by decide), f12 wNP (by decide),
      f11 wNP (by decide), f10 wNP (by decide), f9 wNP (by decide), v8]
  · rw [f16 wM1 (by decide), f15 wM1 (by decide), f14 wM1 (by decide), f13 wM1 (by decide), f12 wM1 (by decide),
      v11]
  · rw [f16 wF (by decide), f15 wF (by decide), v14]
  · rw [f16 wA (by decide), v15]
  · exact Fr.trans (Fr.weaken f1 (by decide)) (Fr.trans (Fr.weaken f2 (by decide)) (Fr.trans (Fr.weaken f3 (by decide))
      (Fr.trans (Fr.weaken f4 (by decide)) (Fr.trans (Fr.weaken f5 (by decide)) (Fr.trans (Fr.weaken f6 (by decide))
      (Fr.trans (Fr.weaken f7 (by decide)) (Fr.trans (Fr.weaken f8 (by decide)) (Fr.trans (Fr.weaken f9 (by decide))
      (Fr.trans (Fr.weaken f10 (by decide)) (Fr.trans (Fr.weaken f11 (by decide)) (Fr.trans (Fr.weaken f12 (by decide))
      (Fr.trans (Fr.weaken f13 (by decide)) (Fr.trans (Fr.weaken f14 (by decide)) (Fr.trans (Fr.weaken f15 (by decide))
      (Fr.weaken f16 (by decide))))))))))))))))
  · omega

/-! ## The witness -/

/-- One coefficient list of the witness: its length, then its `intN`s. -/
def witSeg (c : Call) (wt : Wit c.n) (sr : ℕ × ℕ) : List ℕ :=
  (wt.coef sr.1 sr.2).length :: (wt.coef sr.1 sr.2).flatMap intN

theorem sum_getElem! {α : Type} [Inhabited α] (g : α → ℕ) :
    ∀ S : List α, ∑ k ∈ Finset.range S.length, g S[k]! = (S.map g).sum
  | [] => by simp
  | x :: S => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, sum_getElem! g S]
    ring

theorem flatMap_drop_cons {α β : Type} (S : List α) (f : α → List β) (k : ℕ) (hk : k < S.length) :
    (S.drop k).flatMap f = f S[k] ++ (S.drop (k + 1)).flatMap f := by
  rw [List.drop_eq_getElem_cons hk, List.flatMap_cons]

def witW : St VV MM :=
  .seq (rdW wX) (.seq (skV wX) (forS wI gJR (.seq (rdW wX) (.seq (.op (.copy wY wX)) (.seq (.op (.add wY wX))
    (skV wY))))))

theorem WS.witW {C : Ctx} {b d : DS VV MM} {L R Q : List ℕ} (c : Call) (p : Params) (wt : Wit c.n)
    (h : WS b d L (witN c p wt ++ R) Q) (hL : L.length < 2 ^ C.Wd) (hJR : d.env gJR = p.J * roleCount c.kind) :
    Hs C CellTablesProg.witW d (20 * (witN c p wt).length + 20) (fun e => WS b e L R Q ∧
      Fr d e [wX, wY, wN, wI, j1, yJ]) := by
  have hl0 := h.len
  have hSl : (srList c p).length = p.J * roleCount c.kind := by
    simp [srList, List.length_flatMap]
  have hsp : witN c p wt ++ R = (coordsOf wt.I).length :: (coordsOf wt.I ++ ((srList c p).flatMap (witSeg c wt) ++ R)) := by
    simp only [witN, List.append_assoc, List.singleton_append, List.cons_append]; rfl
  have hlen : (witN c p wt).length = 1 + (coordsOf wt.I).length + ((srList c p).flatMap (witSeg c wt)).length := by
    simp [witN, witSeg]; omega
  have hS2 : (srList c p).length ≤ ((srList c p).flatMap (witSeg c wt)).length := by
    rw [List.length_flatMap]
    calc (srList c p).length = ((srList c p).map fun _ => 1).sum := by simp
      _ ≤ _ := List.sum_le_sum (by intro i _; simp [witSeg])
  rw [hsp] at h
  have hl1 := h.len
  simp only [List.length_append, List.length_cons] at hl1
  apply Hx.hs
  refine Hs.then (h.rdW hL wX (by decide) (by decide)) (fun e1 ⟨w1, v1, f1⟩ n1 hn1 => ?_)
  refine Hs.then (w1.skV hL wX (by decide) (by decide) v1) (fun e2 ⟨w2, f2⟩ n2 hn2 => ?_)
  have e2J : e2.env gJR = (srList c p).length := by rw [f2 gJR (by decide), f1 gJR (by decide), hJR, hSl]
  let I : ℕ → DS VV MM → Prop := fun k e => WS b e L (((srList c p).drop k).flatMap (witSeg c wt) ++ R) Q ∧
    Fr e2 e [wX, wY, wN, wI, j1, yJ]
  have hloop := forS_spec (C := C) wI gJR (by decide) (.seq (CellTablesProg.rdW wX) (.seq (.op (.copy wY wX))
      (.seq (.op (.add wY wX)) (CellTablesProg.skV wY)))) e2 (srList c p).length (by omega) I
    (fun k => 5 * (witSeg c wt (srList c p)[k]!).length + 10)
    (fun k e v ⟨i1, i2⟩ => ⟨i1.set wI v (by decide) (by decide), Fr.trans i2 (Fr.set e v (by decide))⟩)
    ⟨by simpa using w2, Fr.refl _ _⟩ e2J ?_
  · refine Hs.last hloop (fun e3 ⟨⟨w3, f3⟩, _, _⟩ n3 hn3 => ?_)
    refine ⟨⟨by simpa using w3, Fr.trans (Fr.weaken f1 (by decide)) (Fr.trans (Fr.weaken f2 (by decide)) f3)⟩, ?_⟩
    have hsum : ∑ k ∈ Finset.range (srList c p).length, (5 * (witSeg c wt (srList c p)[k]!).length + 10 + 4) =
        5 * ((srList c p).flatMap (witSeg c wt)).length + 14 * (srList c p).length := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_getElem! (fun sr => (witSeg c wt sr).length), List.length_flatMap]
      simp; ring
    rw [hsum] at hn3
    omega
  · intro k hk e ⟨i1, i2⟩ hek hem
    have hseg : (witSeg c wt (srList c p)[k]).length ≤ ((srList c p).flatMap (witSeg c wt)).length := by
      rw [List.length_flatMap]
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩)
    have g2 := flatMap_intN_length (wt.coef (srList c p)[k].1 (srList c p)[k].2)
    have hsg : (witSeg c wt (srList c p)[k]).length = 1 + 2 * (wt.coef (srList c p)[k].1 (srList c p)[k].2).length := by
      simp [witSeg, g2]; omega
    rw [flatMap_drop_cons _ _ k hk] at i1
    simp only [witSeg, List.cons_append, List.append_assoc] at i1
    apply Hx.hs
    refine Hs.then (i1.rdW hL wX (by decide) (by decide)) (fun e1 ⟨w1, v1, f1⟩ n1 hn1 => ?_)
    refine Hs.then (hs_copy C wY wX e1 (by decide)) (fun e5 he5 n5 hn5 => ?_)
    subst he5
    refine Hs.then (hs_add C wY wX _ (by decide) (by vsimp [v1]; omega)) (fun e6 he6 n6 hn6 => ?_)
    subst he6
    have w6 := (w1.set wY (e1.env wX) (by decide) (by decide)).set wY ((e1.set wY (e1.env wX)).env wY +
      (e1.set wY (e1.env wX)).env wX) (by decide) (by decide)
    refine Hs.last (w6.skV hL wY (by decide) (by decide) (by vsimp [v1, g2]; omega)) (fun e7 ⟨w7, f7⟩ n7 hn7 => ?_)
    have hfr : Fr e e7 [wX, wY, wN, j1, yJ] := Fr.trans (Fr.weaken f1 (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken f7 (by decide))))
    refine ⟨⟨⟨w7, Fr.trans i2 (Fr.weaken hfr (by decide))⟩, by rw [hfr wI (by decide)]; exact hek, by rw [hfr gJR (by decide)]; exact hem⟩, ?_⟩
    rw [getElem!_pos (srList c p) k hk, hsg]
    rw [g2] at hn7
    omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
