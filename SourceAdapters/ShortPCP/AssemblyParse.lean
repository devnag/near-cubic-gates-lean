import SourceAdapters.ShortPCP.AssemblyCells

/-!
# Cell-language parsers for the top-level machine of input 6

Continuation of `AssemblyCells` (proof of `thm:short-pcp-ours`; `app:short-pcp-proof`, "The exact Lean interface"):

* `parseX`: read `frame x̄` from the input and keep the index of its last `1` (for `x̄ = x10^j` this is `n = |x|`,
  `lem:tm-ram`; the mask machine needs `n`);
* `copyNatK`: copy one `natWord` from the callee's output, doubly framed and counted, keeping its value;
* `copyFrameK`, `copyFrames`: copy framed words from the callee's output, doubly framed and counted (the callee's
  output is `listWord frame S`, P05's multiset).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Assembly

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-! ## Words -/

/-- The index of the last `true` of `l` (positions counted from `k`), or `acc` when there is none. -/
def lastTrue : List Bool → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | b :: l, k, acc => lastTrue l (k + 1) (if b then k else acc)

theorem lastTrue_append (l m : List Bool) (k acc : ℕ) :
    lastTrue (l ++ m) k acc = lastTrue m (k + l.length) (lastTrue l k acc) := by
  induction l generalizing k acc with
  | nil => simp [lastTrue]
  | cons b l ih => simp only [List.cons_append, lastTrue, ih, List.length_cons]; ring_nf

theorem lastTrue_zeros (j k acc : ℕ) : lastTrue (List.replicate j false) k acc = acc := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, lastTrue, ih]

/-- For `x̄ = x10^j` the last `1` is at index `|x|`. -/
theorem lastTrue_padded (x : List Bool) (j : ℕ) : lastTrue (x ++ true :: List.replicate j false) 0 0 = x.length := by
  rw [lastTrue_append]; simp [lastTrue, lastTrue_zeros]

theorem lastTrue_take_succ (l : List Bool) (k : ℕ) (h : k < l.length) :
    lastTrue (l.take (k + 1)) 0 0 = if l.getD k false then k else lastTrue (l.take k) 0 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, lastTrue_append]
  simp [lastTrue, List.length_take, min_eq_left h.le, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem frame_length' (l : List Bool) : (frame l).length = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [frame, ih]; ring

theorem frame_even (l : List Bool) (i : ℕ) (hi : i ≤ l.length) : (frame l).getD (2 * i) false = decide (i < l.length) := by
  induction l generalizing i with
  | nil => simp at hi; subst hi; rfl
  | cons b l ih =>
    rcases i with _ | i
    · simp [frame]
    · simp only [frame, List.length_cons] at hi ⊢
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, List.getD_cons_succ, List.getD_cons_succ, ih i (by omega)]
      simp

theorem frame_odd (l : List Bool) (i : ℕ) (hi : i < l.length) : (frame l).getD (2 * i + 1) false = l.getD i false := by
  induction l generalizing i with
  | nil => simp at hi
  | cons b l ih =>
    rcases i with _ | i
    · simp [frame]
    · simp only [frame, List.length_cons] at hi ⊢
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring, List.getD_cons_succ, List.getD_cons_succ, ih i (by omega)]
      simp

theorem take_succ (l : List Bool) (k : ℕ) (h : k < l.length) : l.take (k + 1) = l.take k ++ [l.getD k false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_of_drop {cw u rest : List Bool} {cp : ℕ} (h : cw.drop cp = u ++ rest) (j : ℕ) (hj : j < u.length) :
    cw.getD (cp + j) false = u.getD j false := by
  have := bitOf_drop h j hj
  unfold bitOf at this
  cases h1 : cw.getD (cp + j) false <;> cases h2 : u.getD j false <;> simp_all

/-! ## Loops one pass at a time -/

theorem hs_loopT {c : Cnd VV} {s : St VV MM} {a : DS VV MM} {t t' : ℕ} {R : DS VV MM → Prop} (hc : c.wf)
    (he : c.eval a = true) (h : Hs C s a t (fun b => Hs C (.loop c s) b t' R)) : Hs C (.loop c s) a (t + t' + 2) R := by
  obtain ⟨b, n, hx, hn, d, k, hx2, hk, hd⟩ := h
  exact ⟨d, n + k + 2, Ex.loopT hc he hx hx2, by omega, hd⟩

theorem hs_loopF {c : Cnd VV} {s : St VV MM} {a : DS VV MM} {R : DS VV MM → Prop} (hc : c.wf)
    (he : c.eval a = false) (hR : R a) : Hs C (.loop c s) a 2 R :=
  ⟨a, 2, Ex.loopF hc he, le_rfl, hR⟩

/-! ## Parsing `frame x̄` -/

/-- Read `frame x̄`; `nR := ` the index of its last `1`. -/
def parseX : St VV MM :=
  .seq (.op (.rdI sA)) (.seq (.op (.inc ipR)) (.seq (.op (.zero sC)) (.seq (.op (.zero nR))
    (.loop (.eq sA v1) (.seq (.op (.rdI sB)) (.seq (.op (.inc ipR)) (.seq (.ite (.eq sB v1) (.op (.copy nR sC)) skipS)
      (.seq (.op (.inc sC)) (.seq (.op (.rdI sA)) (.op (.inc ipR)))))))))))

/-- The registers `parseX` may change. -/
def parseT : List (Fin VV) := [sA, sB, sC, nR, ipR, vJ]

theorem parseX_spec (a : DS VV MM) (hc : Cst a) (hip : a.env ipR = a.ip) (xb rest : List Bool)
    (hcw : C.inp.drop a.ip = frame xb ++ rest) (hW : C.inp.length + 1 < 2 ^ C.Wd) :
    Hs C parseX a (xb.length * (12 + 2) + 10) (fun b => b.env nR = lastTrue xb 0 0 ∧
      b.ip = a.ip + (frame xb).length ∧ b.env ipR = b.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧
      b.kc = a.kc ∧ Fr a b parseT) := by
  have hfl := frame_length' xb
  have hlen : a.ip + (frame xb).length ≤ C.inp.length := by
    have := congrArg List.length hcw; simp only [List.length_drop, List.length_append] at this; omega
  have hbit : ∀ j, j < (frame xb).length → bitOf C.inp (a.ip + j) = ((frame xb).getD j false).toNat :=
    fun j hj => bitOf_drop hcw j hj
  let I : ℕ → DS VV MM → Prop := fun k b => b.ip = a.ip + 2 * k + 1 ∧ b.env ipR = b.ip ∧
    b.env sA = (decide (k < xb.length)).toNat ∧ b.env sC = k ∧ b.env nR = lastTrue (xb.take k) 0 0 ∧ b.out = a.out ∧
    b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b parseT
  have hloop : ∀ b, I 0 b → Hs C (.loop (.eq sA v1) (.seq (.op (.rdI sB)) (.seq (.op (.inc ipR))
      (.seq (.ite (.eq sB v1) (.op (.copy nR sC)) skipS) (.seq (.op (.inc sC)) (.seq (.op (.rdI sA))
        (.op (.inc ipR)))))))) b (xb.length * (12 + 2) + 2) (I xb.length) := by
    refine Hs.loopN (c := .eq sA v1) (show sA ≠ v1 by decide) I xb.length 12 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      have hb1 : b.env v1 = 1 := by rw [h10 v1 (by decide)]; exact hc.one
      have hcb : Cst b := Cst.of_fr hc h10 (by decide)
      refine ⟨by simp [Cnd.eval, h3, hb1, hk], ?_⟩
      have hx : bitOf C.inp (a.ip + (2 * k + 1)) = (xb.getD k false).toNat := by
        rw [hbit _ (by omega), frame_odd xb k hk]
      refine Hs.seq (t1 := 1) (t2 := 10) (hs_rdI C sB b (by omega)) (fun d hd => ?_)
      subst hd
      refine Hs.seq (t1 := 1) (t2 := 8) (hs_inc C ipR _ (by vsimp [h2, h1]; omega)) (fun d hd => ?_)
      subst hd
      set d := ({ b.set sB (bitOf C.inp b.ip) with ip := b.ip + 1 } : DS VV MM).set ipR
        (({ b.set sB (bitOf C.inp b.ip) with ip := b.ip + 1 } : DS VV MM).env ipR + 1) with hd
      have dsB : d.env sB = (xb.getD k false).toNat := by
        rw [hd]; vsimp [h1]; rw [show a.ip + 2 * k + 1 = a.ip + (2 * k + 1) by ring, hx]
        simp [List.getD_eq_getElem?_getD]
      have dsC : d.env sC = k := by rw [hd]; vsimp [h4]
      have dv1 : d.env v1 = 1 := by rw [hd]; vsimp [hb1]
      refine Hs.seq (t1 := 2) (t2 := 5)
        (R1 := fun e => e.env nR = lastTrue (xb.take (k + 1)) 0 0 ∧ e.ip = d.ip ∧ e.out = d.out ∧ e.kin = d.kin ∧
          e.kout = d.kout ∧ e.kc = d.kc ∧ Fr d e [nR, vJ])
        (Hs.ite (c := .eq sB v1) (show sB ≠ v1 by decide) (fun he => ?_) (fun he => ?_)) (fun e he => ?_)
      · have hxk : xb.getD k false = true := by
          revert he; simp only [Cnd.eval, dsB, dv1]; cases xb.getD k false <;> simp
        have hxk' : xb[k]?.getD false = true := by rw [← List.getD_eq_getElem?_getD]; exact hxk
        refine Hs.mono (hs_copy C nR sC d (by decide)) le_rfl ?_
        rintro e rfl
        refine ⟨by vsimp [dsC, lastTrue_take_succ xb k hk, hxk'], rfl, rfl, rfl, rfl, rfl, Fr.set d _ (by simp)⟩
      · have hxk : xb.getD k false = false := by
          revert he; simp only [Cnd.eval, dsB, dv1]; cases xb.getD k false <;> simp
        have hxk' : xb[k]?.getD false = false := by rw [← List.getD_eq_getElem?_getD]; exact hxk
        refine Hs.mono (skip_spec d) le_rfl ?_
        rintro e rfl
        have hdn : d.env nR = lastTrue (xb.take k) 0 0 := by rw [hd]; vsimp [h5]
        refine ⟨by vsimp [hdn, lastTrue_take_succ xb k hk, hxk'], rfl, rfl, rfl, rfl, rfl, Fr.set d _ (by simp)⟩
      · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := he
        have esC : e.env sC = k := by rw [e7 sC (by decide), dsC]
        have eip : e.env ipR = a.ip + 2 * k + 2 := by rw [e7 ipR (by decide), hd]; vsimp [h2, h1]
        refine Hs.seq (t1 := 1) (t2 := 3) (hs_inc C sC e (by rw [esC]; omega)) (fun g hg => ?_)
        subst hg
        refine Hs.seq (t1 := 1) (t2 := 1) (hs_rdI C sA _ (by simp [e2, hd, h1]; omega)) (fun g hg => ?_)
        subst hg
        refine Hs.mono (hs_inc C ipR _ (by vsimp [eip]; omega)) le_rfl ?_
        rintro g rfl
        have hip' : e.ip = a.ip + 2 * k + 2 := by rw [e2, hd]; simp [h1]
        refine ⟨by simp [hip']; ring, by vsimp [eip, hip'], ?_, by vsimp [esC], by vsimp [e1], ?_, ?_, ?_, ?_, ?_⟩
        · vsimp [hip']
          rw [show a.ip + 2 * k + 2 = a.ip + 2 * (k + 1) by ring, hbit _ (by omega), frame_even xb (k + 1) (by omega)]
        · simp [e3, hd, h6]
        · simp [e4, hd, h7]
        · simp [e5, hd, h8]
        · simp [e6, hd, h9]
        · intro y hy
          simp only [parseT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
          vsimp [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2]
          rw [e7 y (by simp [hy.2.2.2.1, hy.2.2.2.2.2]), hd]
          vsimp [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2]
          exact h10 y (by simp [parseT, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2])
    · intro b hb
      obtain ⟨-, -, h3, -, -, -, -, -, -, h10⟩ := hb
      have hb1 : b.env v1 = 1 := by rw [h10 v1 (by decide)]; exact hc.one
      simp [Cnd.eval, h3, hb1]
  -- the prefix
  have hx0 : bitOf C.inp a.ip = (decide (0 < xb.length)).toNat := by
    have := hbit 0 (by omega); rw [Nat.add_zero] at this; rw [this, show (0 : ℕ) = 2 * 0 by rfl, frame_even xb 0 (by omega)]
  refine Hs.mono (t := 1 + (1 + (1 + (1 + (xb.length * (12 + 2) + 2) + 1) + 1) + 1) + 1)
    (Hs.seq (hs_rdI C sA a (by omega)) (fun d hd => ?_)) (by omega) (fun _ h => h)
  subst hd
  refine Hs.seq (hs_inc C ipR _ (by vsimp [hip]; omega)) (fun d hd => ?_)
  subst hd
  refine Hs.seq (hs_zero C sC _) (fun d hd => ?_)
  subst hd
  refine Hs.seq (hs_zero C nR _) (fun d hd => ?_)
  subst hd
  refine Hs.mono (hloop _ ⟨by simp, by vsimp [hip], by vsimp [hx0], by vsimp [], by vsimp [lastTrue], by simp, rfl, rfl,
    rfl, ?_⟩) le_rfl ?_
  · intro y hy
    simp only [parseT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    vsimp [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2]
  · rintro b ⟨h1, h2, -, -, h5, h6, h7, h8, h9, h10⟩
    refine ⟨by rw [h5, List.take_of_length_le (by omega)], by rw [h1, hfl]; ring, h2, h6, h7, h8, h9, h10⟩

end NearCubicGates.Adapters.ShortPCP.Assembly
