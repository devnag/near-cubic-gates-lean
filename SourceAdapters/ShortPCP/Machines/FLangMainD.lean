import SourceAdapters.ShortPCP.Machines.FLangRdE

/-!
# Single-run time, machine layer 32: the decision half

proof of `thm:short-pcp-ours` (`V0` in time `poly(n, log T)`), proof of `thm:short-pcp-ours` (`V1` accepts iff `V0` accepts on `R ⊕ σ` for every
`σ ∈ S`), proof of `thm:short-pcp-ours` (the proof bits are read at addresses below `L_π`): the `FL` program of stage 4 of
`Time.singleRunTime_of_stages`. On `readWord s L xs (xs.map o) (frame data ++ frame R)` it reads the answer bits
(`rdE`), the data and the coins, parses the instance (`parseP`), builds the tables (`tblP`) and the domain basis
(`domP`), runs one pass per mask (`passD`) and emits `frame [verdict]` (`mainD_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary NearCubicWires.WireExponent3_5
open NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicGates.Adapters.Joins.SingleRun (Request)
open NearCubicGates.Adapters.ACSP.Affine (Instance)

variable {G : Glob}

/-- The domain basis words `19 := packW f [2^0, …, 2^(f−1)]`. -/
def domP : S := genP 23 38 39 19 23 (.set 39 (pw (.v 38)))

/-- The prologue of the decision half. -/
def preD : S :=
  .seq rdE (.seq rdFrame (.seq (.set 10 (.v 0)) (.seq rdFrame (.seq parseP (.seq tblP domP)))))

/-- **The decision half.** -/
def mainD : S :=
  .seq preD (.seq (.set 2 (.k 1)) (.seq (.set 3 (.k 0)) (.seq (.loop 1 (recE 12) passD)
    (.seq (.emit (.k 1)) (.seq (.emit (.v 2)) (.emit (.k 0)))))))

theorem domP_spec (s : FS) (f : ℕ) (h23 : s.env 23 = f) (hK : f * f ≤ G.K) (hN : f ≤ G.N) (hfK : f + 1 ≤ G.K) :
    (evalS G domP s).env 19 = packW f (domW f) ∧ Wr [19, 38, 39] s (evalS G domP s) := by
  have := genP_spec G 23 38 39 19 23 (.set 39 (pw (.v 38))) [39] s f f (fun j => 2 ^ j) (by rw [h23]; omega) h23 hK
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro j hj t w h38
      refine ⟨?_, Nat.pow_lt_pow_right (by norm_num) hj, Wr.setv _ (by simp) _⟩
      simp only [evalS_set, FS.setv_env, Function.update_self]
      exact eE_pow (eE_v 38 |>.trans h38) (by omega))
  exact this

/-- The state after the prologue: the decision context, the coins, the answer bits. -/
theorem preD_spec (q : Request) (hv : q.Valid) (bg : Big G q) (s L : ℕ) (xs : List ℕ) (ans : List Bool) (R : List Bool)
    (hl : ans.length = xs.length) (hinp : G.inp = Time.readWord s L xs ans (q.input R)) (t0 : FS) (hip : t0.ip = s + 1)
    (hR : R.length + 2 ≤ G.K) (hxs : xs.length + 2 ≤ G.K) (hL : L + 2 ≤ G.K) :
    let t := evalS G preD t0
    DCtx G q t ∧ t.env 0 = bitsValue R ∧ t.env 16 = bitsValue ans ∧ t.out = t0.out ∧ t.bad = t0.bad := by
  intro t
  have hNK := bg.N
  have hlin := bg.lin
  have hcK := cap_ge G
  have hD2 : q.data.length * q.data.length ≤ (q.data.length + 1) * (q.data.length + 1) * 1 := by
    simp only [mul_one]; exact Nat.mul_le_mul (by omega) (by omega)
  have hcube := bg.cube (q.data.length + 1) (q.data.length + 1) 1 le_rfl le_rfl (by omega)
  -- the entries
  have hin0 : G.inp.drop t0.ip = entsFrom L xs ans 0 ++ false :: q.input R := by rw [hinp, hip, readWord_drop]
  obtain ⟨e16, ed, ew⟩ := rdE_spec t0 L xs ans (q.input R) hl hin0 hxs hL (by omega) (by omega)
  generalize hu1 : evalS G rdE t0 = u1 at e16 ed ew
  -- the data
  have hcap2 : ∀ n, n + 2 ≤ G.K → 2 * 2 ^ n ≤ G.cap := by
    intro n hn; have := pow_le_cap (G := G) (a := n + 2) hn; rw [pow_succ, pow_succ] at this
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega
  obtain ⟨d0, d1, dip, dw⟩ := rdFrame_spec G u1 q.data (frame R) ed (hcap2 _ (by omega)) (by omega)
  generalize hu2 : evalS G rdFrame u1 = u2 at d0 d1 dip dw
  set u3 := u2.setv 10 (bitsValue q.data) with hu3
  have hd3 : G.inp.drop u3.ip = frame R ++ [] := by
    show G.inp.drop u2.ip = _
    rw [dip, show u1.ip + 2 * q.data.length + 1 = u1.ip + (frame q.data).length by rw [frame_len]; omega,
      ← List.drop_drop, ed, Request.input, List.drop_left, List.append_nil]
  obtain ⟨r0, r1, rip, rw⟩ := rdFrame_spec G u3 R [] hd3 (hcap2 _ hR) (by omega)
  generalize hu4 : evalS G rdFrame u3 = u4 at r0 r1 rip rw
  -- the parse
  obtain ⟨hwf, hf1, hm1, hmt⟩ := valid_pctx q hv
  have pc4 : PCtx G q (u4.env 10) := ⟨by rw [rw.env 10 (by decide)]; simp [u3]; exact At.self q.data, hwf, hf1, hm1, hmt,
    by omega, by omega⟩
  have db := pc4.dbounds
  have hfD := db.f
  obtain ⟨p15, p23, pfl, pfp, pok, pfr, pout, pbad, pip⟩ := parseP_spec G u4 q pc4
  generalize hu5 : evalS G parseP u4 = u5 at p15 p23 pfl pfp pok pfr pout pbad pip
  have hKf : 2 * ((q.code.f + 1) * (8 * q.code.f + 16)) + 1 ≤ G.K := by
    have : (q.code.f + 1) * (8 * q.code.f + 16) ≤ (q.data.length + 1) * (q.data.length + 1) * 8 := by
      have := Nat.mul_le_mul (show q.code.f + 1 ≤ q.data.length + 1 by omega)
        (show 8 * q.code.f + 16 ≤ (q.data.length + 1) * 8 by omega)
      simpa [mul_assoc] using this
    have : (q.data.length + 1) * (q.data.length + 1) * 8 ≤ (q.data.length + 1) * (q.data.length + 1) * 1 * 8 := by
      simp
    omega
  obtain ⟨tb, tw⟩ := tblP_spec G u5 q.code.f p23 hKf (by omega)
  generalize hu6 : evalS G tblP u5 = u6 at tb tw
  have hff : q.code.f * q.code.f ≤ G.K := by
    have := Nat.mul_le_mul (show q.code.f ≤ q.data.length + 1 by omega) (show q.code.f ≤ q.data.length + 1 by omega)
    simp only [mul_one] at hcube; omega
  obtain ⟨o19, ow⟩ := domP_spec u6 q.code.f (by rw [tw.env 23 (by decide), p23]) hff (by omega) (by omega)
  have ht : t = evalS G domP u6 := by
    show evalS G preD t0 = _
    simp only [preD, evalS_seq]
    rw [hu1, hu2, evalS_set, show evalE G u2 (.v 0) = bitsValue q.data from d0, ← hu3, hu4, hu5, hu6]
  rw [ht]
  have w56 : Wr ([19, 38, 39] ++ tblW) u5 (evalS G domP u6) := (tw.mono (by decide)).trans (ow.mono (by decide))
  refine ⟨⟨?_, ?_, o19, ?_, ?_, ?_, pok, valid_irr q hv, ?_, hKf, by omega⟩, ?_, ?_, ?_, ?_⟩
  · rw [w56.env 10 (by decide), pfr 10 (by decide)]; exact pc4
  · rw [w56.env 15 (by decide)]; exact p15
  · rw [w56.env 23 (by decide)]; exact p23
  · rw [w56.fl]; exact pfl
  · rw [w56.fp]; exact pfp
  · exact tb.congr (ow.env 17 (by decide)) (ow.env 18 (by decide))
  · rw [w56.env 0 (by decide), pfr 0 (by decide), r0]
  · rw [w56.env 16 (by decide), pfr 16 (by decide), rw.env 16 (by decide)]; simp [u3]
    rw [dw.env 16 (by decide), e16]
  · rw [w56.out, pout, rw.out]; simp [u3]; rw [dw.out, ew.out]
  · rw [w56.bad, pbad, rw.bad]; simp [u3]; rw [dw.bad, ew.bad]

theorem all_take_succ {α : Type} (l : List α) (g : α → Bool) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).all g = ((l.take j).all g && g l[j]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.all_append]
  simp

/-- **The decision half** (proof of `thm:short-pcp-ours`): on the read word it emits `frame [patched verdict]`. -/
theorem mainD_spec (q : Request) (hv : q.Valid) (bg : Big G q) (s L : ℕ) (R : List Bool) (o : ℕ → Bool)
    (hinp : G.inp = Time.readWord s L (xsOf q R) ((xsOf q R).map o) (q.input R)) (t0 : FS) (hip : t0.ip = s + 1)
    (hR : R.length + 2 ≤ G.K) (hxs : (xsOf q R).length + 2 ≤ G.K) (hL : L + 2 ≤ G.K)
    {F : Type} [Field F] [DecidableEq F] (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F) (hφ : Function.Bijective φ) :
    (evalS G mainD t0).out = t0.out ++ [true, q.patchedVerdict φ (q.decode φ o) R, false] ∧
      (evalS G mainD t0).bad = t0.bad := by
  have hcK := cap_ge G
  have hlin := bg.lin
  have hNK := bg.N
  obtain ⟨c, h0, h16, hout, hbad⟩ := preD_spec q hv bg s L (xsOf q R) ((xsOf q R).map o) R (List.length_map _) hinp t0
    hip hR hxs hL
  generalize hp : evalS G preD t0 = p at c h0 h16 hout hbad
  set W := bitsValue ((xsOf q R).map o) with hW
  have db := c.pc.dbounds
  -- the canonical field of the block list
  have hirr := valid_irr q hv
  letI : Fact (Irreducible (GF.toPoly q.code.irr)) := ⟨hirr⟩
  letI : DecidableEq (AdjoinRoot (GF.toPoly q.code.irr)) := Classical.decEq _
  have hbl : blocks q R = blkAll q (RingHom.id (AdjoinRoot (GF.toPoly q.code.irr))) R := by
    rw [blocks, dif_pos hirr]
  have hlen : (blocks q R).length = q.masks.length * nT q := by rw [hbl, blkAll_length]
  -- the loop
  set p1 := (p.setv 2 1).setv 3 0 with hp1
  have c1 : DCtx G q p1 := (c.setv 2 1).setv 3 0
  let g : List Bool → Bool := fun σ => runVerdictN q φ o (Request.maskedCoins R σ)
  have hm : min (evalE G p1 (recE 12)) G.N = q.masks.length := by
    rw [recE_parse G p1 q c1.pc c1.h15 12 (by norm_num)]; show min q.masks.length G.N = _
    have := db.nm; omega
  have hloop := loop_inv G (i := 1) (n := recE 12) (body := passD) (s := p1)
    (fun j w => DCtx G q w ∧ w.env 0 = bitsValue R ∧ w.env 16 = W ∧ w.env 3 = j * nT q ∧
      w.env 2 = (if (q.masks.take j).all g then 1 else 0) ∧ Wr (1 :: passW) p1 w)
    ⟨c1, by simp [p1, h0], by simp [p1, h16], by simp [p1], by simp [p1], Wr.refl _ _⟩ (by
      rw [hm]
      rintro j hj w ⟨cw, w0, w16, w3, w2, ww⟩
      obtain ⟨a2, a2le, a3, aw⟩ := passD_spec q hv φ hφ (RingHom.id (AdjoinRoot (GF.toPoly q.code.irr))) (w.setv 1 j)
        (cw.setv 1 j) bg o R j W (by simp [w0]) (by omega) (by simp) hj (by simp [w16]) (by simp [w3])
        (by simp [w2]; split_ifs <;> omega) (by
          intro bi hbi
          have hlt : j * nT q + bi < (blocks q R).length := by
            rw [hlen]
            have : (j + 1) * nT q ≤ q.masks.length * nT q := Nat.mul_le_mul_right _ hj
            rw [add_mul, one_mul] at this; omega
          rw [hW, xsOf, block_wordD q o _ _ hlt, hbl, blkAll_getD _ _ _ _ _ hj hbi])
      refine ⟨cw.setv 1 j |>.wr aw, by rw [aw.env 0 (by decide)]; simp [w0],
        by rw [aw.env 16 (by decide)]; simp [w16], a3, ?_, ?_⟩
      · rw [a2]; simp only [FS.setv_env, Function.update_of_ne (by decide : (2 : Var) ≠ 1), w2]
        rw [all_take_succ _ _ _ hj, ite_and_mul]
      · exact (ww.trans (Wr.setv _ (by simp) _)).trans (aw.mono fun x hx => List.mem_cons_of_mem _ hx))
  rw [hm] at hloop
  obtain ⟨-, -, -, -, e2, ew⟩ := hloop
  generalize hw : evalS G (.loop 1 (recE 12) passD) p1 = w at e2 ew
  rw [List.take_length] at e2
  have hpv : q.patchedVerdict φ (q.decode φ o) R = q.masks.all g := by
    unfold Request.patchedVerdict; congr 1; funext σ; exact runVerdict_eq q φ hv hφ o _
  have ht : evalS G mainD t0 = evalS G (.emit (.k 0)) (evalS G (.emit (.v 2)) (evalS G (.emit (.k 1)) w)) := by
    show evalS G (.seq preD _) t0 = _
    simp only [evalS_seq]
    rw [hp, evalS_set, evalS_set, show evalE G p (.k 1) = 1 from min_eq_left (by omega),
      show evalE G (p.setv 2 1) (.k 0) = 0 from Nat.zero_min _, ← hp1, hw]
  rw [ht]
  simp only [evalS_emit]
  refine ⟨?_, ?_⟩
  · have h1c : min 1 G.cap = 1 := min_eq_left (by omega)
    simp only [evalE, ew.out, p1, FS.setv_out, hout, e2, hpv, h1c, Nat.zero_min, List.append_assoc,
      List.singleton_append]
    cases q.masks.all g <;> simp
  · rw [ew.bad]; simp [p1, hbad]

end NearCubicGates.Adapters.ShortPCP.Machines.FL
