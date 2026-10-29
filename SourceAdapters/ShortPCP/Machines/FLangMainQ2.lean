import SourceAdapters.ShortPCP.Machines.FLangMainQ

/-!
# Single-run time, machine layer 35: the query half, assembled

proof of `thm:short-pcp-ours`: the `FL` program of stage 2 of `Time.singleRunTime_of_stages`. On
`prefixWord (frame data ++ frame R)` it emits `frame (readerWord n L xs (frame data ++ frame R))`: the width prefix
`1^n 0`, one entry `1 1 0 0 ++ frame (binary L a)` per address `a ∈ xsOf q R` (`passQ` per mask), `0`, and a copy of
its input after the prefix (`mainQ_spec`). `L = 12·|data| + 40`.
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

/-- The address width `L = 12·|data| + 40`. -/
def addrW (q : Request) : ℕ := 12 * q.data.length + 40

/-- `7 := |π0|`, `16 := |π0| + |π1|`. -/
def lensP : S :=
  .seq (.set 6 (recE 2)) (.seq (.set 7 (lRSE (.v 6))) (.seq (.set 6 (.sub (recE 11) (pw (recE 1))))
    (.set 16 (.add (.add (.v 7) nSE) (lRSE (.v 6))))))

/-- The prologue of the query half (after the prefix). -/
def preQ : S :=
  .seq rdFrame (.seq (.set 10 (.v 0)) (.seq (.set 11 (.v 1)) (.seq rdFrame (.seq parseP (.seq tblP (.seq domP
    (.seq lensP (.set 2 (.add (.mul (.k 12) (.v 11)) (.k 40))))))))))

/-- **The query half.** -/
def mainQ : S :=
  .seq prefE (.seq preQ (.seq (.loop 3 (recE 12) passQ) (.seq (emitF (.k 0)) (.seq (copyE 10 11)
    (.seq (copyE 0 1) (.emit (.k 0)))))))

theorem preQ_spec (q : Request) (hv : q.Valid) (bg : Big G q) (R : List Bool) (t0 : FS)
    (hin : G.inp.drop t0.ip = q.input R) (hR : R.length + 2 ≤ G.K) :
    let t := evalS G preQ t0
    DCtx G q t ∧ t.env 0 = bitsValue R ∧ t.env 1 = R.length ∧ t.env 10 = bitsValue q.data ∧
      t.env 11 = q.data.length ∧ t.env 2 = addrW q ∧ t.env 7 = lenR q ∧ t.env 16 = lenR q + lenH q ∧
      t.out = t0.out ∧ t.bad = t0.bad := by
  intro t
  have hNK := bg.N
  have hlin := bg.lin
  have hcK := cap_ge G
  have hcube := bg.cube (q.data.length + 1) (q.data.length + 1) 1 le_rfl le_rfl (by omega)
  have hD2 : q.data.length * q.data.length ≤ (q.data.length + 1) * (q.data.length + 1) * 1 := by
    simp only [mul_one]; exact Nat.mul_le_mul (by omega) (by omega)
  have hcap2 : ∀ n, n + 2 ≤ G.K → 2 * 2 ^ n ≤ G.cap := by
    intro n hn; have := pow_le_cap (G := G) (a := n + 2) hn; rw [pow_succ, pow_succ] at this
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega
  obtain ⟨d0, d1, dip, dw⟩ := rdFrame_spec G t0 q.data (frame R) hin (hcap2 _ (by omega)) (by omega)
  generalize hu2 : evalS G rdFrame t0 = u2 at d0 d1 dip dw
  set u3 := (u2.setv 10 (bitsValue q.data)).setv 11 q.data.length with hu3
  have hd3 : G.inp.drop u3.ip = frame R ++ [] := by
    show G.inp.drop u2.ip = _
    rw [dip, show t0.ip + 2 * q.data.length + 1 = t0.ip + (frame q.data).length by rw [frame_len]; omega,
      ← List.drop_drop, hin, Request.input, List.drop_left, List.append_nil]
  obtain ⟨r0, r1, rip, rw⟩ := rdFrame_spec G u3 R [] hd3 (hcap2 _ hR) (by omega)
  generalize hu4 : evalS G rdFrame u3 = u4 at r0 r1 rip rw
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
    simp only [mul_one] at hcube; omega
  obtain ⟨tb, tw⟩ := tblP_spec G u5 q.code.f p23 hKf (by omega)
  generalize hu6 : evalS G tblP u5 = u6 at tb tw
  have hff : q.code.f * q.code.f ≤ G.K := by
    have := Nat.mul_le_mul (show q.code.f ≤ q.data.length + 1 by omega) (show q.code.f ≤ q.data.length + 1 by omega)
    simp only [mul_one] at hcube; omega
  obtain ⟨o19, ow⟩ := domP_spec u6 q.code.f (by rw [tw.env 23 (by decide), p23]) hff (by omega) (by omega)
  generalize hu7 : evalS G domP u6 = u7 at o19 ow
  have w57 : Wr ([19, 38, 39] ++ tblW) u5 u7 := (tw.mono (by decide)).trans (ow.mono (by decide))
  have c7 : DCtx G q u7 := ⟨by rw [w57.env 10 (by decide), pfr 10 (by decide)]; exact pc4,
    by rw [w57.env 15 (by decide)]; exact p15, o19, by rw [w57.env 23 (by decide)]; exact p23,
    by rw [w57.fl]; exact pfl, by rw [w57.fp]; exact pfp, pok, valid_irr q hv,
    tb.congr (ow.env 17 (by decide)) (ow.env 18 (by decide)), hKf, by omega⟩
  -- the lengths
  have hel := bg.elems db
  have hel1 : 4 * 2 ^ q.code.f + 2 * lenR q + lenH q + lenI q + 2 ≤ G.cap :=
    le_trans (Nat.le_mul_of_pos_right _ (by omega)) hel
  have hdA := db.dA
  have hmH := db.mH
  have e6a : evalE G u7 (recE 2) = q.dA := recE_parse G u7 q c7.pc c7.h15 2 (by norm_num)
  have c8 : DCtx G q (u7.setv 6 q.dA) := c7.setv 6 _
  have e7 : evalE G (u7.setv 6 q.dA) (lRSE (.v 6)) = lenR q := by
    rw [lRSE_eval c8.h23 c8.atoms (by simp [evalE]) (hb4_of (bg.deg db.f _ hdA))]; unfold lenR outLen; simp
  have c9 : DCtx G q ((u7.setv 6 q.dA).setv 7 (lenR q)) := c8.setv 7 _
  have e6b : evalE G ((u7.setv 6 q.dA).setv 7 (lenR q)) (.sub (recE 11) (pw (recE 1))) = dH q :=
    eE_sub (recE_parse G _ q c9.pc c9.h15 11 (by norm_num))
      (eE_pow (recE_parse G _ q c9.pc c9.h15 1 (by norm_num)) (by show q.code.hBasis.length + 1 ≤ G.K; omega))
  set u10 := ((u7.setv 6 q.dA).setv 7 (lenR q)).setv 6 (dH q) with hu10
  have c10 : DCtx G q u10 := c9.setv 6 _
  have e16 : evalE G u10 (.add (.add (.v 7) nSE) (lRSE (.v 6))) = lenR q + lenH q := by
    have hl := lRSE_eval c10.h23 c10.atoms (show evalE G u10 (.v 6) = dH q by simp [u10, evalE])
      (hb4_of (bg.deg db.f _ (lt_of_le_of_lt (Nat.sub_le _ _) db.dB)))
    rw [eE_add (eE_add (show evalE G u10 (.v 7) = lenR q by simp [u10, evalE]) (nSE_eval G c10.h23 (by omega))
      (by omega)) hl (by simp only [lenH, outLen, if_true] at hel1; omega)]
    simp [lenH, outLen]; ring
  set u11 := u10.setv 16 (lenR q + lenH q) with hu11
  have e2 : evalE G u11 (.add (.mul (.k 12) (.v 11)) (.k 40)) = addrW q := by
    have h11 : u11.env 11 = q.data.length := by
      simp [u11, u10]; rw [w57.env 11 (by decide), pfr 11 (by decide), rw.env 11 (by decide)]; simp [u3]
    rw [eE_add (eE_mul (eE_k (by omega)) (eE_v 11 |>.trans h11) (by omega)) (eE_k (by omega)) (by omega)]; rfl
  have q1 : evalS G (.set 11 (.v 1)) (evalS G (.set 10 (.v 0)) u2) = u3 := by
    rw [evalS_set, evalS_set]; simp [evalE, d0, d1, u3]
  have q2 : evalS G (.set 6 (recE 2)) u7 = u7.setv 6 q.dA := by rw [evalS_set, e6a]
  have q3 : evalS G (.set 7 (lRSE (.v 6))) (u7.setv 6 q.dA) = (u7.setv 6 q.dA).setv 7 (lenR q) := by rw [evalS_set, e7]
  have q4 : evalS G (.set 6 (.sub (recE 11) (pw (recE 1)))) ((u7.setv 6 q.dA).setv 7 (lenR q)) = u10 := by
    rw [evalS_set, e6b]
  have q5 : evalS G (.set 16 (.add (.add (.v 7) nSE) (lRSE (.v 6)))) u10 = u11 := by rw [evalS_set, e16]
  have q6 : evalS G (.set 2 (.add (.mul (.k 12) (.v 11)) (.k 40))) u11 = u11.setv 2 (addrW q) := by rw [evalS_set, e2]
  have ht : t = u11.setv 2 (addrW q) := by
    show evalS G preQ t0 = _
    simp only [preQ, lensP, evalS_seq]
    rw [hu2, q1, hu4, hu5, hu6, hu7, q2, q3, q4, q5, q6]
  rw [ht]
  have w7 : ∀ j, j ∉ ([19, 38, 39] ++ tblW) → j ∉ parseW → j ∉ ([0, 1, 2, 3, 4] : List Var) → u7.env j = u3.env j :=
    fun j h1 h2 h3 => by rw [w57.env j h1, pfr j h2, rw.env j h3]
  refine ⟨((c10.setv 16 _).setv 2 _), ?_, ?_, ?_, ?_, by simp, by simp [u11, u10], by simp [u11], ?_, ?_⟩
  · simp [u11, u10]; rw [w57.env 0 (by decide), pfr 0 (by decide), r0]
  · simp [u11, u10]; rw [w57.env 1 (by decide), pfr 1 (by decide), r1]
  · simp [u11, u10]; rw [w7 10 (by decide) (by decide) (by decide)]; simp [u3]
  · simp [u11, u10]; rw [w7 11 (by decide) (by decide) (by decide)]; simp [u3]
  · simp [u11, u10]; rw [w57.out, pout, rw.out]; simp [u3]; rw [dw.out]
  · simp [u11, u10]; rw [w57.bad, pbad, rw.bad]; simp [u3]; rw [dw.bad]

theorem range_flatMap_getD {α : Type} (g : α → List Bool) (d : α) :
    ∀ l : List α, (List.range l.length).flatMap (fun i => g (l.getD i d)) = l.flatMap g
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.flatMap_cons]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [range_flatMap_getD g d l]

theorem xs_entries {F : Type} [Field F] [DecidableEq F] (q : Request) (φ0 : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (R : List Bool) (L : ℕ) (hb : blocks q R = blkAll q φ0 R) :
    (xsOf q R).flatMap (entryW L) =
      (List.range q.masks.length).flatMap (fun i =>
        (blkS q φ0 (Request.maskedCoins R (q.masks.getD i []))).flatMap (elemW L q.code.f)) := by
  rw [range_flatMap_getD (fun σ => (blkS q φ0 (Request.maskedCoins R σ)).flatMap (elemW L q.code.f)) [] q.masks]
  unfold xsOf blockAddrs
  rw [hb, blkAll, List.flatMap_assoc, List.flatMap_assoc]
  congr 1; funext σ
  congr 1; funext k
  rw [List.flatMap_map]; rfl

/-- **The query half** (proof of `thm:short-pcp-ours`): on `prefixWord (q.input R)` it emits
`frame (readerWord n L (xsOf q R) (q.input R))`. -/
theorem mainQ_spec (q : Request) (hv : q.Valid) (bg : Big G q) (R : List Bool) (n : ℕ)
    (hinp : G.inp = Time.prefixWord (q.input R)) (hn : n = Nat.size (q.input R).length) (hK : G.K = 2 * 64 ^ n)
    (t0 : FS) (hip : t0.ip = n + 1) (hR : R.length + 2 ≤ G.K) (hNn : n ≤ G.N) (hnc : n + 2 ≤ G.cap) :
    (evalS G mainQ t0).out = t0.out ++ frame (Time.readerWord n (addrW q) (xsOf q R) (q.input R)) ∧
      (evalS G mainQ t0).bad = t0.bad := by
  have hNK := bg.N
  have hlin := bg.lin
  have hcK := cap_ge G
  have h64 : 64 ≤ G.cap := by omega
  have e1 := prefE_spec (G := G) t0 n hK hNn hnc h64
  generalize hu1 : evalS G prefE t0 = u1 at e1
  have hin : G.inp.drop u1.ip = q.input R := by
    rw [e1.ip, hip, hinp, Time.prefixWord, ← hn]
    rw [show n + 1 = (List.replicate n true).length + 1 by simp, List.drop_append]; simp
  obtain ⟨c2, g0, g1, g10, g11, g2, g7, g16, gout, gbad⟩ := preQ_spec q hv bg R u1 hin hR
  generalize hu2 : evalS G preQ u1 = u2 at c2 g0 g1 g10 g11 g2 g7 g16 gout gbad
  have db := c2.pc.dbounds
  -- the canonical field
  have hirr := valid_irr q hv
  letI : Fact (Irreducible (GF.toPoly q.code.irr)) := ⟨hirr⟩
  letI : DecidableEq (AdjoinRoot (GF.toPoly q.code.irr)) := Classical.decEq _
  haveI := charP_two q (RingHom.id (AdjoinRoot (GF.toPoly q.code.irr)))
  have hbl : blocks q R = blkAll q (RingHom.id (AdjoinRoot (GF.toPoly q.code.irr))) R := by rw [blocks, dif_pos hirr]
  have hm : min (evalE G u2 (recE 12)) G.N = q.masks.length := by
    rw [recE_parse G u2 q c2.pc c2.h15 12 (by norm_num)]; show min q.masks.length G.N = _
    have := db.nm; omega
  have hL : addrW q ≤ G.N := by unfold addrW; omega
  have e3 := (Em_loop 3 (recE 12) passQ (3 :: passQW) (by simp) u2 q.masks.length hm (fun _ => True) trivial
    (fun i => (blkS q (RingHom.id (AdjoinRoot (GF.toPoly q.code.irr))) (Request.maskedCoins R (q.masks.getD i []))).flatMap
      (elemW (addrW q) q.code.f)) (by
      intro j hj t _ te
      refine ⟨trivial, ?_⟩
      have ct : DCtx G q (t.setv 3 j) := (c2.em te).setv 3 j
      have hk : ∀ x : Var, x ∉ 3 :: passQW → (t.setv 3 j).env x = u2.env x := fun x hx => by
        simp only [FS.setv_env]; rw [Function.update_of_ne (fun h => hx (by simp [h]))]; exact te.env x hx
      have := passQ_spec (G := G) q hv (RingHom.id (AdjoinRoot (GF.toPoly q.code.irr))) (t.setv 3 j) ct bg R j
        (addrW q) ((hk 0 (by decide)).trans g0) (by omega) (by simp) hj ((hk 2 (by decide)).trans g2) hL
        ((hk 7 (by decide)).trans g7) ((hk 16 (by decide)).trans g16)
      rw [List.getD_eq_getElem _ _ hj]
      exact this.mono fun _ hx => List.mem_cons_of_mem _ hx)).2
  generalize hu3 : evalS G (.loop 3 (recE 12) passQ) u2 = u3 at e3
  have e4 := emitF_spec (G := G) u3 (.k 0) (3 :: passQW) (by omega)
  generalize hu4 : evalS G (emitF (.k 0)) u3 = u4 at e4
  have e5 := copyE_spec (G := G) u4 10 11 q.data (by rw [e4.env 10 (by decide), e3.env 10 (by decide), g10])
    (by rw [e4.env 11 (by decide), e3.env 11 (by decide), g11]) (by decide) (by omega) (by omega)
  generalize hu5 : evalS G (copyE 10 11) u4 = u5 at e5
  have e6 := copyE_spec (G := G) u5 0 1 R (by rw [e5.env 0 (by decide), e4.env 0 (by decide), e3.env 0 (by decide), g0])
    (by rw [e5.env 1 (by decide), e4.env 1 (by decide), e3.env 1 (by decide), g1]) (by decide) (by omega) (by omega)
  generalize hu6 : evalS G (copyE 0 1) u5 = u6 at e6
  have ht : evalS G mainQ t0 = evalS G (.emit (.k 0)) u6 := by
    show evalS G (.seq _ _) t0 = _
    simp only [evalS_seq]; rw [hu1, hu2, hu3, hu4, hu5, hu6]
  rw [ht]
  simp only [evalS_emit]
  refine ⟨?_, by rw [e6.bad, e5.bad, e4.bad, e3.bad, gbad, e1.bad]⟩
  rw [e6.out, e5.out, e4.out, e3.out, gout, e1.out, show evalE G u6 (.k 0) = 0 from Nat.zero_min _,
    show evalE G u3 (.k 0) = 0 from Nat.zero_min _,
    frame_dbl (Time.readerWord n (addrW q) (xsOf q R) (q.input R)), Time.readerWord, Request.input,
    ← xs_entries q _ R (addrW q) hbl]
  have dc : ∀ (b : Bool) (w : List Bool), dbl (b :: w) = true :: b :: dbl w := fun b w => rfl
  simp only [dbl_append, dc, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
  rfl

end NearCubicGates.Adapters.ShortPCP.Machines.FL
