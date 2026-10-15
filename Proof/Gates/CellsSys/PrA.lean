import Proof.Gates.CellsSys.SplitSpec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

instance : DecidablePred FragVar := fun x => by unfold FragVar; infer_instance

/-- The printer's state. -/
structure PS (e : DS VV MM) (W Rk : List Bool) (Ra : List ℕ) (b : DS VV MM) : Prop where
  ram : b.ram = e.ram
  ip : b.ip = e.ip
  out : b.out = e.out
  rc : RcOK b
  kin : b.kin ++ Rk = W
  sA : (b.ram sA).drop (b.rc sA) = Ra
  cst : Cst b
  fr : ∀ x : Fin VV, ¬ FragVar x → b.env x = e.env x

theorem fragT_ok {T : List (Fin VV)} (hT : ∀ x ∈ T, FragVar x) : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T :=
  ⟨fun h => by have := hT _ h; revert this; decide, fun h => by have := hT _ h; revert this; decide,
   fun h => by have := hT _ h; revert this; decide⟩

theorem PS.step {e b b' : DS VV MM} {W Rk : List Bool} {Ra : List ℕ} (h : PS e W Rk Ra b) (hs : Same b b')
    {T : List (Fin VV)} (hf : Fr b b' T) (hT : ∀ x ∈ T, FragVar x) : PS e W Rk Ra b' :=
  ⟨hs.ram.trans h.ram, hs.ip.trans h.ip, hs.out.trans h.out, RcOK.same h.rc hs, by rw [hs.kin]; exact h.kin,
    by rw [hs.ram, hs.rc]; exact h.sA, cst_of h.cst hf (fragT_ok hT),
    fun x hx => (hf x (fun hm => hx (hT x hm))).trans (h.fr x hx)⟩

theorem PS.set {e b : DS VV MM} {W Rk : List Bool} {Ra : List ℕ} (h : PS e W Rk Ra b) {x : Fin VV}
    (hx : FragVar x) (v : ℕ) : PS e W Rk Ra (b.set x v) :=
  h.step (Same.set b x v) (Fr.set b v (List.mem_singleton_self x)) (fun z hz => by
    rw [List.mem_singleton] at hz; rw [hz]; exact hx)

/-- One `natWord` of `t3` printed to the call input. -/
theorem ps_emit {e b : DS VV MM} {W R : List Bool} {Ra : List ℕ} (v Bw : ℕ) (h : PS e W (natWord v ++ R) Ra b)
    (hv : b.env t3 = v) (hb : natBitLength v ≤ Bw) (hBw : Bw + 2 < 2 ^ C.Wd) (hW2 : 2 ≤ C.Wd)
    (hL : W.length ≤ C.Lk) :
    Hs C emitNatK b (40 * Bw + 40) (fun b' => PS e W R Ra b' ∧ Fr b b' emitNatT) := by
  have hk : b.kin.length + (natWord (b.env t3)).length ≤ C.Lk := by
    rw [hv]; have := congrArg List.length h.kin; simp only [List.length_append] at this; omega
  refine Hs.mono (emitNatK_spec b h.cst hW2 (by rw [hv]; omega) hk) (by rw [hv]; omega) ?_
  rintro b' ⟨k1, k2, k3, k4⟩
  simp only [Prod.mk.injEq] at k2
  obtain ⟨e1, e2, e3, e4, -, -⟩ := k2
  refine ⟨⟨e3.trans h.ram, e1.trans h.ip, e2.trans h.out, fun m => by rw [e4, e3]; exact h.rc m,
    by rw [k1, hv, List.append_assoc]; exact h.kin, by rw [e3, e4]; exact h.sA, k3,
    fun x hx => (k4 x (fun hm => hx (by revert hm; revert x; decide))).trans (h.fr x hx)⟩, k4⟩

theorem ps_rdA {e b : DS VV MM} {W Rk : List Bool} {v : ℕ} {Ra : List ℕ} (h : PS e W Rk (v :: Ra) b) (x : Fin VV)
    (hx : FragVar x) :
    Hs C (.op (.rdM sA x)) b 1 (fun b' => b'.env x = v ∧ PS e W Rk Ra b' ∧ Fr b b' [x]) := by
  have hd := h.sA
  have hlt : b.rc sA < (b.ram sA).length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at hd; exact List.cons_ne_nil _ _ hd.symm
  have hget : (b.ram sA).getD (b.rc sA) 0 = v := by
    rw [List.getD_eq_getElem _ _ hlt]
    have := congrArg (fun l => l.head?) hd
    simp only [List.head?_drop, List.head?_cons] at this
    rw [List.getElem?_eq_getElem hlt] at this
    exact Option.some.inj this
  refine Hs.mono (hs_rdM C sA x b hlt) le_rfl ?_
  rintro b' rfl
  have hfr : Fr b ((b.set x ((b.ram sA).getD (b.rc sA) 0)).adv sA) [x] := Fr.set b _ (List.mem_singleton_self x)
  refine ⟨by simp only [DS.adv, DS.set_env_self]; exact hget, ⟨h.ram, h.ip, h.out, fun m => ?_, h.kin, ?_, ?_, ?_⟩, hfr⟩
  · by_cases hm : m = sA
    · subst hm; simp [DS.adv, DS.set]; omega
    · simp only [DS.adv, DS.set]; rw [Function.update_of_ne hm]; exact h.rc m
  · simp only [DS.adv, DS.set, Function.update_self]
    rw [← List.drop_drop, hd]; rfl
  · exact cst_of h.cst hfr (fragT_ok (fun z hz => by rw [List.mem_singleton] at hz; rw [hz]; exact hx))
  · intro z hz
    have : z ≠ x := fun e => hz (e ▸ hx)
    simp only [DS.adv, DS.set]; rw [Function.update_of_ne this]; exact h.fr z hz

/-- A record of `sN` by index (into a `FragVar` variable `d`; the index variable is not `c0`, `vJ`). -/
theorem ps_fetchN {e b : DS VV MM} {W Rk : List Bool} {Ra : List ℕ} (h : PS e W Rk Ra b) (x d : Fin VV)
    (hx0 : x ≠ c0) (hxJ : x ≠ vJ) (hd : FragVar d) (hlt : b.env x < (b.ram sN).length) (hW : b.env x < 2 ^ C.Wd) :
    Hs C (fetch sN x d) b (b.rc sN + 5 * b.env x + 9) (fun b' => b'.env d = (b.ram sN).getD (b.env x) 0 ∧
      PS e W Rk Ra b' ∧ Fr b b' [c0, vJ, d]) := by
  refine Hs.mono (o_fetch sN x d hx0 hxJ (by decide) b hlt hW) le_rfl ?_
  rintro b' ⟨f1, f2, f3, f4⟩
  refine ⟨f1, ⟨f3.ram.trans h.ram, f3.ip.trans h.ip, f3.out.trans h.out, RcOK.fetch h.rc f3 f4 hlt,
    by rw [f3.kin]; exact h.kin, by rw [f3.ram, f3.rcA]; exact h.sA,
    cst_of h.cst f2 (fragT_ok (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · decide
      · decide
      · exact hd)), fun z hz => (f2 z (fun hm => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl
        · exact hz (by decide)
        · exact hz (by decide)
        · exact hz hd)).trans (h.fr z hz)⟩, f2⟩

/-! ## `intWord` of a pair difference -/

/-- Print `intWord (X − Y)` for `X` in `xv`, `Y` in `yv`. -/
def prIntP (xv yv : Fin VV) : St VV MM :=
  .ite (.lt xv yv)
    (.seq (.op (.copy t3 v1)) (.seq emitNatK (.seq (.op (.copy t3 yv)) (.seq (.op (.sub t3 xv)) emitNatK))))
    (.seq (.op (.copy t3 vZ)) (.seq emitNatK (.seq (.op (.copy t3 xv)) (.seq (.op (.sub t3 yv)) emitNatK))))

def prIntT : List (Fin VV) := [t3, t5, t6, t7, t8, t9]

theorem prIntT_frag : ∀ x ∈ prIntT, FragVar x := by decide

theorem nbl_small (v : ℕ) (hv : v ≤ 1) (Bw : ℕ) (hB : 1 ≤ Bw) : natBitLength v ≤ Bw := by
  have : natBitLength v ≤ 1 := by
    unfold natBitLength; rcases Nat.lt_or_ge v 1 with h | h
    · interval_cases v; simp
    · have : v = 1 := by omega
      subst this; simp
  omega

theorem ps_prInt {e b : DS VV MM} {W R : List Bool} {Ra : List ℕ} (xv yv : Fin VV) (hxv : xv ∉ prIntT)
    (hyv : yv ∉ prIntT) (hxy : xv ≠ yv) (X Y Bw : ℕ) (h : PS e W (Interfaces.intWord (zOf X Y) ++ R) Ra b)
    (hX : b.env xv = X) (hY : b.env yv = Y) (hb : natBitLength (zOf X Y).natAbs ≤ Bw) (hB1 : 1 ≤ Bw)
    (hBw : Bw + 2 < 2 ^ C.Wd) (hW2 : 2 ≤ C.Wd) (hL : W.length ≤ C.Lk) :
    Hs C (prIntP xv yv) b (2 * (40 * Bw + 40) + 8) (fun b' => PS e W R Ra b' ∧ Fr b b' prIntT) := by
  have htx : t3 ≠ xv := fun h => hxv (by rw [← h]; decide)
  have hty : t3 ≠ yv := fun h => hyv (by rw [← h]; decide)
  have hvx : ∀ (d : DS VV MM), Fr b d prIntT → d.env xv = X := fun d hd => by rw [hd xv hxv]; exact hX
  have hvy : ∀ (d : DS VV MM), Fr b d prIntT → d.env yv = Y := fun d hd => by rw [hd yv hyv]; exact hY
  refine Hs.ite (show xv ≠ yv from hxy) (fun he => ?_) (fun he => ?_)
  · have hlt : X < Y := by simpa [Cnd.eval, hX, hY] using he
    have hz : Interfaces.intWord (zOf X Y) = natWord 1 ++ natWord (Y - X) := by
      unfold Interfaces.intWord zOf; rw [if_pos (by omega)]; congr 2; omega
    rw [hz, List.append_assoc] at h
    refine Hx.hs (Hs.then (o_copy t3 v1 b (by decide)) (fun b1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
    have h1 : PS e W (natWord 1 ++ (natWord (Y - X) ++ R)) Ra b1 := h.step p3 p2 (by decide)
    rw [h.cst.one] at p1
    refine Hs.then (ps_emit 1 Bw h1 p1 (nbl_small 1 le_rfl Bw hB1) hBw hW2 hL) (fun b2 ⟨q1, q2⟩ k2 hk2 => ?_)
    refine Hs.then (o_copy t3 yv b2 hty) (fun b3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
    have F3 : Fr b b3 prIntT := Fr.trans (p2.weaken (by decide)) (Fr.trans (q2.weaken (by decide))
      (r2.weaken (by decide)))
    rw [show b2.env yv = Y from (hvy b2 (Fr.trans (p2.weaken (by decide)) (q2.weaken (by decide))))] at r1
    refine Hs.then (o_sub t3 xv b3 htx (by rw [r1, hvx b3 F3]; omega)) (fun b4 ⟨s1, s2, s3⟩ k4 hk4 => ?_)
    rw [r1, hvx b3 F3] at s1
    refine Hs.last (ps_emit (Y - X) Bw ((q1.step r3 r2 (by decide)).step s3 s2 (by decide)) s1
      (by have : (zOf X Y).natAbs = Y - X := by unfold zOf; omega
          rw [← this]; exact hb) hBw hW2 hL) (fun b5 ⟨u1, u2⟩ k5 hk5 => ⟨⟨u1, ?_⟩, by omega⟩)
    exact Fr.trans F3 (Fr.trans (s2.weaken (by decide)) (u2.weaken (by decide)))
  · have hle : ¬ X < Y := by simpa [Cnd.eval, hX, hY] using he
    have hz : Interfaces.intWord (zOf X Y) = natWord 0 ++ natWord (X - Y) := by
      unfold Interfaces.intWord zOf; rw [if_neg (by omega)]; congr 2; omega
    rw [hz, List.append_assoc] at h
    refine Hx.hs (Hs.then (o_copy t3 vZ b (by decide)) (fun b1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
    have h1 : PS e W (natWord 0 ++ (natWord (X - Y) ++ R)) Ra b1 := h.step p3 p2 (by decide)
    rw [h.cst.z] at p1
    refine Hs.then (ps_emit 0 Bw h1 p1 (nbl_small 0 (by norm_num) Bw hB1) hBw hW2 hL) (fun b2 ⟨q1, q2⟩ k2 hk2 => ?_)
    refine Hs.then (o_copy t3 xv b2 htx) (fun b3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
    have F3 : Fr b b3 prIntT := Fr.trans (p2.weaken (by decide)) (Fr.trans (q2.weaken (by decide))
      (r2.weaken (by decide)))
    rw [show b2.env xv = X from (hvx b2 (Fr.trans (p2.weaken (by decide)) (q2.weaken (by decide))))] at r1
    refine Hs.then (o_sub t3 yv b3 hty (by rw [r1, hvy b3 F3]; omega)) (fun b4 ⟨s1, s2, s3⟩ k4 hk4 => ?_)
    rw [r1, hvy b3 F3] at s1
    refine Hs.last (ps_emit (X - Y) Bw ((q1.step r3 r2 (by decide)).step s3 s2 (by decide)) s1
      (by have : (zOf X Y).natAbs = X - Y := by unfold zOf; omega
          rw [← this]; exact hb) hBw hW2 hL) (fun b5 ⟨u1, u2⟩ k5 hk5 => ⟨⟨u1, ?_⟩, by omega⟩)
    exact Fr.trans F3 (Fr.trans (s2.weaken (by decide)) (u2.weaken (by decide)))

end NearCubicGates.Close.Cells.SystemsPhase
