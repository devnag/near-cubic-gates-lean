import SourceAdapters.Compile.CNFClause

/-!
# Token interpreter, part A: cursor seeks and the index stack

The interpreter of `CNFRpn.RS.step` keeps the index stack in store `sSK` (bottom first) with its height in `iSp`:
`StkRel a st` says `take |st| (ram sSK) = st.reverse`. `pushP`/`popP` implement `x :: st` and `popS st`
(`pushP_spec`, `popP_spec`); `seekP` moves a cursor to a position held in a register.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def iIdx : Fin VV := ⟨60, by decide⟩
def iSp : Fin VV := ⟨61, by decide⟩
def iWl : Fin VV := ⟨62, by decide⟩
def iNc : Fin VV := ⟨63, by decide⟩
def iTk : Fin VV := ⟨64, by decide⟩
def iPl : Fin VV := ⟨65, by decide⟩
def iK : Fin VV := ⟨66, by decide⟩
def iX : Fin VV := ⟨67, by decide⟩
def iY : Fin VV := ⟨68, by decide⟩
def iG : Fin VV := ⟨69, by decide⟩
def iS : Fin VV := ⟨70, by decide⟩
def iJ : Fin VV := ⟨71, by decide⟩

variable {C : Ctx}

/-- Move the cursor of `m` to `env p` (counter `iS`, junk `iJ`). -/
def seekP (m : Fin MM) (p : Fin VV) : St VV MM :=
  .seq (.op (.rwM m)) (.seq (.op (.zero iS)) (.loop (.lt iS p) (.seq (.op (.rdM m iJ)) (.op (.inc iS)))))

theorem seekP_spec (m : Fin MM) (p : Fin VV) (hp : p ∉ [iS, iJ]) (a : DS VV MM)
    (hle : a.env p ≤ (a.ram m).length) (hW : a.env p + 1 < 2 ^ C.Wd) :
    Hs C (seekP m p) a (a.rc m + 5 * a.env p + 6) (fun b => b.rc m = a.env p ∧ b.ram = a.ram ∧
      (∀ m', m' ≠ m → b.rc m' = a.rc m') ∧ b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [iS, iJ]) := by
  have hp' : p ≠ iS ∧ p ≠ iJ := by simpa using hp
  set P := a.env p with hP
  let I : ℕ → DS VV MM → Prop := fun k b => b.env iS = k ∧ b.rc m = k ∧ b.ram = a.ram ∧
    (∀ m', m' ≠ m → b.rc m' = a.rc m') ∧ b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [iS, iJ]
  have hloop := Hs.loopN (C := C) (c := .lt iS p) (s := .seq (.op (.rdM m iJ)) (.op (.inc iS)))
    (show iS ≠ p from fun h => hp'.1 h.symm) I P 3
    (fun k hk b hb => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hb
      have hpb : b.env p = P := by rw [h7 p hp]
      refine ⟨by simp [Cnd.eval, h1, hpb, hk], ?_⟩
      refine Hs.seqc (t1 := 1) (t2 := 1) (hs_rdM C m iJ b (by rw [h2, h3]; omega)) (fun d hd => ?_) (by omega)
      subst hd
      have g1 : ((b.set iJ ((b.ram m).getD (b.rc m) 0)).adv m).env iS = k := by
        simp [DS.adv, DS.set, Function.update_of_ne (show iS ≠ iJ by decide), h1]
      refine Hs.op (OpEx.inc iS _ (by rw [g1]; omega)) ⟨by rw [DS.set_env_self, g1], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [DS.adv, h2]
      · simp [DS.adv, h3]
      · intro m' hm'
        simp [DS.adv, Function.update_of_ne hm', h4 m' hm']
      · simp [DS.adv, h5]
      · simp [DS.adv, h6]
      · intro y hy
        have hy' : y ≠ iS ∧ y ≠ iJ := by simpa using hy
        simp [DS.adv, DS.set, Function.update_apply, hy'.1, hy'.2, h7 y hy])
    (fun b hb => by
      obtain ⟨h1, _, _, _, _, _, h7⟩ := hb
      have hpb : b.env p = P := by rw [h7 p hp]
      simp [Cnd.eval, h1, hpb])
  refine Hs.seqc (t1 := a.rc m + 1) (t2 := 5 * P + 4) (hs_rwM C m a) (fun b hb => ?_) (by omega)
  subst hb
  refine Hs.seqc (t1 := 1) (t2 := P * (3 + 2) + 2) (hs_zero C iS _) (fun b hb => ?_) (by omega)
  subst hb
  refine Hs.mono (hloop _ ⟨by simp, by simp [DS.rew], by simp [DS.rew], fun m' hm' => by
    simp [DS.rew, Function.update_of_ne hm'], by simp [DS.rew], by simp [DS.rew], fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [DS.set, DS.rew, Function.update_apply, hy]⟩) le_rfl ?_
  rintro b ⟨_, h2, h3, h4, h5, h6, h7⟩
  exact ⟨h2, h3, h4, h5, h6, h7⟩

/-! ## The index stack -/

/-- The stack `st` (top first) is stored bottom first in `sSK`, height in `iSp`. -/
structure StkRel (a : DS VV MM) (st : List ℕ) : Prop where
  sp : a.env iSp = st.length
  take : (a.ram sSK).take st.length = st.reverse
  len : st.length ≤ (a.ram sSK).length

theorem take_putAt (l : List ℕ) (n x : ℕ) (h : n ≤ l.length) : (putAt l n x).take (n + 1) = l.take n ++ [x] := by
  unfold putAt
  split_ifs with h1
  · rw [List.take_add_one, List.getElem?_set_self (by omega)]
    simp [List.take_set_of_le]
  · have : n = l.length := by omega
    subst this; simp

theorem take_putAt_le (l : List ℕ) (n x k : ℕ) (h : n ≤ l.length) (hk : k ≤ n) :
    (putAt l n x).take k = l.take k := by
  unfold putAt
  split_ifs with h1
  · exact List.take_set_of_le hk
  · rw [List.take_append_of_le_length (by omega)]

/-- Push `env x` (seek `sSK` to the height, write, increment). -/
def pushP (x : Fin VV) : St VV MM := .seq (seekP sSK iSp) (.seq (.op (.wrM sSK x)) (.op (.inc iSp)))

theorem pushP_spec (x : Fin VV) (hx : x ∉ [iS, iJ, iSp]) (a : DS VV MM) (st : List ℕ) (h : StkRel a st)
    (hW : st.length + 2 < 2 ^ C.Wd) :
    Hs C (pushP x) a (a.rc sSK + 5 * st.length + 10) (fun b => StkRel b (a.env x :: st) ∧
      (b.ram sSK).length ≤ max (a.ram sSK).length (st.length + 1) ∧ b.rc sSK = st.length + 1 ∧
      (∀ m, m ≠ sSK → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b [iS, iJ, iSp]) := by
  have hx' : x ≠ iS ∧ x ≠ iJ ∧ x ≠ iSp := by simpa using hx
  refine Hs.seqc (t1 := a.rc sSK + 5 * st.length + 6) (t2 := 3) (Hs.mono (seekP_spec (C := C) sSK iSp
    (by decide) a (by rw [h.sp]; exact h.len) (by rw [h.sp]; omega)) (by rw [h.sp]) (fun b hb => hb))
    (fun b hb => ?_) (by omega)
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  rw [h.sp] at b1
  refine Hs.seqc (t1 := 1) (t2 := 1) (hs_wrM C sSK x b (by rw [b1, b2]; exact h.len)) (fun d hd => ?_) (by omega)
  subst hd
  have hsp : (b.put sSK (b.env x)).env iSp = st.length := by
    simp only [DS.put]; rw [b6 iSp (by decide), h.sp]
  refine Hs.op (OpEx.inc iSp _ (by rw [hsp]; omega)) ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [DS.set_env_self, hsp]; simp
  · simp only [DS.set_ram, DS.put, Function.update_self, List.length_cons]
    rw [b1, b2, take_putAt _ _ _ h.len, h.take, b6 x (by simp [hx'.1, hx'.2.1])]; simp
  · simp only [DS.set_ram, DS.put, Function.update_self, List.length_cons]
    rw [b1, b2, putAt_length _ _ _ h.len]; omega
  · simp only [DS.set_ram, DS.put, Function.update_self]
    rw [b1, b2, putAt_length _ _ _ h.len]
  · simp [DS.put, b1]
  · intro m hm
    simp only [DS.set_ram, DS.set_rc, DS.put, Function.update_of_ne hm]
    exact ⟨by rw [b2], b3 m hm⟩
  · simp [DS.put, b4]
  · simp [DS.put, b5]
  · intro y hy
    have hy' : y ≠ iS ∧ y ≠ iJ ∧ y ≠ iSp := by simpa using hy
    simp only [DS.set, DS.put]
    rw [Function.update_of_ne hy'.2.2]
    exact b6 y (by simp [hy'.1, hy'.2.1])

/-- Pop into `x` (`0` on the empty stack). -/
def popP (x : Fin VV) : St VV MM :=
  .ite (.eq iSp vZ) (.op (.zero x)) (.seq (.op (.sub iSp v1)) (.seq (seekP sSK iSp) (.op (.rdM sSK x))))

theorem popP_spec (x : Fin VV) (hx : x ∉ [iS, iJ, iSp]) (a : DS VV MM) (st : List ℕ) (h : StkRel a st)
    (hz : a.env vZ = 0) (h1 : a.env v1 = 1) (hW : st.length + 2 < 2 ^ C.Wd) :
    Hs C (popP x) a (a.rc sSK + 5 * st.length + 10) (fun b => b.env x = (popS st).1 ∧ StkRel b (popS st).2 ∧
      b.ram = a.ram ∧ b.rc sSK ≤ max (a.rc sSK) st.length ∧ (∀ m, m ≠ sSK → b.rc m = a.rc m) ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Fr a b [iS, iJ, iSp, x]) := by
  have hx' : x ≠ iS ∧ x ≠ iJ ∧ x ≠ iSp := by simpa using hx
  refine Hs.ite (show iSp ≠ vZ by decide) (fun hc => ?_) (fun hc => ?_)
  · have he : st = [] := by
      have : a.env iSp = 0 := by simpa [Cnd.eval, hz] using hc
      rw [h.sp] at this; exact List.eq_nil_of_length_eq_zero this
    subst he
    refine Hs.mono (hs_zero C x a) (by omega) ?_
    rintro b rfl
    refine ⟨by simp [popS], ⟨?_, by simp [popS], by simp [popS]⟩, rfl, by simp, fun _ _ => rfl, rfl, rfl, by fr_tac⟩
    rw [DS.set_env_ne _ _ (Ne.symm hx'.2.2), h.sp]; rfl
  · obtain ⟨top, rest, rfl⟩ : ∃ top rest, st = top :: rest := by
      cases st with
      | nil => simp [Cnd.eval, h.sp, hz] at hc
      | cons t r => exact ⟨t, r, rfl⟩
    have hsp := h.sp
    simp only [List.length_cons] at hsp
    have htake := h.take
    simp only [List.length_cons, List.reverse_cons] at htake
    have hlen := h.len
    simp only [List.length_cons] at hlen hW
    refine Hs.seqc (t1 := 1) (t2 := a.rc sSK + 5 * rest.length + 8) (hs_sub C iSp v1 a (by decide)
      (by rw [hsp, h1]; omega)) (fun b hb => ?_) (by simp only [List.length_cons]; omega)
    subst hb
    have bsp : (a.set iSp (a.env iSp - a.env v1)).env iSp = rest.length := by
      rw [DS.set_env_self, hsp, h1]; simp
    refine Hs.seqc (t1 := a.rc sSK + 5 * rest.length + 6) (t2 := 1) (Hs.mono (seekP_spec (C := C) sSK iSp
      (by decide) _ (by rw [bsp]; simp; omega) (by rw [bsp]; omega)) (by rw [bsp]; simp) (fun b hb => hb))
      (fun d hd => ?_) (by omega)
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
    rw [bsp] at d1
    simp only [DS.set_ram] at d2
    have hget : (a.ram sSK)[rest.length]?.getD 0 = top := by
      have e := congrArg (fun l : List ℕ => l[rest.length]?) htake
      simp at e
      simp [e]
    refine Hs.op (OpEx.rdM sSK x d (by rw [d1, d2]; omega)) ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [DS.adv, popS, d1, d2, hget]
    · simp only [DS.adv, popS]
      rw [DS.set_env_ne _ _ (Ne.symm hx'.2.2), d6 iSp (by decide), bsp]
    · simp only [DS.adv, DS.set_ram, popS, d2]
      have := congrArg (fun l => l.take rest.length) htake
      simp only [List.take_take] at this
      rw [Nat.min_eq_left (by omega)] at this
      rw [this, List.take_left' (by simp)]
    · simp only [DS.adv, DS.set_ram, popS, d2]; omega
    · simp [DS.adv, DS.set, d2]
    · simp [DS.adv, d1]
    · intro m hm
      simp only [DS.adv, DS.set_rc, Function.update_of_ne hm]
      rw [d3 m hm]; rfl
    · simp [DS.adv, d4]
    · simp [DS.adv, d5]
    · intro y hy
      have hy' : y ≠ iS ∧ y ≠ iJ ∧ y ≠ iSp ∧ y ≠ x := by simpa using hy
      simp only [DS.adv, DS.set]
      rw [Function.update_of_ne hy'.2.2.2, d6 y (by simp [hy'.1, hy'.2.1])]
      simp [Function.update_of_ne hy'.2.2.1]

end NearCubicGates.Adapters.Compile
