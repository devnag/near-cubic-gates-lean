import Proof.Gates.CounterMachine.PrefixGen

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.PrefixProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader

/-- `par := par ⊕ bit(x / pw)`. -/
def toggleP : St VV MM :=
  .seq (.op (.dm jx pw q1 r1)) (.seq (.op (.dm q1 v2 q2 r2))
    (.ite (.eq r2 v1) (.seq (.op (.copy tt v1)) (.seq (.op (.sub tt par)) (.op (.copy par tt)))) (.op (.zero yJ))))

def scanBody : St VV MM :=
  .seq (.op (.rdM sIn ci)) (.seq (.ite (.eq ci pi) toggleP (.op (.zero yJ))) (.op (.shl pw)))

/-- One scan of the coordinate list for the parity entry `pi`. -/
def scanP : St VV MM := .seq (.op (.rwM sIn)) (.seq (.op (.copy pw v1)) (forS js xkk scanBody))

def scanT : List (Fin VV) := [js, ci, pw, q1, r1, q2, r2, tt, par, yJ]

theorem toggle_spec (C : Ctx) (d : DS VV MM) (hc : Cst d) (β : Bool) (hpar : d.env par = β.toNat) (x t : ℕ)
    (hx : d.env jx = x) (hpw : d.env pw = 2 ^ t) (ht : 2 ^ (t + 1) ≤ 2 ^ C.Wd) (hW : 2 ≤ C.Wd) :
    Hs C toggleP d 10 (fun e => e.env par = (xor β (x.testBit t)).toNat ∧ e.out = d.out ∧ e.ram = d.ram ∧
      e.rc = d.rc ∧ Oth d e ∧ Fr d e [q1, r1, q2, r2, tt, par, yJ]) := by
  have h4 : 2 * 2 ≤ 2 ^ C.Wd := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hW)
  refine Hs.seq (t1 := 1) (t2 := 8) (hs_dm C jx pw q1 r1 d (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hpw]; positivity) (by rw [hpw, ← pow_succ']; exact ht)) (fun e he => ?_)
  subst he
  set e := (d.set q1 (d.env jx / d.env pw)).set r1 (d.env jx % d.env pw) with hedef
  have e2 : e.env v2 = 2 := by rw [hedef]; vsimp [hc.two]
  refine Hs.seq (t1 := 1) (t2 := 6) (hs_dm C q1 v2 q2 r2 e (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [e2]; norm_num) (by rw [e2]; exact h4)) (fun f hf => ?_)
  subst hf
  set f := (e.set q2 (e.env q1 / e.env v2)).set r2 (e.env q1 % e.env v2) with hfdef
  have fr2 : f.env r2 = x / 2 ^ t % 2 := by rw [hfdef, e2, hedef]; vsimp [hx, hpw]
  have fpar : f.env par = β.toNat := by rw [hfdef, hedef]; vsimp [hpar]
  have f1 : f.env v1 = 1 := by rw [hfdef, hedef]; vsimp [hc.one]
  have hbit : x.testBit t = decide (x / 2 ^ t % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  have ffr : Fr d f [q1, r1, q2, r2, tt, par, yJ] := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [hfdef, hedef]; vsimp [Function.update_apply, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1]
  refine Hs.ite (c := .eq r2 v1) (show r2 ≠ v1 by decide) (fun h => ?_) (fun h => ?_)
  · have hb1 : x / 2 ^ t % 2 = 1 := by simpa [Cnd.eval, fr2, f1] using h
    refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C tt v1 f (by decide)) (fun g hg => ?_)
    subst hg
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_sub C tt par _ (by decide) (by
      vsimp [f1, fpar]; cases β <;> simp)) (fun g' hg' => ?_)
    subst hg'
    refine Hs.mono (hs_copy C par tt _ (by decide)) le_rfl ?_
    rintro r rfl
    refine ⟨by vsimp [f1, fpar]; rw [hbit, hb1]; cases β <;> simp, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    exact Fr.trans ffr (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.set _ _ (by decide))))
  · have hb0 : x / 2 ^ t % 2 ≠ 1 := by simpa [Cnd.eval, fr2, f1] using h
    refine Hs.mono (hs_zero C yJ f) (by omega) ?_
    rintro r rfl
    refine ⟨by vsimp [fpar]; rw [hbit]; simp only [hb0, decide_false, Bool.xor_false], rfl, rfl, rfl,
      ⟨rfl, rfl, rfl, rfl⟩,
      Fr.trans ffr (Fr.set _ _ (by decide))⟩

theorem getElem_not_mem_take {L : List ℕ} (hnd : L.Nodup) (t : ℕ) (ht : t < L.length) : L[t] ∉ L.take t := by
  intro hm
  obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hm
  rw [List.getElem_take] at hjeq
  have hjt : j < t := by simp at hj; omega
  have := (List.Nodup.getElem_inj_iff hnd).1 hjeq
  omega

theorem scan_spec (C : Ctx) (d : DS VV MM) (hc : Cst d) (β : Bool) (hpar : d.env par = β.toNat) (x i : ℕ)
    (hx : d.env jx = x) (hi : d.env pi = i) (L : List ℕ) (hL : d.ram sIn = L) (hnd : L.Nodup)
    (hk : d.env xkk = L.length) (hLW : L.length < C.Wd) (hrc : d.rc sIn ≤ L.length) (hW : 2 ≤ C.Wd) :
    Hs C scanP d (20 * L.length + 8) (fun e => e.env par = (xor β (pbit L x i)).toNat ∧ e.out = d.out ∧
      e.ram = d.ram ∧ e.rc = Function.update d.rc sIn L.length ∧ Oth d e ∧ Fr d e scanT) := by
  have hLW2 : L.length < 2 ^ C.Wd := lt_of_lt_of_le hLW (Nat.lt_two_pow_self).le
  refine Hs.mono (Hs.seq (t1 := L.length + 1) (t2 := 1 + (L.length * (15 + 4) + 4) + 1)
    (Hs.mono (hs_rwM C sIn d) (by omega) (fun _ h => h)) (fun d1 hd1 => ?_)) (by omega) (fun _ h => h)
  subst hd1
  refine Hs.seq (t1 := 1) (hs_copy C pw v1 _ (by decide)) (fun d2 hd2 => ?_)
  subst hd2
  let I : ℕ → DS VV MM → Prop := fun t g => g.env par = (xor β (if i ∈ L.take t then x.testBit (L.idxOf i)
    else false)).toNat ∧ g.env pw = 2 ^ t ∧ g.rc = Function.update d.rc sIn t ∧ g.out = d.out ∧ g.ram = d.ram ∧
    Oth d g ∧ Fr d g scanT
  have hl := forS_spec' (C := C) js xkk (by decide) scanBody ((d.rew sIn).set pw ((d.rew sIn).env v1)) L.length
    hLW2 I 15
    (fun t g v ⟨g1, g2, g3, g4, g5, g6, g7⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact g1,
      by rw [DS.set_env_ne _ _ (by decide)]; exact g2, g3, g4, g5, g6.trans ⟨rfl, rfl, rfl, rfl⟩,
      Fr.trans g7 (Fr.set g v (by decide))⟩)
    ⟨by vsimp [DS.rew, hpar], by vsimp [DS.rew, hc.one], by simp [DS.rew], rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩,
      Fr.trans (fun y hy => rfl) (Fr.set _ _ (by decide))⟩ (by vsimp [DS.rew, hk]) ?_
  · refine Hs.mono hl le_rfl ?_
    rintro g ⟨⟨g1, _, g3, g4, g5, g6, g7⟩, _, _⟩
    refine ⟨by rw [g1, List.take_of_length_le le_rfl]; rfl, g4, g5, g3, g6, g7⟩
  · intro t ht g ⟨g1, g2, g3, g4, g5, g6, g7⟩ _ _
    have gc : Cst g := Cst.of_fr hc g7 (by decide)
    have hrc' : g.rc sIn < (g.ram sIn).length := by rw [g3, Function.update_self, g5, hL]; exact ht
    refine Hs.seq (t1 := 1) (t2 := 13) (hs_rdM C sIn ci g hrc') (fun e he => ?_)
    subst he
    set e := (g.set ci ((g.ram sIn).getD (g.rc sIn) 0)).adv sIn with hedef
    have eci : e.env ci = L[t] := by
      rw [hedef]; simp only [DS.adv, DS.set_env_self, g3, g5, hL, Function.update_self]
      rw [List.getD_eq_getElem _ _ ht]
    have epi : e.env pi = i := by
      rw [hedef]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide), g7 pi (by decide), hi]
    have ec : Cst e := ⟨by rw [hedef]; simp [DS.adv]; vsimp [gc.z], by rw [hedef]; simp [DS.adv]; vsimp [gc.one],
      by rw [hedef]; simp [DS.adv]; vsimp [gc.two]⟩
    have epar : e.env par = (xor β (if i ∈ L.take t then x.testBit (L.idxOf i) else false)).toNat := by
      rw [hedef]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide)]; exact g1
    have epw : e.env pw = 2 ^ t := by
      rw [hedef]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide)]; exact g2
    have ex : e.env jx = x := by
      rw [hedef]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide), g7 jx (by decide), hx]
    have htake : L.take (t + 1) = L.take t ++ [L[t]] := CellTables.take_succ_getElem L t _ (List.getElem?_eq_getElem ht)
    have hpow : 2 ^ (t + 1) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    -- the new parity
    have step2 : Hs C (.ite (.eq ci pi) toggleP (.op (.zero yJ))) e 11 (fun f =>
        f.env par = (xor β (if i ∈ L.take (t + 1) then x.testBit (L.idxOf i) else false)).toNat ∧
        f.out = e.out ∧ f.ram = e.ram ∧ f.rc = e.rc ∧ Oth e f ∧ Fr e f [q1, r1, q2, r2, tt, par, yJ]) := by
      refine Hs.ite (c := .eq ci pi) (show ci ≠ pi by decide) (fun h => ?_) (fun h => ?_)
      · have hLt : L[t] = i := by simpa [Cnd.eval, eci, epi] using h
        have hnot : i ∉ L.take t := by
          rw [← hLt]; exact getElem_not_mem_take hnd t ht
        have hidx : L.idxOf i = t := by rw [← hLt]; exact List.Nodup.idxOf_getElem hnd t ht
        have bβ : e.env par = β.toNat := by rw [epar, if_neg hnot]; simp
        refine Hs.mono (toggle_spec C e ec β bβ x t ex epw hpow hW) le_rfl ?_
        rintro f ⟨f1, f2, f3, f4, f5, f6⟩
        refine ⟨?_, f2, f3, f4, f5, f6⟩
        rw [f1, htake, if_pos (List.mem_append_right _ (List.mem_singleton.2 hLt.symm)), hidx]
      · have hLt : L[t] ≠ i := by simpa [Cnd.eval, eci, epi] using h
        refine Hs.mono (hs_zero C yJ e) (by omega) ?_
        rintro f rfl
        refine ⟨?_, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, Fr.set e _ (by decide)⟩
        rw [DS.set_env_ne _ _ (by decide), epar, htake]
        simp only [List.mem_append, List.mem_singleton, Ne.symm hLt, or_false]
    refine Hs.seq (t1 := 11) (t2 := 1) step2 (fun f ⟨f1, f2, f3, f4, f5, f6⟩ => ?_)
    have fpw : f.env pw = 2 ^ t := by rw [f6 pw (by decide), epw]
    refine Hs.mono (hs_shl C pw f (by rw [fpw, ← pow_succ']; exact Nat.pow_lt_pow_right (by norm_num) (by omega)))
      le_rfl ?_
    rintro r rfl
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide), f1]
    · rw [DS.set_env_self, fpw, pow_succ]; ring
    · simp only [DS.set_rc, f4, hedef, DS.adv, Function.update_self, g3, Function.update_idem]
    · simp only [DS.set_out, f2, hedef, DS.adv, DS.set_out, g4]
    · simp only [DS.set_ram, f3, hedef, DS.adv, DS.set_ram, g5]
    · exact g6.trans ((show Oth g e from ⟨rfl, rfl, rfl, rfl⟩).trans (f5.trans ⟨rfl, rfl, rfl, rfl⟩))
    · refine Fr.trans g7 (Fr.trans (fun y hy => ?_) (Fr.trans (Fr.weaken f6 (by decide)) (Fr.set f _ (by decide))))
      rw [hedef]; simp only [DS.adv]; exact Fr.set g _ (show ci ∈ scanT by decide) y hy
    · rw [DS.set_env_ne _ _ (by decide), f6 js (by decide), hedef]; simp only [DS.adv]
      rw [DS.set_env_ne _ _ (by decide)]; assumption
    · rw [DS.set_env_ne _ _ (by decide), f6 xkk (by decide), hedef]; simp only [DS.adv]
      rw [DS.set_env_ne _ _ (by decide)]; assumption

/-! ## The fold over the parity list -/

def parBody : St VV MM := .seq (.op (.rdM sPa pi)) scanP

def parityP : St VV MM := .seq (.op (.zero par)) (.seq (.op (.rwM sPa)) (forS jp xnp parBody))

def parT : List (Fin VV) := [jp, pi, js, ci, pw, q1, r1, q2, r2, tt, par, yJ]

theorem parity_spec (C : Ctx) (d : DS VV MM) (hc : Cst d) (x : ℕ) (hx : d.env jx = x) (P L : List ℕ)
    (hP : d.ram sPa = P) (hnp : d.env xnp = P.length) (hPW : P.length < 2 ^ C.Wd) (hL : d.ram sIn = L)
    (hnd : L.Nodup) (hk : d.env xkk = L.length) (hLW : L.length < C.Wd) (hrcP : d.rc sPa ≤ P.length)
    (hrcI : d.rc sIn ≤ L.length) (hW : 2 ≤ C.Wd) :
    Hs C parityP d (P.length * (20 * L.length + 15) + 8) (fun e =>
      e.env par = ((P.map (pbit L x)).foldl xor false).toNat ∧ e.out = d.out ∧ e.ram = d.ram ∧ Oth d e ∧
      Fr d e parT) := by
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := P.length + 1 + (P.length * (20 * L.length + 10 + 4) + 4) + 1)
    (hs_zero C par d) (fun d1 hd1 => ?_)) (by nlinarith) (fun _ h => h)
  subst hd1
  refine Hs.seq (t1 := P.length + 1) (Hs.mono (hs_rwM C sPa _) (by simp only [DS.set_rc]; omega) (fun _ h => h))
    (fun d2 hd2 => ?_)
  subst hd2
  let I : ℕ → DS VV MM → Prop := fun u g => g.env par = (((P.take u).map (pbit L x)).foldl xor false).toNat ∧
    g.rc sPa = u ∧ g.rc sIn ≤ L.length ∧ g.out = d.out ∧ g.ram = d.ram ∧ Oth d g ∧ Fr d g parT
  have hrc0 : ((d.set par 0).rew sPa).rc sIn ≤ L.length := by
    simp only [DS.rew, DS.set_rc]; rw [Function.update_of_ne (by decide)]; exact hrcI
  have hl := forS_spec' (C := C) jp xnp (by decide) parBody (((d.set par 0).rew sPa)) P.length hPW I
    (20 * L.length + 10)
    (fun u g v ⟨g1, g2, g3, g4, g5, g6, g7⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact g1, g2, g3, g4, g5,
      g6.trans ⟨rfl, rfl, rfl, rfl⟩, Fr.trans g7 (Fr.set g v (by decide))⟩)
    ⟨by vsimp [DS.rew], by simp [DS.rew], hrc0, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩,
      Fr.trans (Fr.set d _ (by decide)) (fun y hy => rfl)⟩
    (by vsimp [DS.rew, hnp]) ?_
  · refine Hs.mono hl le_rfl ?_
    rintro g ⟨⟨g1, _, _, g4, g5, g6, g7⟩, _, _⟩
    exact ⟨by rw [g1, List.take_of_length_le le_rfl], g4, g5, g6, g7⟩
  · intro u hu g ⟨g1, g2, g3, g4, g5, g6, g7⟩ hgj hgn
    have gc : Cst g := Cst.of_fr hc g7 (by decide)
    have hrc' : g.rc sPa < (g.ram sPa).length := by rw [g2, g5, hP]; exact hu
    unfold parBody
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 20 * L.length + 8) (hs_rdM C sPa pi g hrc') (fun e he => ?_)) (by omega)
      (fun _ h => h)
    subst he
    set e := (g.set pi ((g.ram sPa).getD (g.rc sPa) 0)).adv sPa with hedef
    have ec : Cst e := ⟨by rw [hedef]; simp [DS.adv]; vsimp [gc.z], by rw [hedef]; simp [DS.adv]; vsimp [gc.one],
      by rw [hedef]; simp [DS.adv]; vsimp [gc.two]⟩
    have epi : e.env pi = P[u] := by
      rw [hedef]; simp only [DS.adv, DS.set_env_self, g2, g5, hP]; rw [List.getD_eq_getElem _ _ hu]
    have epar : e.env par = (((P.take u).map (pbit L x)).foldl xor false).toNat := by
      rw [hedef]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide)]; exact g1
    have ex : e.env jx = x := by
      rw [hedef]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide), g7 jx (by decide), hx]
    have eL : e.ram sIn = L := by rw [hedef]; simp only [DS.adv, DS.set_ram, g5, hL]
    have ek : e.env xkk = L.length := by
      rw [hedef]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide), g7 xkk (by decide), hk]
    have erc : e.rc sIn ≤ L.length := by
      rw [hedef]; simp only [DS.adv, DS.set_rc]; rw [Function.update_of_ne (by decide)]; exact g3
    refine Hs.mono (scan_spec C e ec _ epar x P[u] ex epi L eL hnd ek hLW erc hW) le_rfl ?_
    rintro f ⟨f1, f2, f3, f4, f5, f6⟩
    have htake : P.take (u + 1) = P.take u ++ [P[u]] := CellTables.take_succ_getElem P u _ (List.getElem?_eq_getElem hu)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [f1, htake, List.map_append, List.foldl_append]; rfl
    · rw [f4, Function.update_of_ne (by decide), hedef]; simp [DS.adv, g2]
    · rw [f4, Function.update_self]
    · rw [f2, hedef]; simp [DS.adv, g4]
    · rw [f3, hedef]; simp [DS.adv, g5]
    · exact g6.trans ((show Oth g e from ⟨rfl, rfl, rfl, rfl⟩).trans f5)
    · refine Fr.trans g7 (Fr.trans (fun y hy => ?_) (Fr.weaken f6 (by decide)))
      rw [hedef]; simp only [DS.adv]; exact Fr.set g _ (show pi ∈ parT by decide) y hy
    · rw [f6 jp (by decide), hedef]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide)]; exact hgj
    · rw [f6 xnp (by decide), hedef]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide)]; exact hgn

/-! ## The field -/

/-- The constant `b` as a variable. -/
def cBv (b : Bool) : Fin VV := if b then v1 else vZ

def hbBody (b : Bool) : St VV MM :=
  .seq parityP (.seq (.ite (.eq par (cBv b)) (.op (.copy hv v1)) (.op (.zero hv))) (femNat hv))

/-- The indicator bits of the part `H_b`. -/
def hbParP (b : Bool) : St VV MM := forS jx xK2 (hbBody b)

def hbT : List (Fin VV) := [jp, pi, js, ci, pw, q1, r1, q2, r2, tt, par, yJ, hv, y0, y1, y2, y3, y4]

theorem cBv_env (b : Bool) (d : DS VV MM) (hc : Cst d) : d.env (cBv b) = b.toNat := by
  cases b
  · simp [cBv, hc.z]
  · simp [cBv, hc.one]

theorem hbParO (C : Ctx) (b : Bool) (a : DS VV MM) (hva : Valid C a) (hc : Cst a) (hW : 2 ≤ C.Wd) (K : ℕ)
    (hK : a.env xK2 = K) (P L : List ℕ) (hP : a.ram sPa = P) (hnp : a.env xnp = P.length) (hL : a.ram sIn = L)
    (hnd : L.Nodup) (hk : a.env xkk = L.length) (hLW : L.length < C.Wd) :
    OutT C (hbParP b) a (K * (P.length * (20 * L.length + 15) + 70 + 4) + 4)
      ((List.range K).flatMap (fun x => Fn (if (P.map (pbit L x)).foldl xor false = b then 1 else 0)))
      (jx :: hbT) := by
  have hKW : K < 2 ^ C.Wd := by rw [← hK]; exact hva.env_lt xK2
  have hPW : P.length < 2 ^ C.Wd := by rw [← hnp]; exact hva.env_lt xnp
  refine loopT jx xK2 (by decide) hbT (by decide) (by decide) _ a hva K hKW hK _ _ ?_
  intro x hx d d1 d2 d3 d4 d5
  have dc : Cst d := Cst.of_fr hc d3 (by decide)
  have dP : d.ram sPa = P := by rw [d1, hP]
  have dL : d.ram sIn = L := by rw [d1, hL]
  have dnp : d.env xnp = P.length := by rw [d3 xnp (by decide), hnp]
  have dk : d.env xkk = L.length := by rw [d3 xkk (by decide), hk]
  have hrcP : d.rc sPa ≤ P.length := by rw [← dP]; exact d4.rc_le sPa
  have hrcI : d.rc sIn ≤ L.length := by rw [← dL]; exact d4.rc_le sIn
  unfold OutT hbBody
  refine Hs.mono (Hs.seq (t1 := P.length * (20 * L.length + 15) + 8) (t2 := 2 + 50 + 1)
    (Hs.valid (parity_spec C d dc x d5 P L dP dnp hPW dL hnd dk hLW hrcP hrcI hW) d4 (by omega))
    (fun e ⟨⟨e1, e2, e3, e4, e5⟩, ev⟩ => ?_)) (by omega) (fun _ h => h)
  have ec : Cst e := Cst.of_fr dc e5 (by decide)
  set β := (P.map (pbit L x)).foldl xor false with hβ
  have step : Hs C (.ite (.eq par (cBv b)) (.op (.copy hv v1)) (.op (.zero hv))) e 2 (fun f =>
      f = e.set hv (if β = b then 1 else 0)) := by
    refine Hs.ite (c := .eq par (cBv b)) (show par ≠ cBv b by cases b <;> decide) (fun h => ?_) (fun h => ?_)
    · have hb : β = b := by
        have : e.env par = e.env (cBv b) := by simpa [Cnd.eval] using h
        rw [e1, cBv_env b e ec] at this
        have key : ∀ u w : Bool, u.toNat = w.toNat → u = w := by decide
        exact key _ _ this
      refine Hs.mono (hs_copy C hv v1 e (by decide)) le_rfl ?_
      rintro f rfl; rw [if_pos hb, ec.one]
    · have hb : β ≠ b := by
        have : e.env par ≠ e.env (cBv b) := by simpa [Cnd.eval] using h
        rw [e1, cBv_env b e ec] at this
        intro h'; rw [h'] at this; exact this rfl
      refine Hs.mono (hs_zero C hv e) le_rfl ?_
      rintro f rfl; rw [if_neg hb]
  refine Hs.seq (t1 := 2) (t2 := 50) step (fun f hf => ?_)
  subst hf
  have fc : Cst (e.set hv (if β = b then 1 else 0)) :=
    Cst.of_fr ec (Fr.set e _ (show hv ∈ [hv] by simp)) (by decide)
  have hval : (if β = b then 1 else 0) < 2 ^ C.Wd :=
    lt_of_le_of_lt (by split_ifs <;> omega) (Nat.one_lt_two_pow (by omega))
  have fv : Valid C (e.set hv (if β = b then 1 else 0)) := Valid.set' ev hv _ hval
  refine Hs.mono (femO C hv (by decide) _ fv fc hW) (by
    rw [DS.set_env_self]; split_ifs <;> simp [natBitLength]) ?_
  rintro g ⟨g1, g2, g3, g4, g5⟩
  refine ⟨?_, by rw [g2]; exact e3, e4.trans ((show Oth e (e.set hv (if β = b then 1 else 0)) from
    ⟨rfl, rfl, rfl, rfl⟩).trans g3), ?_, g5⟩
  · rw [g1, DS.set_env_self]; simp only [DS.set_out, e2]
  · exact Fr.trans (Fr.weaken e5 (by decide)) (Fr.trans (Fr.set e _ (by decide)) (Fr.weaken g4 (by decide)))

end NearCubicGates.Close.CounterMachine.PrefixProg
