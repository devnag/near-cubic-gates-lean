import Proof.Gates.Cells.Pre2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

def wW : Fin VV := ⟨76, by decide⟩
def wK : Fin VV := ⟨77, by decide⟩
def wP : Fin VV := ⟨78, by decide⟩
def wNF : Fin VV := ⟨80, by decide⟩
def wCo : Fin VV := ⟨81, by decide⟩

theorem params_shape (c : Call) (p : Params) (wt : Wit c.n) : paramsN p ++ witN c p wt =
    [p.n, bitN p.pair] ++ (p.W :: (ratN p.beta ++ (p.k :: ([p.T, p.m, p.Dmax] ++ (p.P :: ([p.e] ++
    ((p.primes.sort (· ≤ ·)).length :: (p.primes.sort (· ≤ ·) ++ ([p.window, p.L2, p.Lw] ++ (p.hE ::
    ([p.h, p.R0] ++ (ratN p.ell0 ++ (p.M1 :: ([p.J] ++ (p.factors.length :: (p.factors ++ (p.A :: (p.Lambda ::
    ((coordsOf wt.I).length :: (coordsOf wt.I ++ blocksAll wt.coef (roleCount c.kind) p.J)))))))))))))))))))) := by
  simp only [paramsN, witN, srList, blocksAll, blocksOf, List.flatMap_assoc, List.flatMap_map, List.append_assoc,
    List.cons_append, List.singleton_append, List.nil_append]

def walkP1 : St VV MM :=
  .seq (skK 2) (.seq (rdW wW) (.seq (skK 3) (.seq (rdW wK) (.seq (skK 3) (.seq (rdW wP) (.seq (skK 1)
    (.seq (rdW vNP) (.op (.copy vIPr wPos)))))))))

def wp1T : List (Fin VV) := [wY, c0, vJ, wPos, wW, wK, wP, vNP, vIPr]

theorem walkP1_spec (c : Call) (p : Params) (wt : Wit c.n) (a : DS VV MM) (pos0 : ℕ)
    (h0 : WSt (cellN c p wt) a pos0 (paramsN p ++ witN c p wt)) (hW : pos0 + 20 < 2 ^ C.Wd) :
    Hs C walkP1 a 200 (fun d =>
      WSt (cellN c p wt) d (pos0 + 13) (p.primes.sort (· ≤ ·) ++ ([p.window, p.L2, p.Lw] ++ (p.hE ::
        ([p.h, p.R0] ++ (ratN p.ell0 ++ (p.M1 :: ([p.J] ++ (p.factors.length :: (p.factors ++ (p.A :: (p.Lambda ::
        ((coordsOf wt.I).length :: (coordsOf wt.I ++ blocksAll wt.coef (roleCount c.kind) p.J))))))))))))) ∧
      d.env wW = p.W ∧ d.env wK = p.k ∧ d.env wP = p.P ∧ d.env vNP = (p.primes.sort (· ≤ ·)).length ∧
      d.env vIPr = pos0 + 13 ∧ Agr a d [sN] wp1T) := by
  rw [params_shape] at h0
  refine Hs.bseq (skK_spec (C := C) 2 _ a pos0 [p.n, bitN p.pair] _ h0 rfl (by omega)) (by omega)
    (fun e1 ⟨w1, a1⟩ => ?_)
  refine Hs.bseq (rdW_spec (C := C) wW (by decide) _ e1 _ p.W _ w1 (by omega)) (by omega)
    (fun e2 ⟨u2, w2, a2⟩ => ?_)
  refine Hs.bseq (skK_spec (C := C) 3 _ e2 _ (ratN p.beta) _ w2 (ratN_length _) (by omega)) (by omega)
    (fun e3 ⟨w3, a3⟩ => ?_)
  refine Hs.bseq (rdW_spec (C := C) wK (by decide) _ e3 _ p.k _ w3 (by omega)) (by omega)
    (fun e4 ⟨u4, w4, a4⟩ => ?_)
  refine Hs.bseq (skK_spec (C := C) 3 _ e4 _ [p.T, p.m, p.Dmax] _ w4 rfl (by omega)) (by omega)
    (fun e5 ⟨w5, a5⟩ => ?_)
  refine Hs.bseq (rdW_spec (C := C) wP (by decide) _ e5 _ p.P _ w5 (by omega)) (by omega)
    (fun e6 ⟨u6, w6, a6⟩ => ?_)
  refine Hs.bseq (skK_spec (C := C) 1 _ e6 _ [p.e] _ w6 rfl (by omega)) (by omega)
    (fun e7 ⟨w7, a7⟩ => ?_)
  refine Hs.bseq (rdW_spec (C := C) vNP (by decide) _ e7 _ _ _ w7 (by omega)) (by omega)
    (fun e8 ⟨u8, w8, a8⟩ => ?_)
  refine Hs.mono (hs_copy C vIPr wPos e8 (by decide)) (by omega) ?_
  rintro d rfl
  refine ⟨⟨w8.ram, w8.rc, by rw [DS.set_env_ne _ _ (by decide)]; exact w8.pv, w8.dr, w8.le⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide), a8.fr wW (by decide), a7.fr wW (by decide), a6.fr wW (by decide),
      a5.fr wW (by decide), a4.fr wW (by decide), a3.fr wW (by decide), u2]
  · rw [DS.set_env_ne _ _ (by decide), a8.fr wK (by decide), a7.fr wK (by decide), a6.fr wK (by decide),
      a5.fr wK (by decide), u4]
  · rw [DS.set_env_ne _ _ (by decide), a8.fr wP (by decide), a7.fr wP (by decide), u6]
  · rw [DS.set_env_ne _ _ (by decide), u8]
  · rw [DS.set_env_self, w8.pv]
  · exact (a1.weaken (by decide) (by decide)).trans ((a2.weaken (by decide) (by decide)).trans
      ((a3.weaken (by decide) (by decide)).trans ((a4.weaken (by decide) (by decide)).trans
      ((a5.weaken (by decide) (by decide)).trans ((a6.weaken (by decide) (by decide)).trans
      ((a7.weaken (by decide) (by decide)).trans ((a8.weaken (by decide) (by decide)).trans
      (Agr.set _ _ _ (by decide)))))))))

def walkP2 : St VV MM :=
  .seq (.op (.copy wY vNP)) (.seq skW (.seq (skK 3) (.seq (rdW vHE) (.seq (skK 2) (.seq (skK 3) (.seq (rdW vM1)
    (.seq (skK 1) (.seq (.op (.copy gFS wPos)) (rdW wNF)))))))))

def wp2T : List (Fin VV) := [wY, c0, vJ, wPos, vHE, vM1, gFS, wNF]

theorem walkP2_spec (L : List ℕ) (p : Params) (REST : List ℕ) (a : DS VV MM) (pos1 : ℕ)
    (h0 : WSt L a pos1 (p.primes.sort (· ≤ ·) ++ ([p.window, p.L2, p.Lw] ++ (p.hE ::
        ([p.h, p.R0] ++ (ratN p.ell0 ++ (p.M1 :: ([p.J] ++ (p.factors.length :: REST)))))))))
    (hNP : a.env vNP = (p.primes.sort (· ≤ ·)).length)
    (hW : pos1 + (p.primes.sort (· ≤ ·)).length + 20 < 2 ^ C.Wd) :
    Hs C walkP2 a ((p.primes.sort (· ≤ ·)).length * 5 + 200) (fun d =>
      WSt L d (pos1 + (p.primes.sort (· ≤ ·)).length + 12) REST ∧
      d.env vHE = p.hE ∧ d.env vM1 = p.M1 ∧ d.env gFS = pos1 + (p.primes.sort (· ≤ ·)).length + 11 ∧
      d.env wNF = p.factors.length ∧ Agr a d [sN] wp2T) := by
  refine Hs.bseq (hs_copy C wY vNP a (by decide)) (by omega) (fun e1 he1 => ?_)
  subst he1
  have w1 : WSt L (a.set wY (a.env vNP)) pos1 _ := ⟨h0.ram, h0.rc, by rw [DS.set_env_ne _ _ (by decide)]; exact h0.pv,
    h0.dr, h0.le⟩
  have hsk := skW_spec (C := C) L _ pos1 _ _ w1 (by rw [DS.set_env_self, hNP]) (by omega)
  refine Hs.bseq hsk (by omega) (fun e2 ⟨w2, _, a2⟩ => ?_)
  refine Hs.bseq (skK_spec (C := C) 3 _ e2 _ [p.window, p.L2, p.Lw] _ w2 rfl (by omega)) (by omega)
    (fun e3 ⟨w3, a3⟩ => ?_)
  refine Hs.bseq (rdW_spec (C := C) vHE (by decide) _ e3 _ p.hE _ w3 (by omega)) (by omega)
    (fun e4 ⟨u4, w4, a4⟩ => ?_)
  refine Hs.bseq (skK_spec (C := C) 2 _ e4 _ [p.h, p.R0] _ w4 rfl (by omega)) (by omega)
    (fun e5 ⟨w5, a5⟩ => ?_)
  refine Hs.bseq (skK_spec (C := C) 3 _ e5 _ (ratN p.ell0) _ w5 (ratN_length _) (by omega)) (by omega)
    (fun e6 ⟨w6, a6⟩ => ?_)
  refine Hs.bseq (rdW_spec (C := C) vM1 (by decide) _ e6 _ p.M1 _ w6 (by omega)) (by omega)
    (fun e7 ⟨u7, w7, a7⟩ => ?_)
  refine Hs.bseq (skK_spec (C := C) 1 _ e7 _ [p.J] _ w7 rfl (by omega)) (by omega)
    (fun e8 ⟨w8, a8⟩ => ?_)
  refine Hs.bseq (hs_copy C gFS wPos e8 (by decide)) (by omega) (fun e9 he9 => ?_)
  subst he9
  have w9 : WSt L (e8.set gFS (e8.env wPos)) _ _ := ⟨w8.ram, w8.rc, by rw [DS.set_env_ne _ _ (by decide)]; exact w8.pv,
    w8.dr, w8.le⟩
  refine Hs.mono (rdW_spec (C := C) wNF (by decide) _ _ _ p.factors.length _ w9 (by omega)) (by omega) ?_
  rintro d ⟨u10, w10, a10⟩
  refine ⟨by convert w10 using 2, ?_, ?_, ?_, u10, ?_⟩
  · rw [a10.fr vHE (by decide), DS.set_env_ne _ _ (by decide), a8.fr vHE (by decide), a7.fr vHE (by decide),
      a6.fr vHE (by decide), a5.fr vHE (by decide), u4]
  · rw [a10.fr vM1 (by decide), DS.set_env_ne _ _ (by decide), a8.fr vM1 (by decide), u7]
  · rw [a10.fr gFS (by decide), DS.set_env_self, w8.pv]
  · exact (Agr.set _ _ _ (by decide)).trans ((a2.weaken (by decide) (by decide)).trans
      ((a3.weaken (by decide) (by decide)).trans ((a4.weaken (by decide) (by decide)).trans
      ((a5.weaken (by decide) (by decide)).trans ((a6.weaken (by decide) (by decide)).trans
      ((a7.weaken (by decide) (by decide)).trans ((a8.weaken (by decide) (by decide)).trans
      ((Agr.set _ _ _ (by decide)).trans (a10.weaken (by decide) (by decide))))))))))

theorem len_le_flatMap' {α β : Type} (l : List α) (f : α → List β) (h : ∀ x ∈ l, 1 ≤ (f x).length) :
    l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h x (List.mem_cons_self ..)
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

def blkStep : St VV MM := .seq (rdW wY) (.seq (.op (.shl wY)) skW)

def setWS : St VV MM := .seq (.op (.copy gWS wPos)) (.seq (.op (.add gWS wCo)) (.op (.copy wY wCo)))

theorem setWS_spec (a : DS VV MM) (h : a.env wPos + a.env wCo < 2 ^ C.Wd) :
    Hs C setWS a 5 (fun b => b.env gWS = a.env wPos + a.env wCo ∧ b.env wY = a.env wCo ∧ b.ram = a.ram ∧
      b.rc = a.rc ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      Fr a b [gWS, wY]) := by
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C gWS wPos a (by decide)) (fun e he => ?_)
  subst he
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_add C gWS wCo _ (by decide)
    (by rw [DS.set_env_self, DS.set_env_ne _ _ (by decide)]; exact h)) (fun e he => ?_)
  subst he
  refine Hs.mono (hs_copy C wY wCo _ (by decide)) le_rfl ?_
  rintro b rfl
  refine ⟨by vsimp [], by vsimp [], rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  rw [DS.set_env_ne _ _ hy.2, DS.set_env_ne _ _ hy.1, DS.set_env_ne _ _ hy.1]

def walkP3 : St VV MM :=
  .seq (.op (.copy wY wNF)) (.seq skW (.seq (rdW vA) (.seq (rdW vLam) (.seq (rdW wCo) (.seq setWS
    (.seq skW (.seq (forS c1 gJR blkStep) (.op (.copy vNL wPos)))))))))

def wp3T : List (Fin VV) := [wY, c0, vJ, wPos, vA, vLam, wCo, gWS, c1, vNL]

/-- The witness blocks, one list per stage-role pair. -/
def blkG (c : Call) (wt : Wit c.n) (sr : ℕ × ℕ) : List ℕ := [(wt.coef sr.1 sr.2).length] ++ (wt.coef sr.1 sr.2).flatMap intN

theorem blocksAll_eq (c : Call) (p : Params) (wt : Wit c.n) :
    blocksAll wt.coef (roleCount c.kind) p.J = (srList c p).flatMap (blkG c wt) := by
  simp only [srList, blocksAll, blocksOf, blkG, List.flatMap_assoc, List.flatMap_map]

theorem blkStep_spec (L : List ℕ) (e : DS VV MM) (pos : ℕ) (cs : List ℤ) (rest : List ℕ)
    (h : WSt L e pos ([cs.length] ++ cs.flatMap intN ++ rest)) (hW : pos + 1 + 2 * cs.length < 2 ^ C.Wd) :
    Hs C blkStep e (2 * cs.length * 5 + 20) (fun d => WSt L d (pos + 1 + 2 * cs.length) rest ∧
      Agr e d [sN] [wY, c0, vJ, wPos]) := by
  rw [List.append_assoc] at h
  refine Hs.bseq (rdW_spec (C := C) wY (by decide) L e pos cs.length _ h (by omega)) (by omega)
    (fun e1 ⟨u1, w1, a1⟩ => ?_)
  refine Hs.bseq (hs_shl C wY e1 (by rw [u1]; omega)) (by omega) (fun e2 he2 => ?_)
  subst he2
  have w2 : WSt L (e1.set wY (2 * e1.env wY)) (pos + 1) (cs.flatMap intN ++ rest) :=
    ⟨w1.ram, w1.rc, by rw [DS.set_env_ne _ _ (by decide)]; exact w1.pv, w1.dr, w1.le⟩
  have hsk := skW_spec (C := C) L _ _ _ _ w2 (by rw [DS.set_env_self, u1, flatMap_intN_length])
    (by rw [flatMap_intN_length]; omega)
  rw [flatMap_intN_length] at hsk
  refine Hs.mono hsk (by omega) ?_
  rintro d ⟨wd, _, ad⟩
  exact ⟨wd, (a1.weaken (by decide) (by decide)).trans ((Agr.set _ _ _ (by decide)).trans
    (ad.weaken (by decide) (by decide)))⟩

theorem take_succ_flatMap {α β : Type} (l : List α) (f : α → List β) (m : ℕ) (hm : m < l.length) :
    ((l.take (m + 1)).flatMap f).length = ((l.take m).flatMap f).length + (f l[m]).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, List.flatMap_append, List.length_append,
    List.flatMap_singleton]

theorem drop_cons_flatMap {α β : Type} (l : List α) (f : α → List β) (m : ℕ) (hm : m < l.length) :
    (l.drop m).flatMap f = f l[m] ++ (l.drop (m + 1)).flatMap f := by
  rw [List.drop_eq_getElem_cons hm, List.flatMap_cons]

theorem walkP3_spec (c : Call) (p : Params) (wt : Wit c.n) (a : DS VV MM) (pos2 : ℕ)
    (h0 : WSt (cellN c p wt) a pos2 (p.factors ++ (p.A :: (p.Lambda :: ((coordsOf wt.I).length ::
      (coordsOf wt.I ++ blocksAll wt.coef (roleCount c.kind) p.J))))))
    (hNF : a.env wNF = p.factors.length) (hJR : a.env gJR = p.J * roleCount c.kind)
    (hW : (cellN c p wt).length + 10 < 2 ^ C.Wd) :
    Hs C walkP3 a ((cellN c p wt).length * 30 + (p.J * roleCount c.kind) * (10 * (cellN c p wt).length + 20 + 4) +
      200) (fun d => d.env vA = p.A ∧ d.env vLam = p.Lambda ∧
      d.env gWS = pos2 + p.factors.length + 3 + (coordsOf wt.I).length ∧ d.env vNL = (cellN c p wt).length ∧
      d.env wCo = (coordsOf wt.I).length ∧ d.ram sN = cellN c p wt ∧ Agr a d [sN] wp3T) := by
  have hle := h0.le
  have hlen0 := congrArg List.length h0.dr
  simp only [List.length_drop, List.length_append, List.length_cons] at hlen0
  refine Hs.bseq (hs_copy C wY wNF a (by decide)) (by omega) (fun e1 he1 => ?_)
  subst he1
  have w1 : WSt (cellN c p wt) (a.set wY (a.env wNF)) pos2 _ :=
    ⟨h0.ram, h0.rc, by rw [DS.set_env_ne _ _ (by decide)]; exact h0.pv, h0.dr, h0.le⟩
  have hsk := skW_spec (C := C) _ _ pos2 _ _ w1 (by rw [DS.set_env_self, hNF]) (by omega)
  refine Hs.bseq hsk (by omega) (fun e2 ⟨w2, _, a2⟩ => ?_)
  refine Hs.bseq (rdW_spec (C := C) vA (by decide) _ e2 _ p.A _ w2 (by omega)) (by omega)
    (fun e3 ⟨u3, w3, a3⟩ => ?_)
  refine Hs.bseq (rdW_spec (C := C) vLam (by decide) _ e3 _ p.Lambda _ w3 (by omega)) (by omega)
    (fun e4 ⟨u4, w4, a4⟩ => ?_)
  refine Hs.bseq (rdW_spec (C := C) wCo (by decide) _ e4 _ _ _ w4 (by omega)) (by omega)
    (fun e5 ⟨u5, w5, a5⟩ => ?_)
  refine Hs.bseq (setWS_spec (C := C) e5 (by rw [w5.pv, u5]; omega)) (by omega)
    (fun e8 ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ => ?_)
  have hsk2 := skW_spec (C := C) (cellN c p wt) e8 (pos2 + p.factors.length + 1 + 1 + 1) (coordsOf wt.I)
    (blocksAll wt.coef (roleCount c.kind) p.J ++ []) ⟨by rw [s3]; exact w5.ram, by rw [s4]; exact w5.rc,
      by rw [s10 wPos (by decide)]; exact w5.pv, by rw [List.append_nil]; exact w5.dr, w5.le⟩
    (by rw [s2, u5]) (by omega)
  refine Hs.bseq hsk2 (by omega) (fun e9 ⟨w9, _, a9⟩ => ?_)
  have hsl : (srList c p).length = p.J * roleCount c.kind := srList_len c p
  have hJRe9 : e9.env gJR = p.J * roleCount c.kind := by
    rw [a9.fr gJR (by decide), s10 gJR (by decide), a5.fr gJR (by decide), a4.fr gJR (by decide),
      a3.fr gJR (by decide), a2.fr gJR (by decide), DS.set_env_ne _ _ (by decide), hJR]
  have hNW : p.J * roleCount c.kind < 2 ^ C.Wd := by
    have h1 := blocksAll_eq c p wt
    have h2 : (srList c p).length ≤ ((srList c p).flatMap (blkG c wt)).length :=
      len_le_flatMap' _ _ (fun x _ => by simp [blkG])
    have h3 := congrArg List.length w9.dr
    simp only [List.length_drop, List.length_append, List.length_nil, add_zero] at h3
    rw [h1] at h3; omega
  set posB := pos2 + p.factors.length + 1 + 1 + 1 + (coordsOf wt.I).length with hposB
  let I : ℕ → DS VV MM → Prop := fun m e =>
    WSt (cellN c p wt) e (posB + (((srList c p).take m).flatMap (blkG c wt)).length)
      (((srList c p).drop m).flatMap (blkG c wt) ++ []) ∧ Agr e9 e [sN] [wY, c0, vJ, wPos, c1]
  have hl := forS_spec' (C := C) c1 gJR (by decide) blkStep e9 (p.J * roleCount c.kind) hNW I
    (10 * (cellN c p wt).length + 20)
    (fun m e v ⟨i1, i2⟩ => ⟨⟨i1.ram, i1.rc, by rw [DS.set_env_ne _ _ (by decide)]; exact i1.pv, i1.dr, i1.le⟩,
      i2.trans (Agr.set _ _ _ (by decide))⟩)
    ⟨by simp only [List.take_zero, List.flatMap_nil, List.length_nil, add_zero, List.drop_zero]
        rw [← blocksAll_eq]; exact w9, Agr.refl _ _ _⟩ hJRe9 ?_
  · refine Hs.bseq hl (by omega) (fun e10 ⟨⟨i1, i2⟩, _, _⟩ => ?_)
    rw [← hsl, List.take_length, List.drop_length, List.flatMap_nil, List.nil_append] at i1
    have hend : posB + ((srList c p).flatMap (blkG c wt)).length = (cellN c p wt).length := by
      have h1 := i1.dr
      have h2 := i1.le
      rw [List.drop_eq_nil_iff] at h1
      omega
    refine Hs.mono (hs_copy C vNL wPos e10 (by decide)) (by omega) ?_
    rintro d hd
    have hfr : ∀ y, y ∉ [wY, c0, vJ, wPos, c1, gWS, wCo, vLam, vA, vNL] → d.env y = a.env y := by
      intro y hy
      have h1 : y ≠ vNL := fun h => hy (by rw [h]; decide)
      rw [hd, DS.set_env_ne _ _ h1, i2.fr y (nmem_sub (by decide) hy), a9.fr y (nmem_sub (by decide) hy),
        s10 y (nmem_sub (by decide) hy), a5.fr y (nmem_sub (by decide) hy), a4.fr y (nmem_sub (by decide) hy),
        a3.fr y (nmem_sub (by decide) hy), a2.fr y (nmem_sub (by decide) hy),
        DS.set_env_ne _ _ (fun h => hy (by rw [h]; decide))]
    subst hd
    refine ⟨?_, ?_, ?_, ?_, ?_, by rw [DS.set_ram]; exact i1.ram, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide), i2.fr vA (by decide), a9.fr vA (by decide), s10 vA (by decide),
        a5.fr vA (by decide), a4.fr vA (by decide), u3]
    · rw [DS.set_env_ne _ _ (by decide), i2.fr vLam (by decide), a9.fr vLam (by decide), s10 vLam (by decide),
        a5.fr vLam (by decide), u4]
    · rw [DS.set_env_ne _ _ (by decide), i2.fr gWS (by decide), a9.fr gWS (by decide), s1, w5.pv, u5]
    · rw [DS.set_env_self, i1.pv, hend]
    · rw [DS.set_env_ne _ _ (by decide), i2.fr wCo (by decide), a9.fr wCo (by decide), s10 wCo (by decide), u5]
    · refine ⟨fun m hm => ?_, fun m hm => ?_, ?_, ?_, ?_, ?_, ?_, fun y hy => hfr y (nmem_sub (by decide) hy)⟩
      · rw [DS.set_ram, i2.ram m hm, a9.ram m hm, s3, a5.ram m hm, a4.ram m hm, a3.ram m hm, a2.ram m hm]; rfl
      · rw [DS.set_rc, i2.rc m hm, a9.rc m hm, s4, a5.rc m hm, a4.rc m hm, a3.rc m hm, a2.rc m hm]; rfl
      · rw [DS.set_ip, i2.ip, a9.ip, s5, a5.ip, a4.ip, a3.ip, a2.ip]; rfl
      · rw [DS.set_out, i2.out, a9.out, s6, a5.out, a4.out, a3.out, a2.out]; rfl
      · rw [DS.set_kin, i2.kin, a9.kin, s7, a5.kin, a4.kin, a3.kin, a2.kin]; rfl
      · rw [DS.set_kout, i2.kout, a9.kout, s8, a5.kout, a4.kout, a3.kout, a2.kout]; rfl
      · rw [DS.set_kc, i2.kc, a9.kc, s9, a5.kc, a4.kc, a3.kc, a2.kc]; rfl
  · intro m hm e ⟨i1, i2⟩ hem hjr
    have hm' : m < (srList c p).length := by rw [hsl]; exact hm
    rw [drop_cons_flatMap _ _ m hm', List.append_assoc] at i1
    have hle := i1.le
    have hblk : (blkG c wt (srList c p)[m]).length = 1 + 2 * (wt.coef (srList c p)[m].1 (srList c p)[m].2).length := by
      simp only [blkG, List.length_append, List.length_singleton, flatMap_intN_length]
    have hcs2 : (posB + ((List.take m (srList c p)).flatMap (blkG c wt)).length) + (1 + 2 * (wt.coef (srList c p)[m].1 (srList c p)[m].2).length)
        ≤ (cellN c p wt).length := by
      have h1 := congrArg List.length i1.dr
      rw [List.length_drop, List.length_append, hblk] at h1
      omega
    have hst := blkStep_spec (C := C) _ e _ (wt.coef (srList c p)[m].1 (srList c p)[m].2) _ i1 (by omega)
    refine Hs.mono hst (by omega) ?_
    rintro d ⟨d1, d2⟩
    refine ⟨⟨?_, i2.trans (d2.weaken (by decide) (by decide))⟩, ?_, ?_⟩
    · rw [take_succ_flatMap (srList c p) (blkG c wt) m hm', hblk, ← Nat.add_assoc, ← Nat.add_assoc]; exact d1
    · rw [d2.fr c1 (by decide), hem]
    · rw [d2.fr gJR (by decide), hjr]

end NearCubicGates.Close.Cells
