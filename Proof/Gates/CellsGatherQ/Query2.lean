import Proof.Gates.CellsGatherQ.Query1
import Proof.Gates.CellsGatherK.KeySpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.QueryPass

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter
open NearCubicGates.Close.Cells.RecordEmission (GW eG2 qScratch QPre)
open NearCubicGates.Close.Cells.QueryKey (kPC kQ kT kS kKey keyScratch KeyGoal qKey)

/-! ## The hypotheses of the pass, bundled -/

structure Hy (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) : Prop where
  spec : ∃ cT, Spec cT (header c) p
  dec : ∃ w, decodeWitness c p w = some wt
  adm : ∃ B1 B2 : ℕ, c.Admitted B1 B2
  bits : ∀ x ∈ CounterMachine.cellN c p wt, natBitLength x ≤ Big
  wd : wdNeed c p wt Big ≤ C.Wd

/-! ## Staying a `QPre` state -/

theorem QPre.step {c : Call} {p : Params} {wt : Wit c.n} {i : ℕ} {a0 d e : DS VV MM} (h : QPre c p wt i a0 d)
    (hk : RecordEmission.Ke d e) (hrc : ∀ m, e.rc m ≤ (e.ram m).length) (T : List (Fin VV))
    (hT : ∀ x ∈ T, gScratch x ∧ x ≠ eG2) (hfr : Fr d e T) : QPre c p wt i a0 e where
  pre := h.pre
  env := fun x hx => by
    by_cases hxT : x ∈ T
    · exact absurd (hT x hxT).1 hx
    · rw [hfr x hxT]; exact h.env x hx
  ram := fun m hm => (hk.ram m hm).trans (h.ram m hm)
  rcur := hrc
  ip := hk.ip.trans h.ip
  out := hk.out.trans h.out
  kin := hk.kin.trans h.kin
  kout := hk.kout.trans h.kout
  kc := hk.kc.trans h.kc
  g2 := by
    have : eG2 ∉ T := fun hm => (hT _ hm).2 rfl
    rw [hfr _ this]; exact h.g2

theorem QPre.set {c : Call} {p : Params} {wt : Wit c.n} {i : ℕ} {a0 d : DS VV MM} (h : QPre c p wt i a0 d)
    (x : Fin VV) (hx : gScratch x ∧ x ≠ eG2) (v : ℕ) : QPre c p wt i a0 (d.set x v) :=
  QPre.step h ((RecordEmission.Ke.refl d).set_r x v) (fun m => h.rcur m) [x] (by simpa using hx) (Fr.set d v (by simp))

/-- The values the pass reads, at any `QPre` state. -/
theorem QPre.vals {c : Call} {p : Params} {wt : Wit c.n} {i : ℕ} {a0 d : DS VV MM} (h : QPre c p wt i a0 d) :
    Cst d ∧ d.ram sE = ctrL c p wt (cellOf wt.I i) ∧ d.ram sN = CounterMachine.cellN c p wt ∧
    d.env vHE = p.hE ∧ d.env gJ = p.J ∧ d.env gRC = roleCount c.kind ∧ d.env vKB = 2 ^ keyBits p ∧
    d.env gKd = kindTag c.kind ∧ d.env vBN = wWin p ^ nDig c p ∧ d.env vNP = (p.primes.sort (· ≤ ·)).length ∧
    d.env vIPr = a0.env vIPr := by
  have e : ∀ x : Fin VV, ¬ gScratch x → d.env x = a0.env x := h.env
  refine ⟨⟨by rw [e vZ (by unfold gScratch; decide)]; exact h.pre.cst.z,
    by rw [e v1 (by unfold gScratch; decide)]; exact h.pre.cst.one,
    by rw [e v2 (by unfold gScratch; decide)]; exact h.pre.cst.two⟩,
    by rw [h.ram sE (by decide)]; exact h.pre.ctrs, by rw [h.ram sN (by decide)]; exact h.pre.cellN,
    by rw [e vHE (by unfold gScratch; decide)]; exact h.pre.hE, by rw [e gJ (by unfold gScratch; decide)]; exact h.pre.J,
    by rw [e gRC (by unfold gScratch; decide)]; exact h.pre.rc, by rw [e vKB (by unfold gScratch; decide)]; exact h.pre.KB,
    by rw [e gKd (by unfold gScratch; decide)]; exact h.pre.kind, by rw [e vBN (by unfold gScratch; decide)]; exact h.pre.BN,
    by rw [e vNP (by unfold gScratch; decide)]; exact h.pre.NP, e vIPr (by unfold gScratch; decide)⟩

def kList : List (Fin VV) :=
  [⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩,
    ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, t5, t6, t7, t8, t9, c0, vJ]

theorem mem_kList (x : Fin VV) (h : keyScratch x) : x ∈ kList := by
  unfold keyScratch at h
  rcases h with ⟨h1, h2⟩ | h | h | h | h | h | h | h
  · obtain ⟨v, hv⟩ := x
    simp only at h1 h2
    interval_cases v <;> simp [kList, Fin.ext_iff]
  all_goals (subst h; decide)

theorem fr_of_key {a b : DS VV MM} (h : ∀ x : Fin VV, ¬ keyScratch x → b.env x = a.env x) : Fr a b kList :=
  fun y hy => h y (fun hk => hy (mem_kList y hk))

/-! ## Bounds -/

theorem qKey_lt {cT : ℕ} {c : Call} {p : Params} (wt : Wit c.n) (y : Cells wt.I) (hs : Spec cT (header c) p)
    (part : Option Bool) (t q s : ℕ) (hpart : part ∈ parts c) (hq : q ∈ p.primes.sort (· ≤ ·))
    (ht : t < wWin p ^ nDig c p) (hsl : s < q ^ roleCount c.kind) : qKey c p wt y part t q s < 2 ^ keyW c p := by
  have hm : qKey c p wt y part t q s ∈ GatherPhase.rowKeys c p wt y := by
    rw [QueryKey.rowKeys_eq]
    simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨part, hpart, t, ht, q, hq, s, hsl, rfl⟩
  obtain ⟨id, hid, he⟩ := GatherPhase.rowKeys_mem c p wt y hs _ hm
  rw [← he]; exact reqKey_lt c p hs id hid

theorem widths (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) (hwd : wdNeed c p wt Big ≤ C.Wd) :
    2 * (valueWidth c p + keyW c p) + 2 ≤ C.Wd := by
  unfold wdNeed recWidth at hwd
  unfold keyW
  have hX : 2 ≤ 256 * (p.J + 4) * (Big + c.n + 16) := by
    have : 4 * 16 ≤ (p.J + 4) * (Big + c.n + 16) := Nat.mul_le_mul (by omega) (by omega)
    rw [Nat.mul_assoc]; omega
  generalize 256 * (p.J + 4) * (Big + c.n + 16) = X at hwd hX
  omega

/-- The record of a key and a tag fits the width. -/
theorem rec_fit (Wd vw kw key n1 : ℕ) (h : 2 * (vw + kw) + 2 ≤ Wd) (hk : key < 2 ^ kw) (hn : n1 < 2 ^ kw) :
    (2 * key + 1) * (2 ^ vw * 2 ^ kw) + n1 + 1 < 2 ^ Wd := by
  have hV : 1 ≤ 2 ^ vw := Nat.one_le_two_pow
  have h1 : (2 * key + 1) * (2 ^ vw * 2 ^ kw) + n1 + 1 ≤ 2 * 2 ^ kw * (2 ^ vw * 2 ^ kw) := by
    have e1 : 2 * key + 1 + 1 ≤ 2 * 2 ^ kw := by omega
    have e2 : (2 * key + 1 + 1) * (2 ^ vw * 2 ^ kw) ≤ 2 * 2 ^ kw * (2 ^ vw * 2 ^ kw) := Nat.mul_le_mul_right _ e1
    have e3 : 2 ^ kw ≤ 2 ^ vw * 2 ^ kw := Nat.le_mul_of_pos_left _ hV
    nlinarith
  have h2 : 2 * 2 ^ kw * (2 ^ vw * 2 ^ kw) = 2 ^ (1 + vw + 2 * kw) := by
    rw [pow_add, pow_add, pow_one, two_mul kw, pow_add]; ring
  have h3 : 2 ^ (1 + vw + 2 * kw) < 2 ^ Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-! ## One query record -/

/-- Key, then `qRec gZ kKey tag` written at the cursor of `sG`, then `tag + 1`. -/
def uB (kP : St VV MM) : St VV MM :=
  .seq kP (.seq (.op (.copy qR kKey)) (.seq (.op (.shl qR)) (.seq (.op (.inc qR)) (.seq (.op (.mul qR eG2 qX))
  (.seq (.op (.add qX qT)) (.seq (.op (.wrM sG qX)) (.op (.inc qT))))))))

def uT : List (Fin VV) := [qR, qX, qT] ++ kList

theorem uT_ok : ∀ x ∈ uT, gScratch x ∧ x ≠ eG2 := by unfold uT kList gScratch; decide

theorem uB_spec (kP : St VV MM) (kc : Ctx → Call → Params → ℕ → ℕ) (hk : KeyGoal kP kc) (C : Ctx) (c : Call)
    (p : Params) (wt : Wit c.n) (i : ℕ) (a0 : DS VV MM) (Big : ℕ) (hy : Hy C c p wt Big) (d : DS VV MM)
    (S Wc : List ℕ) (n1 : ℕ) (part : Option Bool) (t q s : ℕ) (hpart : part ∈ parts c)
    (hq : q ∈ p.primes.sort (· ≤ ·)) (ht : t < wWin p ^ nDig c p) (hsl : s < q ^ roleCount c.kind)
    (hQ : QPre c p wt i a0 d) (hG : GW d S Wc) (hT : d.env qT = n1) (hn1 : n1 < 2 ^ keyW c p)
    (hpc : d.env kPC = partCode part) (hqv : d.env kQ = q) (htv : d.env kT = t) (hsv : d.env kS = s) :
    Hs C (uB kP) d (kc C c p Big + 20) (fun e => QPre c p wt i a0 e ∧
      GW e S (Wc ++ [qRec (GatherPhase.gZ c p) (qKey c p wt (cellOf wt.I i) part t q s) n1]) ∧ e.env qT = n1 + 1 ∧
      Fr d e uT) := by
  obtain ⟨cT, hs⟩ := hy.spec
  obtain ⟨hc, hE, hN, hhE, hJ, hrc, hKB, -, -, -, -⟩ := QPre.vals hQ
  have hkey := qKey_lt wt (cellOf wt.I i) hs part t q s hpart hq ht hsl
  have hfit := rec_fit C.Wd (valueWidth c p) (keyW c p) _ n1 (widths C c p wt Big hy.wd) hkey hn1
  have hG1 : 1 ≤ 2 ^ valueWidth c p * 2 ^ keyW c p := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hK : Hs C kP d (kc C c p Big) (fun b => b.env kKey = qKey c p wt (cellOf wt.I i) part t q s ∧
      b.ram = d.ram ∧ (∀ m, m ≠ sE → b.rc m = d.rc m) ∧ b.rc sE ≤ (b.ram sE).length ∧
      b.ip = d.ip ∧ b.out = d.out ∧ b.kin = d.kin ∧ b.kout = d.kout ∧ b.kc = d.kc ∧
      (∀ x : Fin VV, ¬ keyScratch x → b.env x = d.env x)) := by
    obtain ⟨b, n, hx, hn, hb⟩ := hk C c p wt (cellOf wt.I i) d Big part q t s hs hy.dec hy.adm hy.bits hy.wd hpart hq
      ht hsl ⟨hc, hE, by rw [hE]; have := hQ.rcur sE; rw [hE] at this; exact this, hhE, hJ, hrc, hKB, hpc, hqv, htv, hsv⟩
    exact ⟨b, n, hx, hn, hb⟩
  apply Hx.hs
  refine Hs.then hK (fun b ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ m0 hm0 => ?_)
  have bG2 : b.env eG2 = 2 ^ valueWidth c p * 2 ^ keyW c p := by
    rw [b10 eG2 (by unfold keyScratch; decide)]; exact hQ.g2
  have bT : b.env qT = n1 := by rw [b10 qT (by unfold keyScratch; decide)]; exact hT
  have bGW : GW b S Wc := GW.congr hG (by rw [b2]) (b3 sG (by decide))
  have f2 : 2 * qKey c p wt (cellOf wt.I i) part t q s + 1 ≤
      (2 * qKey c p wt (cellOf wt.I i) part t q s + 1) * (2 ^ valueWidth c p * 2 ^ keyW c p) :=
    Nat.le_mul_of_pos_right _ hG1
  refine Hs.then (hs_copy C qR kKey b (by decide)) (fun e1 he1 m1 hm1 => ?_); subst he1
  refine Hs.then (hs_shl C qR _ (by vsimp [b1]; linarith)) (fun e2 he2 m2 hm2 => ?_); subst he2
  refine Hs.then (hs_inc C qR _ (by vsimp [b1]; linarith)) (fun e3 he3 m3 hm3 => ?_); subst he3
  refine Hs.then (hs_mul C qR eG2 qX _ (by decide) (by decide) (by decide) (by vsimp [b1, bG2]; linarith))
    (fun e4 he4 m4 hm4 => ?_); subst he4
  refine Hs.then (hs_add C qX qT _ (by decide) (by vsimp [b1, bG2, bT]; linarith)) (fun e5 he5 m5 hm5 => ?_)
  have v5 : e5.env qX = qRec (GatherPhase.gZ c p) (qKey c p wt (cellOf wt.I i) part t q s) n1 := by
    rw [he5]; vsimp [b1, bG2, bT]; unfold qRec GatherPhase.gZ; rw [pow_add]
  have s5 : e5.ram = b.ram ∧ e5.rc = b.rc ∧ e5.ip = b.ip ∧ e5.out = b.out ∧ e5.kin = b.kin ∧ e5.kout = b.kout ∧
      e5.kc = b.kc := by rw [he5]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have f5 : ∀ y, y ≠ qR → y ≠ qX → e5.env y = b.env y := by
    intro y h1 h2; rw [he5]; simp [DS.set, Function.update_apply, h1, h2]
  clear he5
  have g5 : GW e5 S Wc := GW.congr bGW (by rw [s5.1]) (by rw [s5.2.1])
  refine Hs.then (hs_wrM C sG qX e5 g5.len_le) (fun e6 he6 m6 hm6 => ?_); subst he6
  have g6 : GW (e5.put sG (e5.env qX)) S (Wc ++ [qRec (GatherPhase.gZ c p) (qKey c p wt (cellOf wt.I i) part t q s) n1]) := by
    have h := g5.put qX; rw [v5] at h ⊢; exact h
  have t6 : (e5.put sG (e5.env qX)).env qT = n1 := by
    rw [RecordEmission.put_env, f5 qT (by decide) (by decide), bT]
  refine Hs.last (hs_inc C qT _ (by rw [t6]; linarith)) (fun e7 he7 m7 hm7 => ?_); subst he7
  have fr : Fr d ((e5.put sG (e5.env qX)).set qT ((e5.put sG (e5.env qX)).env qT + 1)) uT := by
    intro y hy
    have h1 : y ≠ qR := fun h => hy (by subst h; decide)
    have h2 : y ≠ qX := fun h => hy (by subst h; decide)
    have h3 : y ≠ qT := fun h => hy (by subst h; decide)
    have h4 : y ∉ kList := fun h => hy (List.mem_append_right _ h)
    rw [DS.set_env_ne _ _ h3, RecordEmission.put_env, f5 y h1 h2]
    exact fr_of_key b10 y h4
  have ke : RecordEmission.Ke d ((e5.put sG (e5.env qX)).set qT ((e5.put sG (e5.env qX)).env qT + 1)) := by
    refine ⟨fun m hm => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (e5.put sG (e5.env qX)).ram m = d.ram m
      simp only [DS.put, Function.update_of_ne hm]; rw [s5.1, b2]
    · show e5.ip = d.ip; rw [s5.2.2.1, b5]
    · show e5.out = d.out; rw [s5.2.2.2.1, b6]
    · show e5.kin = d.kin; rw [s5.2.2.2.2.1, b7]
    · show e5.kout = d.kout; rw [s5.2.2.2.2.2.1, b8]
    · show e5.kc = d.kc; rw [s5.2.2.2.2.2.2, b9]
  have rc : ∀ m, ((e5.put sG (e5.env qX)).set qT ((e5.put sG (e5.env qX)).env qT + 1)).rc m ≤
      (((e5.put sG (e5.env qX)).set qT ((e5.put sG (e5.env qX)).env qT + 1)).ram m).length := by
    intro m
    by_cases hm : m = sG
    · subst hm; exact g6.len_le
    · show (e5.put sG (e5.env qX)).rc m ≤ ((e5.put sG (e5.env qX)).ram m).length
      simp only [DS.put, Function.update_of_ne hm]; rw [s5.1, s5.2.1]
      by_cases hE' : m = sE
      · subst hE'; exact b4
      · rw [b3 m hE', b2]; exact hQ.rcur m
  refine ⟨⟨QPre.step hQ ke rc uT uT_ok fr, g6, by
    show (e5.put sG (e5.env qX)).env qT + 1 = n1 + 1; rw [t6], fr⟩, by omega⟩

end NearCubicGates.Close.Cells.QueryPass
