import SourceAdapters.RAMACSP.GenTBank
import SourceAdapters.Joins.TermsCircuit

/-!
# Printing the routing items (G5 input of `Joins/TermsCircuit`)

Paper: the routing equations of `app:affine-embedding` and `lem:routing`.
The generator emits route, switch-bit, pair, column-successor and data-bit
checks at their selected host points, using the complete translation bank.

`routeP` prints the item words (`Joins.itemWord`) of `routingPairs l` in order: per item the continuation flag
`natWord 1`, the `mH` guard codes of `routePattern` (`patP`), the equation's tokens in postorder (reads as
`natWord 1 ++ natWord (b + 1)`, operations `natWord tag ++ natWord 0`), and the end token. The stage is in program
variable `50`, the column bit in `51`, the guard coordinate in `52`; the layout `k, ℓ, q` in `31, 32, 34`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters
open NearCubicWires.RepairRepresentation (natWord)

variable {G : Glob}

/-! ## The item printers -/

/-- The variables an item printer changes: the scratch `0 … 19` and the guard coordinate `52`. -/
def IW : List Var := 52 :: SW

theorem SW_sub_IW : ∀ x ∈ SW, x ∈ IW := fun x hx => List.mem_cons_of_mem _ hx

theorem IW_sub_LW : ∀ x ∈ IW, x ∈ LW := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | h
  · exact mem_LW.mpr (Or.inr (by decide))
  · exact SW_sub_LW x h

/-- `t` agrees with `s` off `IW`. -/
def AgI (s t : FS) : Prop := ∀ i : Var, i ∉ IW → t.env i = s.env i

theorem AgI.trans {s t u : FS} (h1 : AgI s t) (h2 : AgI t u) : AgI s u := fun i hi => (h2 i hi).trans (h1 i hi)

theorem AgI.of_em {s t : FS} {W : List Var} {w : List Bool} (h : Em W s t w) (hW : ∀ x ∈ W, x ∈ IW) : AgI s t :=
  fun i hi => h.env i (fun h' => hi (hW i h'))

/-- `e` has the value `x` on every state agreeing with `s` off `IW`. -/
def FixI (s : FS) (e : E) (x : ℕ) : Prop := ∀ t, AgI s t → evalE G t e = x

/-- One token: `natWord tag ++ natWord arg`. -/
def tokP (tag : ℕ) (arg : E) : S := .seq (emitNatE (.k tag)) (emitNatE arg)

/-- The read token of the bank variable `b`. -/
def rdT (b : E) : S := tokP 1 (.add b (.k 1))

/-- An operation token (`2` add, `3` mul, `4` square, `5` end). -/
def opT (tag : ℕ) : S := tokP tag (.k 0)

theorem small_ok (hK : 8 ≤ G.K) {c : ℕ} (hc : c ≤ 5) : c ≤ G.cap ∧ natBitLength c + 2 ≤ G.K := by
  have hcap := cap_add G
  have : 2 ^ 3 ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨by omega, ?_⟩
  have := natBitLength_le_of_lt (v := c) (L := 3) (by norm_num) (by omega); omega

theorem tok_spec (s0 u : FS) (hu : AgI s0 u) (tag : ℕ) (arg : E) (b : ℕ) (harg : FixI (G := G) s0 arg b)
    (htag : tag ≤ 5) (hb : natBitLength b + 2 ≤ G.K) (hK : 8 ≤ G.K) (hN : G.K ≤ G.N) :
    Em IW u (evalS G (tokP tag arg) u) (natWord tag ++ natWord b) := by
  obtain ⟨hc, hl⟩ := small_ok hK htag
  refine Em_acc ((emitNatK_spec (G := G) u tag hc hl hN).mono SW_sub_IW) (fun t1 a1 => ?_)
  have hv : evalE G t1 arg = b := harg t1 (hu.trans (AgI.of_em a1 (fun x hx => hx)))
  have h := emitNatE_spec (G := G) t1 arg (by rw [hv]; exact hb) hN
  rw [hv] at h
  exact h.mono SW_sub_IW

/-- A read token: `natWord 1 ++ natWord (b + 1)`. -/
theorem rdT_spec (s0 u : FS) (hu : AgI s0 u) (g : E) (b : ℕ) (hg : FixI (G := G) s0 g b) (m : ℕ)
    (hb : b < 2 ^ m) (hK : m + 8 ≤ G.K) (hN : G.K ≤ G.N) :
    Em IW u (evalS G (rdT g) u) (natWord 1 ++ natWord (b + 1)) := by
  have hcap := cap_add G
  have hpm : 2 ^ (m + 1) ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  refine tok_spec s0 u hu 1 _ (b + 1) (fun t ht => ?_) (by norm_num) ?_ (by omega) hN
  · have := (small_ok (G := G) (c := 1) (by omega) (by norm_num)).1
    exact eE_add (hg t ht) (eE_k this) (by omega)
  · have := natBitLength_le_of_lt (v := b + 1) (L := m + 1) (by omega) (by omega); omega

theorem opT_spec (s0 u : FS) (hu : AgI s0 u) (tag : ℕ) (htag : tag ≤ 5) (hK : 8 ≤ G.K) (hN : G.K ≤ G.N) :
    Em IW u (evalS G (opT tag) u) (natWord tag ++ natWord 0) := by
  have h0 := small_ok (G := G) hK (show 0 ≤ 5 by norm_num)
  exact tok_spec s0 u hu tag (.k 0) 0 (fun t _ => eE_k h0.1) htag h0.2 hK hN

/-! ## The guard pattern -/

/-- The guard code of coordinate `a` (in `52`) of the pattern with known mask `kn` and value mask `va`. -/
def codeE (kn va : E) : E :=
  .mul (.md (.shr kn (.v 52)) (.k 2)) (.add (.k 1) (.md (.shr va (.v 52)) (.k 2)))

/-- `mH = k + ℓ + q + 4`. -/
def mE : E := .add (.add (.add (.v 31) (.v 32)) (.v 34)) (.k 4)

/-- The guard pattern's `mH` codes. -/
def patP (kn va : E) : S := .loop 52 mE (emitNatE (codeE kn va))

/-- The code of a guard entry from the masks. -/
def gcode (K V a : ℕ) : ℕ := K / 2 ^ a % 2 * (1 + V / 2 ^ a % 2)

theorem patP_spec (s0 u : FS) (hu : AgI s0 u) (kn va : E) (K V m : ℕ) (hk : FixI (G := G) s0 kn K)
    (hv : FixI (G := G) s0 va V) (hm : FixI (G := G) s0 mE m) (hK : 8 ≤ G.K) (hN : G.K ≤ G.N) (hmN : m ≤ G.N) :
    Em IW u (evalS G (patP kn va) u) ((List.range m).flatMap (fun a => natWord (gcode K V a))) := by
  have hcap := cap_add G
  have h8 : 2 ^ 3 ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine (Em_loop 52 mE (emitNatE (codeE kn va)) IW (List.mem_cons_self) u m
    (by rw [hm u hu]; exact min_eq_left hmN) (fun t => AgI s0 t) hu (fun a => natWord (gcode K V a))
    (fun a ha t ht te => ?_)).2
  have h52 : AgI s0 (t.setv 52 a) := fun i hi => by
    simp only [FS.setv_env, Function.update_apply]
    rw [if_neg (show i ≠ 52 from fun e => hi (by rw [e]; exact List.mem_cons_self))]; exact ht i hi
  have hb1 : K / 2 ^ a % 2 ≤ 1 := by have := Nat.mod_lt (K / 2 ^ a) (show 0 < 2 by norm_num); omega
  have hb2 : V / 2 ^ a % 2 ≤ 1 := by have := Nat.mod_lt (V / 2 ^ a) (show 0 < 2 by norm_num); omega
  have h2 := (small_ok (G := G) (c := 2) hK (by norm_num)).1
  have h1 := (small_ok (G := G) (c := 1) hK (by norm_num)).1
  have e52 : evalE G (t.setv 52 a) (.v 52) = a := by simp [eE_v]
  have ev : evalE G (t.setv 52 a) (codeE kn va) = gcode K V a := by
    unfold codeE gcode
    have eA := eE_md (eE_shr (hk _ h52) e52) (eE_k h2)
    have eB := eE_md (eE_shr (hv _ h52) e52) (eE_k h2)
    have eC := eE_add (eE_k h1) eB (by omega)
    exact eE_mul eA eC (by have := Nat.mul_le_mul hb1 (show 1 + V / 2 ^ a % 2 ≤ 2 by omega); omega)
  have hg : gcode K V a ≤ 2 := by
    unfold gcode; have := Nat.mul_le_mul hb1 (show 1 + V / 2 ^ a % 2 ≤ 2 by omega); omega
  have hl := (small_ok (G := G) (c := gcode K V a) hK (by omega)).2
  have h := emitNatE_spec (G := G) (t.setv 52 a) (codeE kn va) (by rw [ev]; exact hl) hN
  rw [ev] at h
  exact ⟨h52.trans (AgI.of_em h SW_sub_IW), h.mono SW_sub_IW⟩

/-- One item: the flag `1`, the guard, the tokens `toks`, the end token. -/
def itemP (kn va : E) (toks : S) : S := .seq (emitNatE (.k 1)) (.seq (patP kn va) (.seq toks (opT 5)))

theorem itemP_spec (s0 u : FS) (hu : AgI s0 u) (kn va : E) (K V m : ℕ) (hk : FixI (G := G) s0 kn K)
    (hv : FixI (G := G) s0 va V) (hm : FixI (G := G) s0 mE m) (toks : S) (w : List Bool)
    (ht : ∀ t, AgI s0 t → Em IW t (evalS G toks t) w) (hK : 8 ≤ G.K) (hN : G.K ≤ G.N) (hmN : m ≤ G.N) :
    Em IW u (evalS G (itemP kn va toks) u)
      (natWord 1 ++ ((List.range m).flatMap (fun a => natWord (gcode K V a)) ++ (w ++ (natWord 5 ++ natWord 0)))) := by
  obtain ⟨hc, hl⟩ := small_ok (G := G) hK (show 1 ≤ 5 by norm_num)
  refine Em_acc ((emitNatK_spec (G := G) u 1 hc hl hN).mono SW_sub_IW) (fun t1 a1 => ?_)
  have u1 : AgI s0 t1 := hu.trans (AgI.of_em a1 (fun x hx => hx))
  refine Em_acc (patP_spec s0 t1 u1 kn va K V m hk hv hm hK hN hmN) (fun t2 a2 => ?_)
  have u2 : AgI s0 t2 := u1.trans (AgI.of_em a2 (fun x hx => hx))
  refine Em_acc (ht t2 u2) (fun t3 a3 => ?_)
  exact opT_spec s0 t3 (u2.trans (AgI.of_em a3 (fun x hx => hx))) 5 le_rfl hK hN

/-! ## Token lists -/

/-- A sequence of printers. -/
def seqL : List S → S
  | [] => .skip
  | a :: l => .seq a (seqL l)

theorem seqL_spec (s0 : FS) : ∀ (ps : List (S × TermTok)) (u : FS), AgI s0 u →
    (∀ p ∈ ps, ∀ t, AgI s0 t → Em IW t (evalS G p.1 t) (termTokWord p.2)) →
    Em IW u (evalS G (seqL (ps.map Prod.fst)) u) ((ps.map Prod.snd).flatMap termTokWord)
  | [], u, _, _ => ⟨fun _ _ => rfl, by simp [dbl, seqL, evalS], rfl, rfl, rfl, rfl⟩
  | p :: ps, u, hu, h => by
    simp only [List.map_cons, seqL, List.flatMap_cons]
    refine Em_acc (h p (by simp) u hu) (fun t1 a1 => ?_)
    exact seqL_spec s0 ps t1 (hu.trans (AgI.of_em a1 (fun x hx => hx))) (fun q hq => h q (by simp [hq]))

/-! ## The context of an item: layout, stage `j` in `50`, column bit `tt` in `51` -/

structure ICtx (l : Routing.Layout) (j tt : ℕ) (s : FS) : Prop where
  lv : LV l s
  j : s.env 50 = j
  t : s.env 51 = tt

theorem ICtx.ag {l : Routing.Layout} {j tt : ℕ} {s t : FS} (h : ICtx l j tt s) (ht : AgI s t) : ICtx l j tt t :=
  ⟨⟨(ht 31 (by decide)).trans h.lv.k, (ht 32 (by decide)).trans h.lv.ell, (ht 34 (by decide)).trans h.lv.q⟩,
    (ht 50 (by decide)).trans h.j, (ht 51 (by decide)).trans h.t⟩

section Masks

variable {l : Routing.Layout} {j tt : ℕ} {s0 : FS} (hc : ICtx l j tt s0) (hK : l.m + 8 ≤ G.K)
include hc hK

theorem fix_m : FixI (G := G) s0 mE l.m := fun t ht => by
  have lv := (hc.ag ht).lv
  have hm : l.m = l.k + l.ell + l.q + 4 := rfl
  have h4 := (small_ok (G := G) (c := 4) (by omega) (by norm_num)).1
  have hcap := cap_add G
  have hmK : l.m < 2 ^ G.K := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold mE
  rw [eE_add (eE_add (eE_add (by rw [eE_v, lv.k]) (by rw [eE_v, lv.ell]) (by omega)) (by rw [eE_v, lv.q]) (by omega))
    (eE_k h4) (by omega)]
  rfl

/-- The known mask of the stage patterns: `cellMask l 0 (2^ℓ − 1) ck 7 1`. -/
def knE (ck : E) : E := cellE (.k 0) (.sub (two (.v 32)) (.k 1)) ck (.k 7) (.k 1)

/-- The value mask: `cellMask l 0 j cv role 0`. -/
def vaE (cv : E) (role : ℕ) : E := cellE (.k 0) (.v 50) cv (.k role) (.k 0)

theorem fix_kn (ck : E) (c : ℕ) (hck : FixI (G := G) s0 ck c) (hcC : c < l.C) :
    FixI (G := G) s0 (knE ck) (Routing.cellMask l 0 (2 ^ l.ell - 1) c 7 1) ∧
      Routing.cellMask l 0 (2 ^ l.ell - 1) c 7 1 < 2 ^ l.m := by
  refine ⟨fun t ht => ?_, ?_⟩
  · have lv := (hc.ag ht).lv
    have hℓ : evalE G t (.sub (two (.v 32)) (.k 1)) = 2 ^ l.ell - 1 :=
      eE_sub (eE_two (by rw [eE_v, lv.ell]) (by unfold Routing.Layout.m at hK; omega)) (k_val hK (one_lt_m l))
    exact (cell_val lv hK hℓ (hck t ht) (k_val hK (small_lt_m l (by norm_num))) 1 (.k 1) (k_val hK (one_lt_m l))
      ⟨Nat.two_pow_pos _, by have := Nat.one_le_two_pow (n := l.ell); omega, hcC, by norm_num, by norm_num⟩).1
  · exact Routing.LayoutFacts.cellMask_lt l 0 _ c 7 1
      ⟨Nat.two_pow_pos _, by have := Nat.one_le_two_pow (n := l.ell); omega, hcC, by norm_num, by norm_num⟩

theorem fix_va (cv : E) (c : ℕ) (hcv : FixI (G := G) s0 cv c) (hcC : c < l.C) (role : ℕ) (hr : role < 8)
    (hj : j < 2 ^ l.ell) :
    FixI (G := G) s0 (vaE cv role) (Routing.cellMask l 0 j c role 0) ∧ Routing.cellMask l 0 j c role 0 < 2 ^ l.m := by
  refine ⟨fun t ht => ?_, ?_⟩
  · have hct := hc.ag ht
    exact (cell_val hct.lv hK (by rw [eE_v, hct.j]) (hcv t ht) (k_val hK (small_lt_m l (by omega))) 0 (.k 0) (k0 hK)
      ⟨Nat.two_pow_pos _, hj, hcC, hr, by norm_num⟩).1
  · exact Routing.LayoutFacts.cellMask_lt l 0 j c role 0 ⟨Nat.two_pow_pos _, hj, hcC, hr, by norm_num⟩

omit hc in
theorem fix_k (c : ℕ) (hcm : c < 2 ^ l.m) : FixI (G := G) s0 (.k c) c := fun t _ => k_val hK hcm

end Masks

/-! ## The guard words -/

theorem guardCode_mask (K V a : ℕ) :
    guardCode (if K.testBit a then some (V.testBit a) else none) = gcode K V a := by
  unfold gcode
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (K / 2 ^ a) with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (V / 2 ^ a) with h2 | h2 <;> simp [h1, h2, guardCode]

theorem ofFn_eq_range {α : Type} (m : ℕ) (g : Fin m → α) (f : ℕ → α) (h : ∀ a : Fin m, g a = f a.val) :
    List.ofFn g = (List.range m).map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact h ⟨i, by simpa using h1⟩

theorem patternWord_route (l : Routing.Layout) (j role ck cv : ℕ) :
    patternWord (Routing.routePattern l j role ck cv) = (List.range l.m).flatMap
      (fun a => natWord (gcode (Routing.cellMask l 0 (2 ^ l.ell - 1) ck 7 1) (Routing.cellMask l 0 j cv role 0) a)) := by
  unfold patternWord
  rw [ofFn_eq_range l.m (Routing.routePattern l j role ck cv) (fun a => if (Routing.cellMask l 0 (2 ^ l.ell - 1) ck 7 1).testBit a
      then some ((Routing.cellMask l 0 j cv role 0).testBit a) else none) (fun a => rfl), List.flatMap_map]
  simp only [guardCode_mask]

/-! ## One stage item -/

theorem stageItem_spec {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (x : Routing.RoutingItem)
    {l : Routing.Layout} {j tt : ℕ} {s0 : FS} (hc : ICtx l j tt s0) (hK : l.m + 8 ≤ G.K) (hKN : G.K ≤ G.N)
    (hmN : l.m ≤ G.N) (u : FS) (hu : AgI s0 u) (ck cv : E) (c1 c2 role : ℕ) (hck : FixI (G := G) s0 ck c1)
    (hcv : FixI (G := G) s0 cv c2) (hc1 : c1 < l.C) (hc2 : c2 < l.C) (hr : role < 8) (hj : j < 2 ^ l.ell)
    (TL : List (S × TermTok)) (hTL : ∀ p ∈ TL, ∀ t, AgI s0 t → Em IW t (evalS G p.1 t) (termTokWord p.2))
    (hg : x.guard l = Routing.routePattern l j role c1 c2) (he : exprToks mk (x.expr (F := F) l) = TL.map Prod.snd) :
    Em IW u (evalS G (itemP (knE ck) (vaE cv role) (seqL (TL.map Prod.fst))) u)
      (itemWord mk (x.guard l, x.expr (F := F) l)) := by
  have hK8 : 8 ≤ G.K := by omega
  obtain ⟨fk, -⟩ := fix_kn hc hK ck c1 hck hc1
  obtain ⟨fv, -⟩ := fix_va hc hK cv c2 hcv hc2 role hr hj
  have h := itemP_spec s0 u hu _ _ _ _ l.m fk fv (fix_m hc hK) _ _
    (fun t ht => seqL_spec s0 TL t ht hTL) hK8 hKN hmN
  unfold itemWord exprWord
  rw [hg, he, patternWord_route]
  simpa only [List.append_assoc] using h

/-! ## The values read by the routing items -/

section Reads

variable {l : Routing.Layout} {j tt : ℕ} {s0 : FS} (hc : ICtx l j tt s0) (hK : l.m + 8 ≤ G.K)
include hc hK

theorem fix_sd (hj : j < 2 * l.k - 1) :
    FixI (G := G) s0 sdE (Routing.stageDelta l j) ∧ Routing.stageDelta l j < 2 ^ l.m := by
  have hfit := l.stages_fit
  have hj1 : j + 1 < 2 ^ l.ell := by omega
  refine ⟨fun t ht => ?_, ?_⟩
  · have h := hc.ag ht; exact (sd_val h.lv hK h.j hj1).1
  · exact (sd_val hc.lv hK hc.j hj1).2

theorem fix_sdx (hj : j < 2 * l.k - 1) :
    FixI (G := G) s0 (.bxor sdE (two dimE)) (Routing.stageDelta l j ^^^ 2 ^ Routing.dimension l.k j) ∧
      Routing.stageDelta l j ^^^ 2 ^ Routing.dimension l.k j < 2 ^ l.m := by
  have hfit := l.stages_fit
  have hj1 : j + 1 < 2 ^ l.ell := by omega
  have hd : Routing.dimension l.k j < l.k := by unfold Routing.dimension; omega
  have hkm : l.k < l.m := by unfold Routing.Layout.m; omega
  have hp : 2 ^ Routing.dimension l.k j < 2 ^ l.m := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine ⟨fun t ht => ?_, Nat.xor_lt_two_pow (sd_val hc.lv hK hc.j hj1).2 hp⟩
  have h := hc.ag ht
  obtain ⟨e1, l1⟩ := sd_val h.lv hK h.j hj1
  exact eE_bxor e1 (eE_two (dim_val h.lv hK h.j hj) (by omega)) (lt_K_of_m hK l1) (lt_K_of_m hK hp)

theorem fix_eta (r : ℕ) (hr : r < 8) : FixI (G := G) s0 (etaE r) (Routing.eta l r) ∧ Routing.eta l r < 2 ^ l.m :=
  ⟨fun t ht => (eta_val (hc.ag ht).lv hK r hr).1, (eta_val hc.lv hK r hr).2⟩

omit hc in
theorem fix_xor {a b : E} {x y : ℕ} (ha : FixI (G := G) s0 a x ∧ x < 2 ^ l.m) (hb : FixI (G := G) s0 b y ∧ y < 2 ^ l.m) :
    FixI (G := G) s0 (.bxor a b) (x ^^^ y) ∧ x ^^^ y < 2 ^ l.m :=
  ⟨fun t ht => eE_bxor (ha.1 t ht) (hb.1 t ht) (lt_K_of_m hK ha.2) (lt_K_of_m hK hb.2), Nat.xor_lt_two_pow ha.2 hb.2⟩

theorem fix_pairx (hj : j < 2 * l.k - 1) :
    FixI (G := G) s0 (.bxor (.bxor (etaE 4) (etaE 1)) (two dimE))
      (Routing.eta l 4 ^^^ Routing.eta l 1 ^^^ 2 ^ Routing.dimension l.k j) ∧
      Routing.eta l 4 ^^^ Routing.eta l 1 ^^^ 2 ^ Routing.dimension l.k j < 2 ^ l.m := by
  have hd : Routing.dimension l.k j < l.k := by unfold Routing.dimension; omega
  have hkm : l.k < l.m := by unfold Routing.Layout.m; omega
  have hp : 2 ^ Routing.dimension l.k j < 2 ^ l.m := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine fix_xor hK (fix_xor hK (fix_eta hc hK 4 (by norm_num)) (fix_eta hc hK 1 (by norm_num))) ⟨fun t ht => ?_, hp⟩
  have h := hc.ag ht
  exact eE_two (dim_val h.lv hK h.j hj) (by omega)

/-- `2^(t+1) − 1` with `t` in `51`. -/
def carry51 : E := .sub (two (.add (.v 51) (.k 1))) (.k 1)

theorem fix_carry51 (htt : tt < l.q) : FixI (G := G) s0 carry51 (2 ^ (tt + 1) - 1) := fun t ht => by
  have h := hc.ag ht
  have hqm : l.q + 1 < l.m := by unfold Routing.Layout.m; have := l.k_pos; omega
  have hp : 2 ^ (tt + 1) < 2 ^ l.m := Nat.pow_lt_pow_right (by norm_num) (by omega)
  unfold carry51
  exact eE_sub (eE_two (eE_add (by rw [eE_v, h.t]) (k_val hK (one_lt_m l)) (cap_ge_m hK (by
    have := Nat.lt_two_pow_self (n := tt + 1); omega))) (by omega)) (k_val hK (one_lt_m l))

/-- The column carry `columnCarry l t` (`t` in `51`). -/
def ccE : E := cellE (.k 0) (.k 0) carry51 (.k 0) (.k 0)

theorem fix_cc (htt : tt < l.q) : FixI (G := G) s0 ccE (Routing.columnCarry l tt) ∧ Routing.columnCarry l tt < 2 ^ l.m := by
  have hcC : 2 ^ (tt + 1) - 1 < l.C := by
    show 2 ^ (tt + 1) - 1 < 2 ^ l.q
    have : 2 ^ (tt + 1) ≤ 2 ^ l.q := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.one_le_two_pow (n := tt + 1); omega
  have hin : Routing.InRange l 0 0 (2 ^ (tt + 1) - 1) 0 0 := ⟨Nat.two_pow_pos _, Nat.two_pow_pos _, hcC, by norm_num, by norm_num⟩
  refine ⟨fun t ht => ?_, Routing.LayoutFacts.cellMask_lt l 0 0 _ 0 0 hin⟩
  have h := hc.ag ht
  exact (cell_val h.lv hK (k0 hK) (fix_carry51 hc hK htt t ht) (k0 hK) 0 (.k 0) (k0 hK) hin).1

/-- The value column of a column item: `2^t − 1`. -/
def cvE : E := .sub (two (.v 51)) (.k 1)

/-- The known column of a column item: `2^(t+1) − 1` if `t + 1 < q`, else `2^t − 1`. -/
def ckE : E := .add (.mul (.lt (.add (.v 51) (.k 1)) (.v 34)) carry51)
  (.mul (.sub (.k 1) (.lt (.add (.v 51) (.k 1)) (.v 34))) cvE)

theorem fix_cv (htt : tt < l.q) : FixI (G := G) s0 cvE (2 ^ tt - 1) := fun t ht => by
  have h := hc.ag ht
  have hqm : l.q + 1 < l.m := by unfold Routing.Layout.m; have := l.k_pos; omega
  exact eE_sub (eE_two (by rw [eE_v, h.t]) (by omega)) (k_val hK (one_lt_m l))

theorem fix_ck (htt : tt < l.q) :
    FixI (G := G) s0 ckE (if tt + 1 < l.q then 2 ^ (tt + 1) - 1 else 2 ^ tt - 1) := fun t ht => by
  have h := hc.ag ht
  have hqm : l.q + 1 < l.m := by unfold Routing.Layout.m; have := l.k_pos; omega
  have hp1 : 2 ^ (tt + 1) < 2 ^ l.m := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hp0 : 2 ^ tt < 2 ^ l.m := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have e1 : evalE G t (.add (.v 51) (.k 1)) = tt + 1 :=
    eE_add (by rw [eE_v, h.t]) (k_val hK (one_lt_m l)) (cap_ge_m hK (by have := Nat.lt_two_pow_self (n := tt + 1); omega))
  have elt := eE_lt (G := G) (s := t) e1 (show evalE G t (.v 34) = l.q by rw [eE_v, h.lv.q])
  have ec := fix_carry51 hc hK htt t ht
  have ev := fix_cv hc hK htt t ht
  have hpos := Nat.two_pow_pos l.m
  unfold ckE
  split_ifs with hlt
  · rw [if_pos hlt] at elt
    have m1 := eE_mul elt ec (cap_ge_m hK (by rw [Nat.one_mul]; omega))
    have s1 := eE_sub (k_val (G := G) (t := t) hK (one_lt_m l)) elt
    have m2 := eE_mul s1 ev (cap_ge_m hK (by rw [Nat.sub_self, Nat.zero_mul]; omega))
    rw [eE_add m1 m2 (cap_ge_m hK (by rw [Nat.one_mul, Nat.sub_self, Nat.zero_mul]; omega))]
    simp
  · rw [if_neg hlt] at elt
    have m1 := eE_mul elt ec (cap_ge_m hK (by rw [Nat.zero_mul]; omega))
    have s1 := eE_sub (k_val (G := G) (t := t) hK (one_lt_m l)) elt
    have m2 := eE_mul s1 ev (cap_ge_m hK (by rw [Nat.sub_zero, Nat.one_mul]; omega))
    rw [eE_add m1 m2 (cap_ge_m hK (by rw [Nat.zero_mul, Nat.sub_zero, Nat.one_mul]; omega))]
    simp

end Reads

/-! ## The token lists of the five item kinds (postorder of `RoutingItem.expr`) -/

/-- `η₃ + η₁`. -/
def e31E : E := .bxor (etaE 3) (etaE 1)
/-- `η₄ + η₁`. -/
def e41E : E := .bxor (etaE 4) (etaE 1)
/-- `η₄ + η₁ + 2^dim`. -/
def e41xE : E := .bxor (.bxor (etaE 4) (etaE 1)) (two dimE)

def routeTL (l : Routing.Layout) (j : ℕ) : List (S × TermTok) :=
  [(rdT (.k 0), .read (some 0)), (rdT sdE, .read (some (Routing.stageDelta l j))), (opT 2, .add),
   (rdT (etaE 1), .read (some (Routing.eta l 1))), (rdT sdE, .read (some (Routing.stageDelta l j))),
   (rdT (.bxor sdE (two dimE)), .read (some (Routing.stageDelta l j ^^^ 2 ^ Routing.dimension l.k j))),
   (opT 2, .add), (opT 3, .mul), (opT 2, .add)]

def routeS : List S :=
  [rdT (.k 0), rdT sdE, opT 2, rdT (etaE 1), rdT sdE, rdT (.bxor sdE (two dimE)), opT 2, opT 3, opT 2]

def switchTL (l : Routing.Layout) : List (S × TermTok) :=
  [(rdT e31E, .read (some (Routing.eta l 3 ^^^ Routing.eta l 1))), (opT 4, .square),
   (rdT e31E, .read (some (Routing.eta l 3 ^^^ Routing.eta l 1))), (opT 2, .add)]

def switchS : List S := [rdT e31E, opT 4, rdT e31E, opT 2]

def pairTL (l : Routing.Layout) (j : ℕ) : List (S × TermTok) :=
  [(rdT e41E, .read (some (Routing.eta l 4 ^^^ Routing.eta l 1))),
   (rdT e41xE, .read (some (Routing.eta l 4 ^^^ Routing.eta l 1 ^^^ 2 ^ Routing.dimension l.k j))), (opT 2, .add)]

def pairS : List S := [rdT e41E, rdT e41xE, opT 2]

def colTL (l : Routing.Layout) (tt : ℕ) : List (S × TermTok) :=
  [(rdT (.k 0), .read (some 0)), (rdT ccE, .read (some (Routing.columnCarry l tt))), (opT 2, .add)]

def colS : List S := [rdT (.k 0), rdT ccE, opT 2]

def dataTL (l : Routing.Layout) : List (S × TermTok) :=
  [(rdT (etaE 2), .read (some (Routing.eta l 2))), (opT 4, .square), (rdT (etaE 2), .read (some (Routing.eta l 2))),
   (opT 2, .add)]

def dataS : List S := [rdT (etaE 2), opT 4, rdT (etaE 2), opT 2]

/-! ## The routing printer -/

/-- The items of stage `j` (in `50`): route, switch bit, pair, then the `q` column items (column bit in `51`). -/
def stageBody : S :=
  .seq (itemP (knE (.k 0)) (vaE (.k 0) 0) (seqL routeS)) (.seq (itemP (knE (.k 0)) (vaE (.k 0) 3) (seqL switchS))
    (.seq (itemP (knE (.k 0)) (vaE (.k 0) 4) (seqL pairS)) (.loop 51 (.v 34) (itemP (knE ckE) (vaE cvE 1) (seqL colS)))))

/-- **The routing printer**: the stage items for `j < 2k − 1`, then the data-bit items for `j < 2k`. -/
def routeP : S :=
  .seq (.loop 50 (.sub (.mul (.k 2) (.v 31)) (.k 1)) stageBody)
    (.loop 50 (.mul (.k 2) (.v 31)) (itemP (knE (.k 0)) (vaE (.k 0) 2) (seqL dataS)))

section Spec

variable {F : Type} [Field F] [CharP F 2] (mk : F → ℕ)

/-- The item word of a routing item. -/
abbrev rWord (l : Routing.Layout) (x : Routing.RoutingItem) : List Bool := itemWord mk (x.guard l, x.expr (F := F) l)

theorem rd_tok {l : Routing.Layout} {s0 : FS} {g : E} {b : ℕ} (hg : FixI (G := G) s0 g b ∧ b < 2 ^ l.m)
    (hK : l.m + 8 ≤ G.K) (hKN : G.K ≤ G.N) :
    ∀ t, AgI s0 t → Em IW t (evalS G (rdT g) t) (termTokWord (.read (some b))) :=
  fun t ht => rdT_spec s0 t ht g b hg.1 l.m hg.2 hK hKN

theorem op_tok {s0 : FS} (tag : ℕ) (tok : TermTok) (htok : termTokWord tok = natWord tag ++ natWord 0) (htag : tag ≤ 5)
    (hK : 8 ≤ G.K) (hKN : G.K ≤ G.N) :
    ∀ t, AgI s0 t → Em IW t (evalS G (opT tag) t) (termTokWord tok) :=
  fun t ht => htok ▸ opT_spec s0 t ht tag htag hK hKN

theorem zero_fix {l : Routing.Layout} {s0 : FS} (hK : l.m + 8 ≤ G.K) : FixI (G := G) s0 (.k 0) 0 ∧ 0 < 2 ^ l.m :=
  ⟨fix_k hK 0 (Nat.two_pow_pos _), Nat.two_pow_pos _⟩

theorem col_lt {l : Routing.Layout} {tt : ℕ} (htt : tt < l.q) :
    (if tt + 1 < l.q then 2 ^ (tt + 1) - 1 else 2 ^ tt - 1) < l.C ∧ 2 ^ tt - 1 < l.C := by
  show _ < 2 ^ l.q ∧ _ < 2 ^ l.q
  have h0 : 2 ^ tt < 2 ^ l.q := Nat.pow_lt_pow_right (by norm_num) htt
  have h1 := Nat.two_pow_pos tt
  refine ⟨?_, by omega⟩
  split_ifs with h
  · have : 2 ^ (tt + 1) ≤ 2 ^ l.q := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.one_le_two_pow (n := tt + 1); omega
  · omega

/-- The column items of stage `j` (column bit `tt` in `51`). -/
theorem colItem_spec (l : Routing.Layout) (j tt : ℕ) (hj : j < 2 * l.k - 1) (htt : tt < l.q) (s0 : FS)
    (hc : ICtx l j tt s0) (hK : l.m + 8 ≤ G.K) (hKN : G.K ≤ G.N) (hmN : l.m ≤ G.N) :
    Em IW s0 (evalS G (itemP (knE ckE) (vaE cvE 1) (seqL colS)) s0) (rWord mk l (.column j tt)) := by
  have hK8 : 8 ≤ G.K := by omega
  have hfit := l.stages_fit
  have hjℓ : j < 2 ^ l.ell := by omega
  have z := zero_fix (G := G) (s0 := s0) hK
  exact stageItem_spec mk (.column j tt) hc hK hKN hmN s0 (fun _ _ => rfl) ckE cvE _ _ 1 (fix_ck hc hK htt)
    (fix_cv hc hK htt) (col_lt htt).1 (col_lt htt).2 (by norm_num) hjℓ (colTL l tt) (by
      intro p hp
      simp only [colTL, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact rd_tok z hK hKN
      · exact rd_tok (fix_cc hc hK htt) hK hKN
      · exact op_tok 2 .add rfl (by norm_num) hK8 hKN) rfl rfl

theorem stageBody_spec (l : Routing.Layout) (j : ℕ) (hj : j < 2 * l.k - 1) (s1 : FS) (hl : LV l s1)
    (h50 : s1.env 50 = j) (hK : l.m + 8 ≤ G.K) (hKN : G.K ≤ G.N) (hqN : l.q ≤ G.N) (hmN : l.m ≤ G.N) :
    Em LW s1 (evalS G stageBody s1) (rWord mk l (.route j) ++ (rWord mk l (.switchBit j) ++ (rWord mk l (.pair j) ++
      (List.range l.q).flatMap (fun tt => rWord mk l (.column j tt))))) := by
  have hK8 : 8 ≤ G.K := by omega
  have hfit := l.stages_fit
  have hjℓ : j < 2 ^ l.ell := by omega
  have hC : 0 < l.C := Nat.two_pow_pos _
  have hc : ICtx l j (s1.env 51) s1 := ⟨hl, h50, rfl⟩
  have z := zero_fix (G := G) (s0 := s1) hK
  -- route
  have E1 := stageItem_spec mk (.route j) hc hK hKN hmN s1 (fun _ _ => rfl) (.k 0) (.k 0) 0 0 0 z.1 z.1 hC hC
    (by norm_num) hjℓ (routeTL l j) (by
      intro p hp
      simp only [routeTL, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact rd_tok z hK hKN
      · exact rd_tok (fix_sd hc hK hj) hK hKN
      · exact op_tok 2 .add rfl (by norm_num) hK8 hKN
      · exact rd_tok (fix_eta hc hK 1 (by norm_num)) hK hKN
      · exact rd_tok (fix_sd hc hK hj) hK hKN
      · exact rd_tok (fix_sdx hc hK hj) hK hKN
      · exact op_tok 2 .add rfl (by norm_num) hK8 hKN
      · exact op_tok 3 .mul rfl (by norm_num) hK8 hKN
      · exact op_tok 2 .add rfl (by norm_num) hK8 hKN) rfl rfl
  generalize hu1 : evalS G (itemP (knE (.k 0)) (vaE (.k 0) 0) (seqL ((routeTL l j).map Prod.fst))) s1 = u1 at E1
  have g1 : AgI s1 u1 := AgI.of_em E1 (fun x hx => hx)
  -- switch bit
  have E2 := stageItem_spec mk (.switchBit j) hc hK hKN hmN u1 g1 (.k 0) (.k 0) 0 0 3 z.1 z.1 hC hC
    (by norm_num) hjℓ (switchTL l) (by
      intro p hp
      simp only [switchTL, List.mem_cons, List.not_mem_nil, or_false] at hp
      have e := fix_xor hK (fix_eta hc hK 3 (by norm_num)) (fix_eta hc hK 1 (by norm_num))
      rcases hp with rfl | rfl | rfl | rfl
      · exact rd_tok e hK hKN
      · exact op_tok 4 .square rfl (by norm_num) hK8 hKN
      · exact rd_tok e hK hKN
      · exact op_tok 2 .add rfl (by norm_num) hK8 hKN) rfl rfl
  generalize hu2 : evalS G (itemP (knE (.k 0)) (vaE (.k 0) 3) (seqL ((switchTL l).map Prod.fst))) u1 = u2 at E2
  have g2 : AgI s1 u2 := g1.trans (AgI.of_em E2 (fun x hx => hx))
  -- pair
  have E3 := stageItem_spec mk (.pair j) hc hK hKN hmN u2 g2 (.k 0) (.k 0) 0 0 4 z.1 z.1 hC hC
    (by norm_num) hjℓ (pairTL l j) (by
      intro p hp
      simp only [pairTL, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact rd_tok (fix_xor hK (fix_eta hc hK 4 (by norm_num)) (fix_eta hc hK 1 (by norm_num))) hK hKN
      · exact rd_tok (fix_pairx hc hK hj) hK hKN
      · exact op_tok 2 .add rfl (by norm_num) hK8 hKN) rfl rfl
  generalize hu3 : evalS G (itemP (knE (.k 0)) (vaE (.k 0) 4) (seqL ((pairTL l j).map Prod.fst))) u2 = u3 at E3
  have g3 : AgI s1 u3 := g2.trans (AgI.of_em E3 (fun x hx => hx))
  -- the column loop
  have lv3 : LV l u3 := (hc.ag g3).lv
  have E4 := (Em_loop 51 (.v 34) (itemP (knE ckE) (vaE cvE 1) (seqL colS)) LW (mem_LW.mpr (Or.inr (by decide))) u3 l.q
    (by rw [eE_v, lv3.q]; exact min_eq_left hqN) (fun t => (∀ i : Var, i ∉ LW → t.env i = s1.env i) ∧ t.env 50 = j)
    ⟨fun i hi => g3 i (fun h => hi (IW_sub_LW i h)), (hc.ag g3).j⟩ (fun tt => rWord mk l (.column j tt))
    (fun tt htt t ⟨ht, ht50⟩ te => ?_)).2
  · have hs : evalS G stageBody s1 = evalS G (.loop 51 (.v 34) (itemP (knE ckE) (vaE cvE 1) (seqL colS))) u3 := by
      rw [← hu3, ← hu2, ← hu1]; rfl
    rw [hs]
    exact (E1.mono IW_sub_LW).trans ((E2.mono IW_sub_LW).trans ((E3.mono IW_sub_LW).trans E4))
  · have hct : ICtx l j tt (t.setv 51 tt) := ⟨lv_of hl (fun i hi => by
        simp only [FS.setv_env, Function.update_apply]
        rw [if_neg (show i ≠ 51 from fun e => hi (by rw [e]; exact mem_LW.mpr (Or.inr (by decide))))]; exact ht i hi),
      by simp only [FS.setv_env, Function.update_apply]; rw [if_neg (by decide)]; exact ht50, by simp⟩
    have E := colItem_spec mk l j tt hj htt (t.setv 51 tt) hct hK hKN hmN
    refine ⟨⟨fun i hi => ?_, ?_⟩, E.mono IW_sub_LW⟩
    · rw [E.env i (fun h => hi (IW_sub_LW i h))]
      simp only [FS.setv_env, Function.update_apply]
      rw [if_neg (show i ≠ 51 from fun e => hi (by rw [e]; exact mem_LW.mpr (Or.inr (by decide))))]; exact ht i hi
    · rw [E.env 50 (by decide)]; exact hct.j

theorem dataItem_spec (l : Routing.Layout) (j : ℕ) (hj : j < 2 * l.k) (s0 : FS) (hl : LV l s0)
    (h50 : s0.env 50 = j) (hK : l.m + 8 ≤ G.K) (hKN : G.K ≤ G.N) (hmN : l.m ≤ G.N) :
    Em IW s0 (evalS G (itemP (knE (.k 0)) (vaE (.k 0) 2) (seqL dataS)) s0) (rWord mk l (.dataBit j)) := by
  have hK8 : 8 ≤ G.K := by omega
  have hfit := l.stages_fit
  have hjℓ : j < 2 ^ l.ell := by omega
  have hC : 0 < l.C := Nat.two_pow_pos _
  have hc : ICtx l j (s0.env 51) s0 := ⟨hl, h50, rfl⟩
  have z := zero_fix (G := G) (s0 := s0) hK
  exact stageItem_spec mk (.dataBit j) hc hK hKN hmN s0 (fun _ _ => rfl) (.k 0) (.k 0) 0 0 2 z.1 z.1 hC hC
    (by norm_num) hjℓ (dataTL l) (by
      intro p hp
      simp only [dataTL, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact rd_tok (fix_eta hc hK 2 (by norm_num)) hK hKN
      · exact op_tok 4 .square rfl (by norm_num) hK8 hKN
      · exact rd_tok (fix_eta hc hK 2 (by norm_num)) hK hKN
      · exact op_tok 2 .add rfl (by norm_num) hK8 hKN) rfl rfl

theorem setv50_lv {l : Routing.Layout} {s t : FS} (hl : LV l s) (ht : ∀ i : Var, i ∉ LW → t.env i = s.env i) (j : ℕ) :
    LV l (t.setv 50 j) :=
  lv_of hl (fun i hi => by
    simp only [FS.setv_env, Function.update_apply]
    rw [if_neg (show i ≠ 50 from fun e => hi (by rw [e]; exact mem_LW.mpr (Or.inr (by decide))))]; exact ht i hi)

/-- **The routing printer prints the item words of `routingPairs l`.** -/
theorem routeP_spec (l : Routing.Layout) (s : FS) (hl : LV l s) (hK : l.m + 8 ≤ G.K) (hKN : G.K ≤ G.N)
    (hkN : 2 * l.k ≤ G.N) (hqN : l.q ≤ G.N) (hmN : l.m ≤ G.N) :
    Em LW s (evalS G routeP s) ((routingPairs (F := F) l).flatMap (itemWord mk)) := by
  have hkm := two_k_lt l
  have e2k : ∀ {u : FS}, LV l u → evalE G u (.mul (.k 2) (.v 31)) = 2 * l.k := fun hu =>
    eE_mul (k_val hK (small_lt_m l (by norm_num))) (by rw [eE_v, hu.k]) (cap_ge_m hK hkm)
  have e2k1 : ∀ {u : FS}, LV l u → evalE G u (.sub (.mul (.k 2) (.v 31)) (.k 1)) = 2 * l.k - 1 := fun hu =>
    eE_sub (e2k hu) (k_val hK (small_lt_m l (by norm_num)))
  suffices H : Em LW s (evalS G routeP s)
      ((List.range (2 * l.k - 1)).flatMap (fun j => rWord mk l (.route j) ++ (rWord mk l (.switchBit j) ++
        (rWord mk l (.pair j) ++ (List.range l.q).flatMap (fun tt => rWord mk l (.column j tt))))) ++
       (List.range (2 * l.k)).flatMap (fun j => rWord mk l (.dataBit j))) by
    convert H using 2
    simp [routingPairs, Routing.routingItems, List.flatMap_append, List.flatMap_map, Routing.switchCount,
      List.flatMap_assoc, Function.comp_def]
  refine Em_acc (Em_loop 50 _ stageBody LW (mem_LW.mpr (Or.inr (by decide))) s (2 * l.k - 1)
    (by rw [e2k1 hl]; omega) (fun t => ∀ i : Var, i ∉ LW → t.env i = s.env i) (fun _ _ => rfl) _
    (fun j hj t ht te => ?_)).2 (fun t1 a1 => ?_)
  · have E := stageBody_spec mk l j hj (t.setv 50 j) (setv50_lv hl ht j) (by simp) hK hKN hqN hmN
    refine ⟨fun i hi => ?_, E⟩
    rw [E.env i hi]
    simp only [FS.setv_env, Function.update_apply]
    rw [if_neg (show i ≠ 50 from fun e => hi (by rw [e]; exact mem_LW.mpr (Or.inr (by decide))))]; exact ht i hi
  · have lv1 : LV l t1 := lv_of hl a1.env
    refine (Em_loop 50 _ _ LW (mem_LW.mpr (Or.inr (by decide))) t1 (2 * l.k) (by rw [e2k lv1]; omega)
      (fun t => ∀ i : Var, i ∉ LW → t.env i = s.env i) a1.env _ (fun j hj t ht te => ?_)).2
    have E := dataItem_spec mk l j hj (t.setv 50 j) (setv50_lv hl ht j) (by simp) hK hKN hmN
    refine ⟨fun i hi => ?_, E.mono IW_sub_LW⟩
    rw [E.env i (fun h => hi (IW_sub_LW i h))]
    simp only [FS.setv_env, Function.update_apply]
    rw [if_neg (show i ≠ 50 from fun e => hi (by rw [e]; exact mem_LW.mpr (Or.inr (by decide))))]; exact ht i hi

end Spec

end NearCubicGates.Adapters.RAMACSP.Gen
