import Proof.Gates.CounterMachine.PrefixParse

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.PrefixProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicWires.WireExponent3_5.FinalPass.Tm (frameP)

/-! ## The output specification -/

/-- `P` from `a` appends `Δ` within `t`; only the variables `T` and the cursors change. -/
def OutT (C : Ctx) (P : St VV MM) (a : DS VV MM) (t : ℕ) (Δ : List Bool) (T : List (Fin VV)) : Prop :=
  Hs C P a t (fun d => d.out = a.out ++ Δ ∧ d.ram = a.ram ∧ Oth a d ∧ Fr a d T ∧ Valid C d)

theorem OutT.mono {C : Ctx} {P : St VV MM} {a : DS VV MM} {t t' : ℕ} {Δ : List Bool} {T : List (Fin VV)}
    (h : OutT C P a t Δ T) (ht : t ≤ t') : OutT C P a t' Δ T := Hs.mono h ht (fun _ h => h)

theorem OutT.weaken {C : Ctx} {P : St VV MM} {a : DS VV MM} {t : ℕ} {Δ : List Bool} {T T' : List (Fin VV)}
    (h : OutT C P a t Δ T) (hT : ∀ y ∈ T, y ∈ T') : OutT C P a t Δ T' :=
  Hs.mono h le_rfl (fun _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, Fr.weaken h4 hT, h5⟩)

theorem OutT.eq {C : Ctx} {P : St VV MM} {a : DS VV MM} {t : ℕ} {Δ Δ' : List Bool} {T : List (Fin VV)}
    (h : OutT C P a t Δ T) (he : Δ = Δ') : OutT C P a t Δ' T := he ▸ h

theorem seqT {C : Ctx} {P Q : St VV MM} {a : DS VV MM} {t1 t2 : ℕ} {Δ1 Δ2 : List Bool} {T : List (Fin VV)}
    (h1 : OutT C P a t1 Δ1 T)
    (h2 : ∀ d, d.ram = a.ram → Oth a d → Fr a d T → Valid C d → OutT C Q d t2 Δ2 T) :
    OutT C (.seq P Q) a (t1 + t2 + 1) (Δ1 ++ Δ2) T := by
  refine Hs.seq h1 (fun d ⟨d1, d2, d3, d4, d5⟩ => ?_)
  refine Hs.mono (h2 d d2 d3 d4 d5) le_rfl ?_
  rintro e ⟨e1, e2, e3, e4, e5⟩
  exact ⟨by rw [e1, d1, List.append_assoc], e2.trans d2, d3.trans e3, Fr.trans d4 e4, e5⟩

theorem Valid.set' {C : Ctx} {a : DS VV MM} (h : Valid C a) (x : Fin VV) (v : ℕ) (hv : v < 2 ^ C.Wd) :
    Valid C (a.set x v) := by
  refine ⟨fun y => ?_, h.ip_le, h.ram_lt, h.rc_le, h.kin_le, h.kout_le, h.kc_le⟩
  by_cases hy : y = x
  · subst hy; simpa using hv
  · rw [DS.set_env_ne _ _ hy]; exact h.env_lt y

/-- `forS` whose invariant only has to survive the counter values `0 … N`. -/
theorem forS_specV {C : Ctx} (i m : Fin VV) (him : i ≠ m) (body : St VV MM) (a : DS VV MM) (N : ℕ)
    (hN : N < 2 ^ C.Wd) (I : ℕ → DS VV MM → Prop) (t : ℕ) (hIi : ∀ k b v, v ≤ N → I k b → I k (b.set i v))
    (h0 : I 0 a) (hm : a.env m = N)
    (hstep : ∀ k < N, ∀ b, I k b → b.env i = k → b.env m = N →
      Hs C body b t (fun d => I (k + 1) d ∧ d.env i = k ∧ d.env m = N)) :
    Hs C (forS i m body) a (N * (t + 4) + 4) (fun b => I N b ∧ b.env i = N ∧ b.env m = N) := by
  refine Hs.mono (t := 1 + (N * (t + 2 + 2) + 2) + 1) ?_ (by ring_nf; omega) (fun _ h => h)
  refine Hs.seq (hs_zero C i a) (fun b hb => ?_)
  subst hb
  refine Hs.loopN (C := C) (c := .lt i m) (s := .seq body (.op (.inc i))) him
    (fun k b => I k b ∧ b.env i = k ∧ b.env m = N) N (t + 2) ?_ ?_ (a.set i 0)
    ⟨hIi 0 a 0 (Nat.zero_le _) h0, by simp [DS.set], by rw [DS.set_env_ne _ _ (Ne.symm him)]; exact hm⟩
  · intro k hk b ⟨hI, hi, hmb⟩
    refine ⟨by simp [Cnd.eval, hi, hmb, hk], ?_⟩
    refine Hs.seq (t1 := t) (t2 := 1) (hstep k hk b hI hi hmb) (fun d ⟨hd, hdi, hdm⟩ => ?_)
    refine Hs.mono (hs_inc C i d (by rw [hdi]; omega)) le_rfl ?_
    rintro e rfl
    exact ⟨hIi _ _ _ (by rw [hdi]; omega) hd, by simp [DS.set, hdi], by
      rw [DS.set_env_ne _ _ (Ne.symm him)]; exact hdm⟩
  · intro b ⟨_, hi, hmb⟩
    simp [Cnd.eval, hi, hmb]

/-- **A printing loop**: pass `k` appends `f k`. -/
theorem loopT {C : Ctx} (i m : Fin VV) (him : i ≠ m) (T : List (Fin VV)) (hiT : i ∉ T) (hmT : m ∉ T)
    (body : St VV MM) (a : DS VV MM) (hv : Valid C a) (N : ℕ) (hN : N < 2 ^ C.Wd) (hm : a.env m = N)
    (f : ℕ → List Bool) (t : ℕ)
    (hbody : ∀ k < N, ∀ d, d.ram = a.ram → Oth a d → Fr a d (i :: T) → Valid C d → d.env i = k →
      OutT C body d t (f k) T) :
    OutT C (forS i m body) a (N * (t + 4) + 4) ((List.range N).flatMap f) (i :: T) := by
  let I : ℕ → DS VV MM → Prop := fun k d => d.out = a.out ++ (List.range k).flatMap f ∧ d.ram = a.ram ∧
    Oth a d ∧ Fr a d (i :: T) ∧ Valid C d
  have hl := forS_specV i m him body a N hN I t
    (fun k d v hvN ⟨d1, d2, d3, d4, d5⟩ => ⟨d1, d2, d3.trans ⟨rfl, rfl, rfl, rfl⟩,
      Fr.trans d4 (Fr.set d v (List.mem_cons_self ..)), Valid.set' d5 i v (by omega)⟩)
    ⟨by simp, rfl, Oth.refl a, Fr.refl _ _, hv⟩ hm ?_
  · refine Hs.mono hl le_rfl ?_
    rintro d ⟨⟨d1, d2, d3, d4, d5⟩, _, _⟩
    exact ⟨d1, d2, d3, d4, d5⟩
  · intro k hk d ⟨d1, d2, d3, d4, d5⟩ hdk hdm
    refine Hs.mono (hbody k hk d d2 d3 d4 d5 hdk) le_rfl ?_
    rintro e ⟨e1, e2, e3, e4, e5⟩
    refine ⟨⟨?_, e2.trans d2, d3.trans e3, Fr.trans d4 (Fr.weaken e4 (fun y hy => List.mem_cons_of_mem _ hy)), e5⟩,
      by rw [e4 i hiT, hdk], by rw [e4 m hmT, hdm]⟩
    rw [e1, d1, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

/-! ## Single fields -/

theorem femO (C : Ctx) (x : Fin VV) (hx : x ∉ femT) (a : DS VV MM) (hv : Valid C a) (hc : Cst a)
    (hW : 2 ≤ C.Wd) : OutT C (femNat x) a (25 * natBitLength (a.env x) + 25) (Fn (a.env x)) femT := by
  refine Hs.mono (Hs.valid (femNat_spec C x hx a hc hW (hv.env_lt x)) hv (by omega)) le_rfl ?_
  rintro d ⟨⟨d1, d2, d3⟩, d4⟩
  exact ⟨d1, d3.ram, Oth.of_sameO d3, d2, d4⟩

theorem emAllO (C : Ctx) (m : Fin MM) (cnt : Fin VV) (hcnt : cnt ∉ emAllT) (a : DS VV MM) (hv : Valid C a)
    (hc : Cst a) (hW : 2 ≤ C.Wd) (Λ : ℕ) (hlen : a.env cnt = (a.ram m).length)
    (hfit : ∀ x ∈ a.ram m, natBitLength x ≤ Λ) :
    OutT C (emAll m cnt) a ((a.ram m).length * (25 * Λ + 31) + (a.ram m).length + 7)
      ((a.ram m).flatMap Fn) emAllT := by
  refine Hs.mono (Hs.valid (emAll_spec C m cnt hcnt a hv hc hW Λ hlen hfit) hv (by omega)) le_rfl ?_
  rintro d ⟨⟨d1, d2, _, d4, d5⟩, d6⟩
  exact ⟨d1, d2, d4, d5, d6⟩

/-- Emit the closing `false` of a frame. -/
theorem endO (C : Ctx) (a : DS VV MM) (hv : Valid C a) (hW : 2 ≤ C.Wd) (T : List (Fin VV)) :
    OutT C (.op (.emit false)) a 1 [false] T := by
  refine Hs.mono (Hs.valid (hs_emit C false a) hv (by omega)) le_rfl ?_
  rintro d ⟨rfl, d2⟩
  exact ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, Fr.refl _ _, d2⟩

/-! ## Variables of the printing phase -/

/-- Protected values (set once before the prefixes). -/
def xs : Fin VV := ⟨48, by decide⟩   -- `n − k`
def xB : Fin VV := ⟨49, by decide⟩   -- `B₀ n`
def xK2 : Fin VV := ⟨50, by decide⟩  -- `2^k`
def xGr : Fin VV := ⟨51, by decide⟩  -- `|C¹.gates| + |C².gates|`
/-- Scratch. -/
def xc : Fin VV := ⟨52, by decide⟩
def xp : Fin VV := ⟨53, by decide⟩
def jo : Fin VV := ⟨54, by decide⟩
def fl : Fin VV := ⟨55, by decide⟩
def jx : Fin VV := ⟨56, by decide⟩
def par : Fin VV := ⟨57, by decide⟩
def pi : Fin VV := ⟨58, by decide⟩
def jp : Fin VV := ⟨59, by decide⟩
def js : Fin VV := ⟨60, by decide⟩
def ci : Fin VV := ⟨61, by decide⟩
def pw : Fin VV := ⟨62, by decide⟩
def q1 : Fin VV := ⟨63, by decide⟩
def r1 : Fin VV := ⟨64, by decide⟩
def q2 : Fin VV := ⟨65, by decide⟩
def r2 : Fin VV := ⟨66, by decide⟩
def tt : Fin VV := ⟨67, by decide⟩
def hv : Fin VV := ⟨68, by decide⟩
def jr : Fin VV := ⟨69, by decide⟩
def x2G : Fin VV := ⟨70, by decide⟩

/-! ## The outer coordinates -/

def outerBody : St VV MM := .seq (memS sIn xkk jo fl) (.ite (.eq fl vZ) (femNat jo) (.op (.zero yJ)))

/-- Field 7 of a prefix: `natWord (n − k)`, then the `x < n` outside the coordinate list. -/
def outerP : St VV MM := .seq (femNat xs) (forS jo gN outerBody)

def outerT : List (Fin VV) := [jo, y0, y1, y2, y3, y4, j1, yv, yJ, fl]

theorem filter_flatMap (l : List ℕ) (p : ℕ → Bool) (g : ℕ → List Bool) :
    (l.filter p).flatMap g = l.flatMap (fun x => if p x then g x else []) := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x <;> simp [h, ih]

theorem outerO (C : Ctx) (a : DS VV MM) (hva : Valid C a) (hc : Cst a) (hW : 2 ≤ C.Wd) (n : ℕ)
    (hn : a.env gN = n) (L : List ℕ) (hL : a.ram sIn = L) (hk : a.env xkk = L.length) (Λ : ℕ)
    (hΛ : natBitLength n ≤ Λ) :
    OutT C outerP a (25 * natBitLength (a.env xs) + 25 + (n * (9 * L.length + 25 * Λ + 44) + 4) + 1)
      (Fn (a.env xs) ++ ((List.range n).filter (fun x => decide (x ∉ L))).flatMap Fn) outerT := by
  refine seqT ((femO C xs (by decide) a hva hc hW).weaken (by decide)) (fun d d1 d2 d3 d4 => ?_)
  have dc : Cst d := Cst.of_fr hc d3 (by decide)
  have dn : d.env gN = n := by rw [d3 gN (by decide), hn]
  have hN : n < 2 ^ C.Wd := by rw [← dn]; exact d4.env_lt gN
  refine OutT.eq ((loopT jo gN (by decide) (outerT.tail) (by decide) (by decide) outerBody d d4 n hN dn
    (fun x => if decide (x ∉ L) then Fn x else []) (9 * L.length + 25 * Λ + 40) ?_).weaken (by decide))
    (by rw [filter_flatMap])
  intro x hx e e1 e2 e3 e4 e5
  have ec : Cst e := Cst.of_fr dc e3 (by decide)
  have eL : e.ram sIn = L := by rw [e1, d1, hL]
  have ek : e.env xkk = (e.ram sIn).length := by rw [e3 xkk (by decide), d3 xkk (by decide), hk, eL]
  unfold OutT outerBody
  refine Hs.mono (Hs.seq (t1 := 9 * L.length + 12) (t2 := 25 * Λ + 25 + 1)
    (Hs.valid (Hs.mono (memS_spec C sIn xkk jo fl (by decide) (by decide) (by decide) (by decide) (by decide)
      e e4 ec ek) (by rw [eL]) (fun _ h => h)) e4 (by omega)) (fun g ⟨⟨g1, g2, g3, _, g5, g6⟩, g7⟩ => ?_))
    (by omega) (fun _ h => h)
  have gc : Cst g := Cst.of_fr ec g6 (by decide)
  have gx : g.env jo = x := by rw [g6 jo (by decide), e5]
  have hxl : natBitLength x ≤ Λ := le_trans (Nat.log_mono_right (by omega) |> Nat.succ_le_succ) hΛ
  refine Hs.ite (c := .eq fl vZ) (show fl ≠ vZ by decide) (fun h => ?_) (fun h => ?_)
  · have hfl : g.env fl = 0 := by simpa [Cnd.eval, gc.z] using h
    have hxL : x ∉ L := by
      intro hm; rw [g1, e5, eL, if_pos hm] at hfl; cases hfl
    refine Hs.mono (femO C jo (by decide) g g7 gc hW) (by rw [gx]; omega) ?_
    rintro r ⟨r1', r2', r3', r4', r5'⟩
    refine ⟨by rw [r1', g2, gx]; simp [hxL], r2'.trans g3, g5.trans r3', Fr.trans (Fr.weaken g6 (by decide))
      (Fr.weaken r4' (by decide)), r5'⟩
  · have hfl : g.env fl ≠ 0 := by simpa [Cnd.eval, gc.z] using h
    have hxL : x ∈ L := by
      by_contra hm; rw [g1, e5, eL, if_neg hm] at hfl; exact hfl rfl
    refine Hs.mono (Hs.valid (hs_zero C yJ g) g7 (by omega)) (by omega) ?_
    rintro r ⟨rfl, r5'⟩
    refine ⟨by rw [DS.set_out, g2]; simp [hxL], g3, g5.trans ⟨rfl, rfl, rfl, rfl⟩,
      Fr.trans (Fr.weaken g6 (by decide)) (Fr.set g _ (by decide)), r5'⟩

/-! ## Roles and the all-true indicator -/

/-- `(v, b)` for `v < G` (the bit held in `cb`). -/
def rolesP (G cb : Fin VV) : St VV MM := forS jr G (.seq (femNat jr) (femNat cb))

theorem rolesO (C : Ctx) (G cb : Fin VV) (hG : G ∉ jr :: femT) (hcb : cb ∉ jr :: femT) (a : DS VV MM)
    (hva : Valid C a) (hc : Cst a) (hW : 2 ≤ C.Wd) (Λ : ℕ) (hGΛ : natBitLength (a.env G) ≤ Λ)
    (hcbΛ : natBitLength (a.env cb) ≤ Λ) :
    OutT C (rolesP G cb) a (a.env G * (50 * Λ + 55) + 4)
      ((List.range (a.env G)).flatMap (fun v => Fn v ++ Fn (a.env cb))) (jr :: femT) := by
  have hGW : a.env G < 2 ^ C.Wd := hva.env_lt G
  refine loopT jr G (fun h => hG (by rw [h]; simp)) femT (by decide) (fun h => hG (List.mem_cons_of_mem _ h))
    _ a hva (a.env G) hGW rfl _ (50 * Λ + 51) ?_
  intro v hvG d d1 d2 d3 d4 d5
  have dc : Cst d := Cst.of_fr hc d3 (by decide)
  have dcb : d.env cb = a.env cb := d3 cb hcb
  have hvl : natBitLength v ≤ Λ := le_trans (Nat.log_mono_right hvG.le |> Nat.succ_le_succ) hGΛ
  have h1 := femO C jr (by decide) d d4 dc hW
  rw [d5] at h1
  refine OutT.mono (seqT (t2 := 25 * natBitLength (a.env cb) + 25) h1 (fun e e1 e2 e3 e4 => ?_)) (by omega)
  have ec : Cst e := Cst.of_fr dc e3 (by decide)
  have ecb : e.env cb = a.env cb := by rw [e3 cb (fun h => hcb (List.mem_cons_of_mem _ h)), dcb]
  have := femO C cb (fun h => hcb (List.mem_cons_of_mem _ h)) e e4 ec hW
  rw [ecb] at this
  exact this

def hbAllP : St VV MM := forS jx xK2 (femNat v1)

theorem hbAllO (C : Ctx) (a : DS VV MM) (hva : Valid C a) (hc : Cst a) (hW : 2 ≤ C.Wd) (K : ℕ)
    (hK : a.env xK2 = K) :
    OutT C hbAllP a (K * 54 + 4) ((List.range K).flatMap (fun _ => Fn 1)) (jx :: femT) := by
  have hKW : K < 2 ^ C.Wd := by rw [← hK]; exact hva.env_lt xK2
  refine loopT jx xK2 (by decide) femT (by decide) (by decide) _ a hva K hKW hK _ 50 ?_
  intro v _ d _ _ d3 d4 _
  have dc : Cst d := Cst.of_fr hc d3 (by decide)
  have := femO C v1 (by decide) d d4 dc hW
  rw [dc.one] at this
  exact this.mono (by simp [natBitLength])

end NearCubicGates.Close.CounterMachine.PrefixProg
