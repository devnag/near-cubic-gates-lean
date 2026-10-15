import Proof.Gates.CounterMachine.PrefixPre

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.PrefixProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicWires.RepairOrdinary (frame)

/-- The printing state: the values, the stores, and bit bounds `Λ` for everything printed. -/
structure GS (C : Ctx) (a : DS VV MM) (c : Call) (p : Params) (wt : Wit c.n) (Λ : ℕ) : Prop where
  valid : Valid C a
  cst : Cst a
  W2 : 2 ≤ C.Wd
  n : a.env gN = c.n
  tag : a.env gKd = kindTag c.kind
  k : a.env xk = p.k
  s : a.env xs = c.n - p.k
  B : a.env xB = Call.B0 c.n
  K2 : a.env xK2 = 2 ^ p.k
  G1 : a.env xG1 = c.first.gates.length
  G2 : a.env xG2 = c.second.gates.length
  Gr : a.env xGr = c.first.gates.length + c.second.gates.length
  m1 : a.env xm1 = (c.first.gates.flatMap gateN).length
  m2 : a.env xm2 = (c.second.gates.flatMap gateN).length
  np : a.env xnp = c.parity.length
  kk : a.env xkk = (coordsOf wt.I).length
  rG1 : a.ram sG1 = c.first.gates.flatMap gateN
  rG2 : a.ram sG2 = c.second.gates.flatMap gateN
  rP : a.ram sPa = c.parity
  rI : a.ram sIn = coordsOf wt.I
  card : wt.I.card = p.k
  resG : resGates c = c.first.gates ++ c.second.gates
  LW : (coordsOf wt.I).length < C.Wd
  Λn : natBitLength c.n ≤ Λ
  Λk : natBitLength p.k ≤ Λ
  Λs : natBitLength (c.n - p.k) ≤ Λ
  ΛB : natBitLength (Call.B0 c.n) ≤ Λ
  ΛK2 : natBitLength (2 ^ p.k) ≤ Λ
  ΛG1 : natBitLength c.first.gates.length ≤ Λ
  ΛG2 : natBitLength c.second.gates.length ≤ Λ
  ΛGr : natBitLength (c.first.gates.length + c.second.gates.length) ≤ Λ
  Λ2G1 : natBitLength (2 * c.first.gates.length) ≤ Λ
  Λ2G2 : natBitLength (2 * c.second.gates.length) ≤ Λ
  Λb1 : ∀ x ∈ c.first.gates.flatMap gateN, natBitLength x ≤ Λ
  Λb2 : ∀ x ∈ c.second.gates.flatMap gateN, natBitLength x ≤ Λ
  ΛI : ∀ x ∈ coordsOf wt.I, natBitLength x ≤ Λ
  Λkk : natBitLength (coordsOf wt.I).length ≤ Λ

theorem GS.tr {C : Ctx} {a d : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ)
    (e : d.ram = a.ram) (f : Fr a d TA) (v : Valid C d) : GS C d c p wt Λ := by
  refine ⟨v, Cst.of_fr h.cst f (by decide), h.W2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [e]; exact h.rG1, by rw [e]; exact h.rG2, by rw [e]; exact h.rP, by rw [e]; exact h.rI, h.card, h.resG,
    h.LW, h.Λn, h.Λk, h.Λs, h.ΛB, h.ΛK2, h.ΛG1, h.ΛG2, h.ΛGr, h.Λ2G1, h.Λ2G2, h.Λb1, h.Λb2, h.ΛI, h.Λkk⟩
  · rw [f gN (by decide)]; exact h.n
  · rw [f gKd (by decide)]; exact h.tag
  · rw [f xk (by decide)]; exact h.k
  · rw [f xs (by decide)]; exact h.s
  · rw [f xB (by decide)]; exact h.B
  · rw [f xK2 (by decide)]; exact h.K2
  · rw [f xG1 (by decide)]; exact h.G1
  · rw [f xG2 (by decide)]; exact h.G2
  · rw [f xGr (by decide)]; exact h.Gr
  · rw [f xm1 (by decide)]; exact h.m1
  · rw [f xm2 (by decide)]; exact h.m2
  · rw [f xnp (by decide)]; exact h.np
  · rw [f xkk (by decide)]; exact h.kk

theorem GS.one_le {C : Ctx} {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ) :
    1 ≤ Λ := le_trans (natBitLength_pos _) h.Λn

theorem nbl_zero : natBitLength 0 = 1 := rfl
theorem nbl_one : natBitLength 1 = 1 := rfl

/-- Every state reached by the printing pieces from `a` is again a printing state. -/
abbrev Next (C : Ctx) (a d : DS VV MM) : Prop := d.ram = a.ram ∧ Oth a d ∧ Fr a d TA ∧ Valid C d

/-! ## Pieces under `GS` -/

def gatesRes : St VV MM := .seq (femNat xGr) (.seq (emAll sG1 xm1) (emAll sG2 xm2))
def gatesMom (r : ℕ) : St VV MM :=
  if r = 0 then .seq (femNat xG1) (emAll sG1 xm1) else .seq (femNat xG2) (emAll sG2 xm2)
def hbRes : Option Bool → St VV MM
  | none => .seq (femNat xK2) hbAllP
  | some b => .seq (femNat xK2) (hbParP b)
def hbMom : St VV MM := .seq (femNat xK2) hbAllP
def rolesRes : St VV MM := .seq (femNat xGr) (rolesP xGr vZ)
def rolesMom (r : ℕ) : St VV MM :=
  .seq (femNat x2G) (.seq (rolesP (if r = 0 then xG1 else xG2) vZ) (rolesP (if r = 0 then xG1 else xG2) v1))

theorem emTA (C : Ctx) {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ)
    (m : Fin MM) (cnt : Fin VV) (hcnt : cnt ∉ emAllT) (L : List ℕ) (hm : a.ram m = L) (hl : a.env cnt = L.length)
    (hΛ : ∀ x ∈ L, natBitLength x ≤ Λ) :
    OutT C (emAll m cnt) a (L.length * (25 * Λ + 31) + L.length + 7) (L.flatMap Fn) TA := by
  have := OutT.weaken (T' := TA) (emAllO C m cnt hcnt a h.valid h.cst h.W2 Λ (by rw [hl, hm]) (by rw [hm]; exact hΛ))
    (by decide)
  rw [hm] at this; exact this

theorem gatesResO (C : Ctx) {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ) :
    OutT C gatesRes a (25 * Λ + 25 + ((c.first.gates.flatMap gateN).length * (25 * Λ + 32) + 7 +
      ((c.second.gates.flatMap gateN).length * (25 * Λ + 32) + 7) + 1) + 1)
      (Fn (resGates c).length ++ ((resGates c).flatMap gateN).flatMap Fn) TA := by
  have h1 := femTA C xGr (by decide) a a (Fr.refl _ _) h.valid h.cst h.W2 Λ (by rw [h.Gr]; exact h.ΛGr)
  refine OutT.eq (seqT h1 (fun d e o f v => ?_)) (by
    rw [h.Gr, h.resG, List.length_append, List.flatMap_append, List.flatMap_append])
  have hd := h.tr e f v
  refine seqT ((emTA C hd sG1 xm1 (by decide) _ hd.rG1 hd.m1 hd.Λb1).mono (by nlinarith)) (fun d' e' o' f' v' => ?_)
  have hd' := hd.tr e' f' v'
  exact (emTA C hd' sG2 xm2 (by decide) _ hd'.rG2 hd'.m2 hd'.Λb2).mono (by nlinarith)

theorem gatesMomO (C : Ctx) {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ)
    (r : ℕ) :
    OutT C (gatesMom r) a (25 * Λ + 25 + ((circ c r).gates.flatMap gateN).length * (25 * Λ + 32) + 8)
      (Fn (circ c r).gates.length ++ ((circ c r).gates.flatMap gateN).flatMap Fn) TA := by
  unfold gatesMom circ
  split_ifs with hr
  · have h1 := femTA C xG1 (by decide) a a (Fr.refl _ _) h.valid h.cst h.W2 Λ (by rw [h.G1]; exact h.ΛG1)
    rw [h.G1] at h1
    refine OutT.mono (seqT (t2 := (c.first.gates.flatMap gateN).length * (25 * Λ + 31) +
      (c.first.gates.flatMap gateN).length + 7) h1 (fun d e o f v => ?_)) (by nlinarith)
    have hd := h.tr e f v
    exact emTA C hd sG1 xm1 (by decide) _ hd.rG1 hd.m1 hd.Λb1
  · have h1 := femTA C xG2 (by decide) a a (Fr.refl _ _) h.valid h.cst h.W2 Λ (by rw [h.G2]; exact h.ΛG2)
    rw [h.G2] at h1
    refine OutT.mono (seqT (t2 := (c.second.gates.flatMap gateN).length * (25 * Λ + 31) +
      (c.second.gates.flatMap gateN).length + 7) h1 (fun d e o f v => ?_)) (by nlinarith)
    have hd := h.tr e f v
    exact emTA C hd sG2 xm2 (by decide) _ hd.rG2 hd.m2 hd.Λb2

theorem hbMomO (C : Ctx) {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ) :
    OutT C hbMom a (25 * Λ + 25 + (2 ^ p.k * 54 + 4) + 1)
      (Fn (2 ^ p.k) ++ (List.range (2 ^ p.k)).flatMap (fun _ => Fn 1)) TA := by
  have h1 := femTA C xK2 (by decide) a a (Fr.refl _ _) h.valid h.cst h.W2 Λ (by rw [h.K2]; exact h.ΛK2)
  rw [h.K2] at h1
  refine seqT h1 (fun d e o f v => ?_)
  have hd := h.tr e f v
  exact OutT.weaken (hbAllO C d hd.valid hd.cst hd.W2 _ hd.K2) (by decide)

theorem hbResO (C : Ctx) {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ)
    (part : Option Bool) :
    OutT C (hbRes part) a (25 * Λ + 25 + (2 ^ p.k * (c.parity.length * (20 * (coordsOf wt.I).length + 15) + 74) + 4)
      + 1) (Fn (2 ^ p.k) ++ (List.range (2 ^ p.k)).flatMap (fun x => Fn (bitN (inPart c wt part (innerPt wt.I x)))))
      TA := by
  cases part with
  | none =>
    unfold hbRes
    have h1 := femTA C xK2 (by decide) a a (Fr.refl _ _) h.valid h.cst h.W2 Λ (by rw [h.K2]; exact h.ΛK2)
    rw [h.K2] at h1
    refine OutT.mono (seqT (t2 := 2 ^ p.k * 54 + 4) h1 (fun d e o f v => ?_)) (by
      have := Nat.mul_le_mul_left (2 ^ p.k)
        (show 54 ≤ c.parity.length * (20 * (coordsOf wt.I).length + 15) + 74 by omega)
      omega)
    have hd := h.tr e f v
    exact (OutT.weaken (hbAllO C d hd.valid hd.cst hd.W2 _ hd.K2) (by decide)).eq (by simp [inPart, bitN])
  | some b =>
    unfold hbRes
    have h1 := femTA C xK2 (by decide) a a (Fr.refl _ _) h.valid h.cst h.W2 Λ (by rw [h.K2]; exact h.ΛK2)
    rw [h.K2] at h1
    refine seqT h1 (fun d e o f v => ?_)
    have hd := h.tr e f v
    refine (OutT.weaken (hbParO C b d hd.valid hd.cst hd.W2 _ hd.K2 c.parity (coordsOf wt.I) hd.rP hd.np hd.rI
      (coordsOf_nodup wt.I) hd.kk hd.LW) (by decide)).eq ?_
    apply List.flatMap_congr
    intro x _
    rw [inPart, innerParity_innerPt]
    congr 1
    by_cases hb : (c.parity.map (pbit (coordsOf wt.I) x)).foldl xor false = b
    · rw [if_pos hb, hb]; simp [bitN]
    · rw [if_neg hb]; simp [bitN, hb]

theorem rolesResO (C : Ctx) {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ) :
    OutT C rolesRes a (25 * Λ + 25 + ((c.first.gates.length + c.second.gates.length) * (50 * Λ + 55) + 4) + 1)
      (Fn (resGates c).length ++ (List.range (resGates c).length).flatMap (fun v => Fn v ++ Fn 0)) TA := by
  have h1 := femTA C xGr (by decide) a a (Fr.refl _ _) h.valid h.cst h.W2 Λ (by rw [h.Gr]; exact h.ΛGr)
  refine OutT.eq (seqT h1 (fun d e o f v => ?_)) (by rw [h.Gr, h.resG, List.length_append])
  have hd := h.tr e f v
  have := OutT.weaken (T' := TA) (rolesO C xGr vZ (by decide) (by decide) d hd.valid hd.cst hd.W2 Λ
    (by rw [hd.Gr]; exact h.ΛGr) (by rw [hd.cst.z, nbl_zero]; exact h.one_le)) (by decide)
  rw [hd.Gr, hd.cst.z] at this
  exact this

theorem rolesMomO (C : Ctx) {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ)
    (r : ℕ) (h2 : a.env x2G = 2 * (circ c r).gates.length) :
    OutT C (rolesMom r) a (25 * Λ + 25 + ((circ c r).gates.length * (50 * Λ + 55) + 4 +
      ((circ c r).gates.length * (50 * Λ + 55) + 4) + 1) + 1)
      (Fn (2 * (circ c r).gates.length) ++ ((List.range (circ c r).gates.length).flatMap (fun v => Fn v ++ Fn 0) ++
        (List.range (circ c r).gates.length).flatMap (fun v => Fn v ++ Fn 1))) TA := by
  have hG : a.env (if r = 0 then xG1 else xG2) = (circ c r).gates.length := by
    unfold circ; split_ifs <;> simp [h.G1, h.G2]
  have hGΛ : natBitLength (circ c r).gates.length ≤ Λ := by unfold circ; split_ifs <;> simp [h.ΛG1, h.ΛG2]
  have h2Λ : natBitLength (2 * (circ c r).gates.length) ≤ Λ := by unfold circ; split_ifs <;> simp [h.Λ2G1, h.Λ2G2]
  have hΛ1 : natBitLength 1 ≤ Λ := by rw [nbl_one]; exact h.one_le
  have hΛ0 : natBitLength 0 ≤ Λ := by rw [nbl_zero]; exact h.one_le
  have h1 := femTA C x2G (by decide) a a (Fr.refl _ _) h.valid h.cst h.W2 Λ (by rw [h2]; exact h2Λ)
  rw [h2] at h1
  unfold rolesMom
  refine seqT h1 (fun d e o f v => ?_)
  have hd := h.tr e f v
  have hxG : (if r = 0 then xG1 else xG2) ∉ jr :: femT := by split_ifs <;> decide
  have dG : d.env (if r = 0 then xG1 else xG2) = (circ c r).gates.length := by
    rw [f _ (by split_ifs <;> decide), hG]
  have r1 := OutT.weaken (T' := TA) (rolesO C _ vZ hxG (by decide) d hd.valid hd.cst hd.W2 Λ (by rw [dG]; exact hGΛ)
    (by rw [hd.cst.z]; exact hΛ0)) (by decide)
  rw [dG, hd.cst.z] at r1
  refine seqT r1 (fun d' e' o' f' v' => ?_)
  have hd' := hd.tr e' f' v'
  have dG' : d'.env (if r = 0 then xG1 else xG2) = (circ c r).gates.length := by
    rw [f' _ (by split_ifs <;> decide), dG]
  have r2' := OutT.weaken (T' := TA) (rolesO C _ v1 hxG (by decide) d' hd'.valid hd'.cst hd'.W2 Λ
    (by rw [dG']; exact hGΛ) (by rw [hd'.cst.one]; exact hΛ1)) (by decide)
  rw [dG', hd'.cst.one] at r2'
  exact r2'

/-! ## The two kinds of prefixes -/

def resPre (part : Option Bool) : St VV MM := preP gatesRes (hbRes part) rolesRes xGr

theorem replicate_flatMap (m : ℕ) (b : Bool) (f : Bool → List Bool) :
    (List.replicate m b).flatMap f = (List.range m).flatMap (fun _ => f b) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ', List.flatMap_append, ih, List.range_succ, List.flatMap_append]; simp

/-- The cost of one prefix (an upper bound for both kinds). -/
def preCost (c : Call) (p : Params) (wt : Wit c.n) (Λ : ℕ) : ℕ :=
  (25 * Λ + 25 + ((c.first.gates.flatMap gateN).length * (25 * Λ + 32) + 7 +
    ((c.second.gates.flatMap gateN).length * (25 * Λ + 32) + 7) + 1) + 1) +
  (25 * Λ + 25 + (2 ^ p.k * (c.parity.length * (20 * (coordsOf wt.I).length + 15) + 74) + 4) + 1) +
  (25 * Λ + 25 + ((c.first.gates.length + c.second.gates.length) * (100 * Λ + 110) + 8) + 1 + 1) +
  (c.n + (coordsOf wt.I).length + 8) * (25 * Λ + 9 * (coordsOf wt.I).length + 50)

theorem resPreO (C : Ctx) {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ)
    (part : Option Bool) :
    OutT C (resPre part) a (preCost c p wt Λ) (frame (resPrefix c p wt part)) TA := by
  have hO := preO C a h.valid h.cst h.W2 Λ c.n (coordsOf wt.I) h.n h.rI h.kk h.Λn (by rw [h.k]; exact h.Λk)
    (by rw [h.s]; exact h.Λs) (by rw [h.B]; exact h.ΛB) h.ΛI h.Λkk xGr (by decide) (by rw [h.Gr]; exact h.ΛGr)
    gatesRes (hbRes part) rolesRes _ _ _ _ _ _
    (fun d e o f v => gatesResO C (h.tr e f v)) (fun d e o f v => hbResO C (h.tr e f v) part)
    (fun d e o f v => rolesResO C (h.tr e f v))
  refine (hO.mono ?_).eq ?_
  · unfold preCost; nlinarith
  · unfold resPrefix
    rw [frame_prefixWord, h.k, h.s, h.B, h.Gr, ← List.length_append, ← h.resG]
    simp only [List.length_map]
    rw [outerCoords_length wt.I h.card, outer_eq]
    simp only [resHbits, List.length_map, List.length_range, List.flatMap_map, List.append_assoc, bitN]
    simp

def setX2 (r : ℕ) : St VV MM :=
  if r = 0 then .seq (.op (.copy x2G xG1)) (.op (.add x2G xG1)) else .seq (.op (.copy x2G xG2)) (.op (.add x2G xG2))

def momPre (r : ℕ) : St VV MM := .seq (setX2 r) (preP (gatesMom r) hbMom (rolesMom r) x2G)

theorem GS.set2 {C : Ctx} {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ)
    (v : ℕ) (hv : v < 2 ^ C.Wd) : GS C (a.set x2G v) c p wt Λ := by
  have f : Fr a (a.set x2G v) [x2G] := Fr.set a v (by simp)
  refine ⟨Valid.set' h.valid x2G v hv, Cst.of_fr h.cst f (by decide), h.W2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, h.rG1, h.rG2, h.rP, h.rI, h.card, h.resG,
    h.LW, h.Λn, h.Λk, h.Λs, h.ΛB, h.ΛK2, h.ΛG1, h.ΛG2, h.ΛGr, h.Λ2G1, h.Λ2G2, h.Λb1, h.Λb2, h.ΛI, h.Λkk⟩
  · rw [f gN (by decide)]; exact h.n
  · rw [f gKd (by decide)]; exact h.tag
  · rw [f xk (by decide)]; exact h.k
  · rw [f xs (by decide)]; exact h.s
  · rw [f xB (by decide)]; exact h.B
  · rw [f xK2 (by decide)]; exact h.K2
  · rw [f xG1 (by decide)]; exact h.G1
  · rw [f xG2 (by decide)]; exact h.G2
  · rw [f xGr (by decide)]; exact h.Gr
  · rw [f xm1 (by decide)]; exact h.m1
  · rw [f xm2 (by decide)]; exact h.m2
  · rw [f xnp (by decide)]; exact h.np
  · rw [f xkk (by decide)]; exact h.kk

theorem momPreO (C : Ctx) {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ)
    (r : ℕ) (h2W : 2 * (circ c r).gates.length < 2 ^ C.Wd) :
    OutT C (momPre r) a (preCost c p wt Λ + 3) (frame (momPrefix c p wt r)) (x2G :: TA) := by
  set G := (circ c r).gates.length with hGdef
  have hG : a.env (if r = 0 then xG1 else xG2) = G := by
    rw [hGdef]; unfold circ; split_ifs <;> simp [h.G1, h.G2]
  have hs : Hs C (setX2 r) a 3 (fun d => d = a.set x2G (2 * G)) := by
    unfold setX2
    split_ifs with hr
    · refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C x2G xG1 a (by decide)) (fun d hd => ?_)
      subst hd
      refine Hs.mono (hs_add C x2G xG1 _ (by decide) (by
        rw [DS.set_env_self, DS.set_env_ne _ _ (by decide)]; have := hG; simp [hr] at this; omega)) le_rfl ?_
      rintro e rfl
      have : a.env xG1 = G := by have := hG; simp [hr] at this; exact this
      simp only [DS.set, Function.update_idem, Function.update_self, Function.update_of_ne (show xG1 ≠ x2G by decide),
        this]; congr 1; ring_nf
    · refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C x2G xG2 a (by decide)) (fun d hd => ?_)
      subst hd
      refine Hs.mono (hs_add C x2G xG2 _ (by decide) (by
        rw [DS.set_env_self, DS.set_env_ne _ _ (by decide)]; have := hG; simp [hr] at this; omega)) le_rfl ?_
      rintro e rfl
      have : a.env xG2 = G := by have := hG; simp [hr] at this; exact this
      simp only [DS.set, Function.update_idem, Function.update_self, Function.update_of_ne (show xG2 ≠ x2G by decide),
        this]; congr 1; ring_nf
  have h' := h.set2 (2 * G) h2W
  have hx2 : (a.set x2G (2 * G)).env x2G = 2 * G := DS.set_env_self _ _ _
  have h2Λ : natBitLength (2 * G) ≤ Λ := by rw [hGdef]; unfold circ; split_ifs <;> simp [h.Λ2G1, h.Λ2G2]
  have hO := preO C (a.set x2G (2 * G)) h'.valid h'.cst h'.W2 Λ c.n (coordsOf wt.I) h'.n h'.rI h'.kk h'.Λn
    (by rw [h'.k]; exact h'.Λk) (by rw [h'.s]; exact h'.Λs) (by rw [h'.B]; exact h'.ΛB) h'.ΛI h'.Λkk x2G (by decide)
    (by rw [hx2]; exact h2Λ) (gatesMom r) hbMom (rolesMom r) _ _ _ _ _ _
    (fun d e o f v => gatesMomO C (h'.tr e f v) r) (fun d e o f v => hbMomO C (h'.tr e f v))
    (fun d e o f v => rolesMomO C (h'.tr e f v) r (by rw [f x2G (by decide), hx2]))
  unfold momPre
  obtain ⟨d1, n1, ex1, hn1, rfl⟩ := hs
  obtain ⟨d2, n2, ex2, hn2, hb2⟩ := hO
  refine ⟨d2, n1 + n2 + 1, Ex.seq ex1 ex2, ?_, ?_⟩
  · have hGb : G ≤ c.first.gates.length + c.second.gates.length := by rw [hGdef]; unfold circ; split_ifs <;> omega
    have hbb : ((circ c r).gates.flatMap gateN).length ≤ (c.first.gates.flatMap gateN).length +
        (c.second.gates.flatMap gateN).length := by unfold circ; split_ifs <;> omega
    have hk1 := Nat.mul_le_mul_left (2 ^ p.k) (show 54 ≤ c.parity.length * (20 * (coordsOf wt.I).length + 15) + 74
      by omega)
    unfold preCost; nlinarith
  · obtain ⟨e1, e2, e3, e4, e5⟩ := hb2
    refine ⟨?_, by rw [e2]; rfl, (show Oth a (a.set x2G (2 * G)) from ⟨rfl, rfl, rfl, rfl⟩).trans e3,
      Fr.trans (Fr.set a _ (by simp)) (Fr.weaken e4 (by decide)), e5⟩
    rw [e1]
    show a.out ++ _ = _
    congr 1
    unfold momPrefix
    rw [frame_prefixWord, h'.k, h'.s, h'.B, hx2]
    simp only [List.length_map]
    rw [outerCoords_length wt.I h.card, outer_eq, replicate_flatMap]
    simp only [List.length_replicate, List.length_append, List.length_map, List.length_range, List.flatMap_append,
      List.flatMap_map, List.append_assoc, bitN]
    simp [hGdef]; ring_nf

end NearCubicGates.Close.CounterMachine.PrefixProg
