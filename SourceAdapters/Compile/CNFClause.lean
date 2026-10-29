import SourceAdapters.Compile.CNFWp

/-!
# Clause codes in cells

proof of `lem:multitape-refuter`: every clause has exactly three literals and is written with the native literal-list code
(`Encodable.encode`, the `Nat.pair` list code) inside the balanced outer code. The interpreter appends the code of
each Tseitin clause (`CNFRpn.rcl`) to the clause store `sCL`; this module is the arithmetic: `pairP` computes
`Nat.pair`, `clauseP` the code `ccode` of one clause (`encode_triple`).

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.TseitinCNF
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The native code of the clause `[(b1, x1), (b2, x2), (b3, x3)]`. -/
def ccode (b1 x1 b2 x2 b3 x3 : ℕ) : ℕ :=
  Nat.pair (Nat.pair b1 x1) (Nat.pair (Nat.pair b2 x2) (Nat.pair (Nat.pair b3 x3) 0 + 1) + 1) + 1

theorem encode_triple (b1 b2 b3 : Bool) (x1 x2 x3 : ℕ) :
    Encodable.encode (triple (b1, x1) (b2, x2) (b3, x3)) = ccode b1.toNat x1 b2.toNat x2 b3.toNat x3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> rfl

/-- `b` appends `codes` to store `m0` (cursor at the end) and changes no other store, the input head or output. -/
structure ExtS (m0 : Fin MM) (a b : DS VV MM) (codes : List ℕ) : Prop where
  st : b.ram m0 = a.ram m0 ++ codes
  rc : b.rc m0 = a.rc m0 + codes.length
  ram : ∀ m, m ≠ m0 → b.ram m = a.ram m
  rcs : ∀ m, m ≠ m0 → b.rc m = a.rc m
  ip : b.ip = a.ip
  out : b.out = a.out

theorem ExtS.of_eq {m0 : Fin MM} {a b : DS VV MM} (h1 : b.ram = a.ram) (h2 : b.rc = a.rc) (h3 : b.ip = a.ip)
    (h4 : b.out = a.out) : ExtS m0 a b [] := ⟨by simp [h1], by simp [h2], fun m _ => by rw [h1],
  fun m _ => by rw [h2], h3, h4⟩

theorem ExtS.trans {m0 : Fin MM} {a b d : DS VV MM} {c1 c2 : List ℕ} (h1 : ExtS m0 a b c1) (h2 : ExtS m0 b d c2) :
    ExtS m0 a d (c1 ++ c2) :=
  ⟨by rw [h2.st, h1.st]; simp, by rw [h2.rc, h1.rc]; simp; omega, fun m hm => (h2.ram m hm).trans (h1.ram m hm),
    fun m hm => (h2.rcs m hm).trans (h1.rcs m hm), h2.ip.trans h1.ip, h2.out.trans h1.out⟩

theorem ExtS.congr {m0 : Fin MM} {a b : DS VV MM} {c1 c2 : List ℕ} (h : ExtS m0 a b c1) (e : c1 = c2) :
    ExtS m0 a b c2 := e ▸ h

def c0 : Fin VV := ⟨72, by decide⟩
def c1 : Fin VV := ⟨73, by decide⟩
def c2 : Fin VV := ⟨74, by decide⟩
def c3 : Fin VV := ⟨75, by decide⟩
def c4 : Fin VV := ⟨76, by decide⟩
def c5 : Fin VV := ⟨77, by decide⟩
def c6 : Fin VV := ⟨78, by decide⟩

variable {C : Ctx}

theorem sq_le_pair (a b : ℕ) : a * a ≤ Nat.pair a b ∧ b * b ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs with h
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/-- `z := Nat.pair x y` (scratch `w`). -/
def pairP (x y z w : Fin VV) : St VV MM :=
  .ite (.lt x y) (.seq (.op (.copy w y)) (.seq (.op (.mul y w z)) (.op (.add z x))))
    (.seq (.op (.copy w x)) (.seq (.op (.mul x w z)) (.seq (.op (.add z x)) (.op (.add z y)))))

theorem pairP_spec (x y z w : Fin VV) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hzw : z ≠ w) (a : DS VV MM) (hW : Nat.pair (a.env x) (a.env y) < 2 ^ C.Wd) :
    Hs C (pairP x y z w) a 8 (fun b => b.env z = Nat.pair (a.env x) (a.env y) ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
      b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [z, w]) := by
  have hsq := sq_le_pair (a.env x) (a.env y)
  have hl := Nat.left_le_pair (a.env x) (a.env y)
  have hr := Nat.right_le_pair (a.env x) (a.env y)
  apply hs_of_wpc
  simp only [pairP, wpc, opwp, Cnd.eval, Cnd.wf]
  refine ⟨hxy, fun h => ?_, fun h => ?_⟩
  · have hlt : a.env x < a.env y := by simpa using h
    have hp : Nat.pair (a.env x) (a.env y) = a.env y * a.env y + a.env x := by simp [Nat.pair, hlt]
    vsimp [Ne.symm hyw, hyw, hzw, Ne.symm hzw, hxz, Ne.symm hxz, Ne.symm hyz, hyz, hxw, Ne.symm hxw]
    and_split
    all_goals first | omega | rfl | skip
    all_goals fr_tac
  · have hge : ¬ a.env x < a.env y := by simpa using h
    have hp : Nat.pair (a.env x) (a.env y) = a.env x * a.env x + a.env x + a.env y := by simp [Nat.pair, hge]
    vsimp [Ne.symm hyw, hyw, hzw, Ne.symm hzw, hxz, Ne.symm hxz, Ne.symm hyz, hyz, hxw, Ne.symm hxw]
    and_split
    all_goals first | omega | rfl | skip
    all_goals fr_tac

/-- `y := x + 1`-style step: `z := Nat.pair x y; z := z + 1`. -/
def pairIncP (x y z : Fin VV) : St VV MM := .seq (pairP x y z c6) (.op (.inc z))

theorem pairIncP_spec (x y z : Fin VV) (hxy : x ≠ y) (hxz : x ≠ z) (hx6 : x ≠ c6) (hyz : y ≠ z) (hy6 : y ≠ c6)
    (hz6 : z ≠ c6) (a : DS VV MM) (hW : Nat.pair (a.env x) (a.env y) + 1 < 2 ^ C.Wd) :
    Hs C (pairIncP x y z) a 10 (fun b => b.env z = Nat.pair (a.env x) (a.env y) + 1 ∧ b.ram = a.ram ∧
      b.rc = a.rc ∧ b.ip = a.ip ∧ b.out = a.out ∧ Fr a b [z, c6]) := by
  refine Hs.seqc (t1 := 8) (t2 := 1) (pairP_spec x y z c6 hxy hxz hx6 hyz hy6 hz6 a (by omega)) (fun b hb => ?_)
    (by omega)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb
  refine Hs.op (OpEx.inc z b (by rw [h1]; exact hW)) ⟨by rw [DS.set_env_self, h1], h2, h3, h4, h5, ?_⟩
  exact h6.trans (Fr.set _ _ (by simp))

/-- Append `ccode` of the literals `(p1,x1) (p2,x2) (p3,x3)` to `sCL` (scratch `c0..c6`). -/
def clauseP (p1 x1 p2 x2 p3 x3 : Fin VV) : St VV MM :=
  .seq (pairP p3 x3 c0 c6) (.seq (pairIncP c0 vZ c1) (.seq (pairP p2 x2 c2 c6) (.seq (pairIncP c2 c1 c3)
    (.seq (pairP p1 x1 c4 c6) (.seq (pairIncP c4 c3 c5) (.op (.wrM sCL c5)))))))

def clT : List (Fin VV) := [c0, c1, c2, c3, c4, c5, c6]

theorem ccode_bounds (b1 x1 b2 x2 b3 x3 : ℕ) :
    Nat.pair b3 x3 ≤ ccode b1 x1 b2 x2 b3 x3 ∧ Nat.pair (Nat.pair b3 x3) 0 + 1 ≤ ccode b1 x1 b2 x2 b3 x3 ∧
      Nat.pair b2 x2 ≤ ccode b1 x1 b2 x2 b3 x3 ∧
      Nat.pair (Nat.pair b2 x2) (Nat.pair (Nat.pair b3 x3) 0 + 1) + 1 ≤ ccode b1 x1 b2 x2 b3 x3 ∧
      Nat.pair b1 x1 ≤ ccode b1 x1 b2 x2 b3 x3 := by
  unfold ccode
  have a1 := Nat.left_le_pair (Nat.pair b1 x1) (Nat.pair (Nat.pair b2 x2) (Nat.pair (Nat.pair b3 x3) 0 + 1) + 1)
  have a2 := Nat.right_le_pair (Nat.pair b1 x1) (Nat.pair (Nat.pair b2 x2) (Nat.pair (Nat.pair b3 x3) 0 + 1) + 1)
  have a3 := Nat.left_le_pair (Nat.pair b2 x2) (Nat.pair (Nat.pair b3 x3) 0 + 1)
  have a4 := Nat.right_le_pair (Nat.pair b2 x2) (Nat.pair (Nat.pair b3 x3) 0 + 1)
  have a5 := Nat.left_le_pair (Nat.pair b3 x3) 0
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem clauseP_spec (p1 x1 p2 x2 p3 x3 : Fin VV) (hr : ∀ y ∈ [p1, x1, p2, x2, p3, x3], y ∉ clT)
    (h1 : p1 ≠ x1) (h2 : p2 ≠ x2) (h3 : p3 ≠ x3) (a : DS VV MM) (hz : a.env vZ = 0)
    (hend : a.rc sCL = (a.ram sCL).length)
    (hW : ccode (a.env p1) (a.env x1) (a.env p2) (a.env x2) (a.env p3) (a.env x3) < 2 ^ C.Wd) :
    Hs C (clauseP p1 x1 p2 x2 p3 x3) a 70 (fun b =>
      ExtS sCL a b [ccode (a.env p1) (a.env x1) (a.env p2) (a.env x2) (a.env p3) (a.env x3)] ∧ Fr a b clT) := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := ccode_bounds (a.env p1) (a.env x1) (a.env p2) (a.env x2) (a.env p3) (a.env x3)
  have hc := fun y hy => hr y hy
  have np1 : p1 ∉ clT := hc p1 (by simp)
  have nx1 : x1 ∉ clT := hc x1 (by simp)
  have np2 : p2 ∉ clT := hc p2 (by simp)
  have nx2 : x2 ∉ clT := hc x2 (by simp)
  have np3 : p3 ∉ clT := hc p3 (by simp)
  have nx3 : x3 ∉ clT := hc x3 (by simp)
  simp only [clT, List.mem_cons, List.not_mem_nil, or_false, not_or] at np1 nx1 np2 nx2 np3 nx3
  -- step 1: c0 := pair p3 x3
  refine Hs.seqc (t1 := 8) (t2 := 61) (pairP_spec p3 x3 c0 c6 h3 np3.1 np3.2.2.2.2.2.2 nx3.1 nx3.2.2.2.2.2.2
    (by decide) a (by omega)) (fun s1 hs1 => ?_) (by omega)
  obtain ⟨e1, r1, k1, i1, o1, f1⟩ := hs1
  have z1 : s1.env vZ = 0 := by rw [f1 vZ (by decide), hz]
  -- step 2: c1 := pair c0 0 + 1
  refine Hs.seqc (t1 := 10) (t2 := 50) (pairIncP_spec c0 vZ c1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s1 (by rw [e1, z1]; omega)) (fun s2 hs2 => ?_) (by omega)
  obtain ⟨e2, r2, k2, i2, o2, f2⟩ := hs2
  rw [e1, z1] at e2
  have fp2 : ∀ y, y ∉ clT → s2.env y = a.env y := fun y hy => by
    simp only [clT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [f2 y (by simp [hy.2.1, hy.2.2.2.2.2.2]), f1 y (by simp [hy.1, hy.2.2.2.2.2.2])]
  -- step 3: c2 := pair p2 x2
  refine Hs.seqc (t1 := 8) (t2 := 41) (pairP_spec p2 x2 c2 c6 h2 np2.2.2.1 np2.2.2.2.2.2.2 nx2.2.2.1
    nx2.2.2.2.2.2.2 (by decide) s2 (by rw [fp2 p2 (by simp [clT]; tauto), fp2 x2 (by simp [clT]; tauto)]; omega))
    (fun s3 hs3 => ?_) (by omega)
  obtain ⟨e3, r3, k3, i3, o3, f3⟩ := hs3
  rw [fp2 p2 (by simp [clT]; tauto), fp2 x2 (by simp [clT]; tauto)] at e3
  have e2' : s3.env c1 = Nat.pair (Nat.pair (a.env p3) (a.env x3)) 0 + 1 := by rw [f3 c1 (by decide), e2]
  -- step 4: c3 := pair c2 c1 + 1
  refine Hs.seqc (t1 := 10) (t2 := 30) (pairIncP_spec c2 c1 c3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s3 (by rw [e3, e2']; omega)) (fun s4 hs4 => ?_) (by omega)
  obtain ⟨e4, r4, k4, i4, o4, f4⟩ := hs4
  rw [e3, e2'] at e4
  have fp4 : ∀ y, y ∉ clT → s4.env y = a.env y := fun y hy => by
    simp only [clT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [f4 y (by simp [hy.2.2.2.1, hy.2.2.2.2.2.2]), f3 y (by simp [hy.2.2.1, hy.2.2.2.2.2.2])]
    exact fp2 y (by simp [clT]; tauto)
  -- step 5: c4 := pair p1 x1
  refine Hs.seqc (t1 := 8) (t2 := 21) (pairP_spec p1 x1 c4 c6 h1 np1.2.2.2.2.1 np1.2.2.2.2.2.2 nx1.2.2.2.2.1
    nx1.2.2.2.2.2.2 (by decide) s4 (by rw [fp4 p1 (by simp [clT]; tauto), fp4 x1 (by simp [clT]; tauto)]; omega))
    (fun s5 hs5 => ?_) (by omega)
  obtain ⟨e5, r5, k5, i5, o5, f5⟩ := hs5
  rw [fp4 p1 (by simp [clT]; tauto), fp4 x1 (by simp [clT]; tauto)] at e5
  have e4' : s5.env c3 = Nat.pair (Nat.pair (a.env p2) (a.env x2)) (Nat.pair (Nat.pair (a.env p3) (a.env x3)) 0 + 1)
      + 1 := by rw [f5 c3 (by decide), e4]
  -- step 6: c5 := pair c4 c3 + 1 = ccode
  refine Hs.seqc (t1 := 10) (t2 := 1) (pairIncP_spec c4 c3 c5 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) s5 (by rw [e5, e4']; unfold ccode at hW; omega)) (fun s6 hs6 => ?_) (by omega)
  obtain ⟨e6, r6, k6, i6, o6, f6⟩ := hs6
  rw [e5, e4'] at e6
  have hend6 : s6.rc sCL = (s6.ram sCL).length := by rw [k6, k5, k4, k3, k2, k1, r6, r5, r4, r3, r2, r1]; exact hend
  refine Hs.op (OpEx.wrM sCL c5 s6 (le_of_eq hend6)) ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [DS.put, Function.update_self, putAt, hend6, lt_irrefl, if_false, e6]
    rw [r6, r5, r4, r3, r2, r1]; rfl
  · simp only [DS.put, Function.update_self]; rw [k6, k5, k4, k3, k2, k1]; simp
  · intro m hm; simp only [DS.put, Function.update_of_ne hm]; rw [r6, r5, r4, r3, r2, r1]
  · intro m hm; simp only [DS.put, Function.update_of_ne hm]; rw [k6, k5, k4, k3, k2, k1]
  · simp only [DS.put]; rw [i6, i5, i4, i3, i2, i1]
  · simp only [DS.put]; rw [o6, o5, o4, o3, o2, o1]
  · intro y hy
    have hy' := hy
    simp only [clT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
    show s6.env y = a.env y
    rw [f6 y (by simp [hy'.2.2.2.2.2.1, hy'.2.2.2.2.2.2]), f5 y (by simp [hy'.2.2.2.2.1, hy'.2.2.2.2.2.2])]
    exact fp4 y hy

end NearCubicGates.Adapters.Compile
