import Proof.Gates.CounterMachine.PrefixGen
import Proof.Gates.Cells.Enum

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicGates.Close.CounterMachine.PrefixProg (rdS_spec Oth Oth.refl Oth.trans j1 yv yJ)

/-! ## Variables and the primes store -/

def wN : Fin VV := ⟨64, by decide⟩   -- records passed (= the cursor of `sN`)
def wX : Fin VV := ⟨65, by decide⟩   -- scratch: the value read
def wY : Fin VV := ⟨66, by decide⟩   -- scratch: a product
def wI : Fin VV := ⟨67, by decide⟩   -- loop counter
def wF : Fin VV := ⟨68, by decide⟩   -- `Σ factors`
def wW : Fin VV := ⟨69, by decide⟩   -- `W`
def wK : Fin VV := ⟨70, by decide⟩   -- `k`
def wP : Fin VV := ⟨71, by decide⟩   -- `P`
def wE : Fin VV := ⟨72, by decide⟩   -- `e`
def wNP : Fin VV := ⟨73, by decide⟩  -- number of primes
def wM1 : Fin VV := ⟨74, by decide⟩  -- `M₁`
def wNF : Fin VV := ⟨75, by decide⟩  -- number of factors
def wA : Fin VV := ⟨76, by decide⟩   -- `A`

/-- The primes, increasing. -/
def sQ : Fin MM := ⟨4, by decide⟩

/-! ## The walk state -/

/-- `R` remains of `L` in `sN`; `wN` counts the records passed; `sQ` holds `Q`; nothing else changed. -/
structure WS (b d : DS VV MM) (L R Q : List ℕ) : Prop where
  rem : L.drop (d.rc sN) = R
  le : d.rc sN ≤ L.length
  ramN : d.ram sN = L
  ramQ : d.ram sQ = Q
  ram : ∀ m, m ≠ sN → m ≠ sQ → d.ram m = b.ram m
  rcQ : d.rc sQ = Q.length
  rc : ∀ m, m ≠ sN → m ≠ sQ → d.rc m = b.rc m
  cnt : d.env wN = d.rc sN
  out : d.out = b.out
  oth : Oth b d
  cst : Cst d

theorem WS.rcN_le {b d : DS VV MM} {L R Q : List ℕ} (h : WS b d L R Q) : d.rc sN + R.length ≤ L.length ∨
    R = [] := by
  rcases Nat.lt_or_ge (d.rc sN) L.length with h1 | h1
  · left; rw [← h.rem, List.length_drop]; omega
  · right; rw [← h.rem]; exact List.drop_eq_nil_of_le h1

theorem WS.lt {b d : DS VV MM} {L R Q : List ℕ} {v : ℕ} (h : WS b d L (v :: R) Q) :
    d.rc sN + R.length + 1 = L.length := by
  have := congrArg List.length h.rem
  simp only [List.length_drop, List.length_cons] at this
  omega

theorem WS.set {b d : DS VV MM} {L R Q : List ℕ} (h : WS b d L R Q) (x : Fin VV) (v : ℕ) (hx : x ≠ wN)
    (h3 : 3 ≤ x.val) : WS b (d.set x v) L R Q :=
  ⟨h.rem, h.le, h.ramN, h.ramQ, h.ram, h.rcQ, h.rc, by rw [DS.set_env_ne _ _ (Ne.symm hx)]; exact h.cnt, h.out,
    h.oth.trans ⟨rfl, rfl, rfl, rfl⟩,
    ⟨by rw [DS.set_env_ne _ _ (fun e => by rw [← e] at h3; simp [vZ] at h3)]; exact h.cst.z,
     by rw [DS.set_env_ne _ _ (fun e => by rw [← e] at h3; simp [v1] at h3)]; exact h.cst.one,
     by rw [DS.set_env_ne _ _ (fun e => by rw [← e] at h3; simp [v2] at h3)]; exact h.cst.two⟩⟩

/-! ## Steps -/

/-- Read one record, count it. -/
def rdW (x : Fin VV) : St VV MM := .seq (.op (.rdM sN x)) (.op (.inc wN))

theorem WS.rdW {C : Ctx} {b d : DS VV MM} {L R Q : List ℕ} {v : ℕ} (h : WS b d L (v :: R) Q)
    (hL : L.length < 2 ^ C.Wd) (x : Fin VV) (hxN : x ≠ wN) (hx : 3 ≤ x.val) :
    Hs C (CellTablesProg.rdW x) d 3 (fun e => WS b e L R Q ∧ e.env x = v ∧ Fr d e [x, wN]) := by
  have hlt := h.lt
  have hrem : (d.ram sN).drop (d.rc sN) = v :: R := by rw [h.ramN]; exact h.rem
  refine Hs.seq (t1 := 1) (t2 := 1) (rdS_spec C sN x d v R hrem) (fun e ⟨e1, e2, e3, e4, e5, e6, e7⟩ => ?_)
  have ewN : e.env wN = d.rc sN := by rw [e7 wN (by simp; exact Ne.symm hxN)]; exact h.cnt
  refine Hs.mono (hs_inc C wN e (by rw [ewN]; omega)) le_rfl ?_
  rintro f rfl
  have erc : e.rc sN = d.rc sN + 1 := by rw [e4]; simp
  refine ⟨⟨?_, by show e.rc sN ≤ _; rw [erc]; omega, by simp [e3, h.ramN], by simp [e3, h.ramQ], fun m h1 h2 => by simp [e3, h.ram m h1 h2],
    by simp [e4, Function.update_of_ne (show sQ ≠ sN by decide), h.rcQ],
    fun m h1 h2 => by simp [e4, Function.update_of_ne h1, h.rc m h1 h2], by simp [ewN, erc], by simp [e5, h.out],
    h.oth.trans (e6.trans ⟨rfl, rfl, rfl, rfl⟩), ?_⟩, ?_, ?_⟩
  · show L.drop (e.rc sN) = R
    rw [← h.ramN, ← e3]; exact e2
  · have := h.cst
    refine ⟨?_, ?_, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide), e7 vZ (by simp; intro e; rw [← e] at hx; simp [vZ] at hx)]; exact this.z
    · rw [DS.set_env_ne _ _ (by decide), e7 v1 (by simp; intro e; rw [← e] at hx; simp [v1] at hx)]; exact this.one
    · rw [DS.set_env_ne _ _ (by decide), e7 v2 (by simp; intro e; rw [← e] at hx; simp [v2] at hx)]; exact this.two
  · rw [DS.set_env_ne _ _ hxN]; exact e1
  · exact Fr.trans (Fr.weaken e7 (by simp)) (Fr.set e _ (by simp))

/-- Pass `k` records (a constant). -/
def skW : ℕ → St VV MM
  | 0 => .op (.zero wX)
  | k + 1 => .seq (CellTablesProg.rdW wX) (skW k)

theorem WS.skW {C : Ctx} : ∀ (k : ℕ) {b d : DS VV MM}
    {L A R Q : List ℕ}, WS b d L (A ++ R) Q → L.length < 2 ^ C.Wd → A.length = k →
    Hs C (CellTablesProg.skW k) d (4 * k + 1) (fun e => WS b e L R Q ∧ Fr d e [wX, wN])
  | 0, b, d, L, A, R, Q, h, _, hk => by
    have : A = [] := List.eq_nil_of_length_eq_zero hk
    subst this
    refine Hs.mono (hs_zero C wX d) le_rfl ?_
    rintro e rfl
    exact ⟨h.set wX 0 (by decide) (by decide), Fr.set d 0 (by simp)⟩
  | k + 1, b, d, L, A, R, Q, h, hL', hk => by
    obtain ⟨v, A', rfl⟩ : ∃ v A', A = v :: A' := by
      cases A with
      | nil => simp at hk
      | cons v A' => exact ⟨v, A', rfl⟩
    refine Hs.mono (Hs.seq (t1 := 3) (t2 := 4 * k + 1) (h.rdW (R := A' ++ R) hL' wX (by decide) (by decide))
      (fun e ⟨e1, _, e3⟩ => ?_)) (by omega) (fun _ h => h)
    refine Hs.mono (WS.skW k e1 hL' (by simpa using hk)) le_rfl ?_
    rintro f ⟨f1, f2⟩
    exact ⟨f1, Fr.trans (Fr.weaken e3 (by simp)) f2⟩

/-- Pass `x` records (a variable). -/
def skV (x : Fin VV) : St VV MM := .seq (PrefixProg.skipS sN x) (.op (.add wN x))

theorem WS.skV {C : Ctx} {b d : DS VV MM} {L A R Q : List ℕ} (h : WS b d L (A ++ R) Q)
    (hL : L.length < 2 ^ C.Wd) (x : Fin VV) (hx : 38 ≤ x.val) (hxN : x ≠ wN) (hlen : d.env x = A.length) :
    Hs C (skV x) d (A.length * 5 + 6) (fun e => WS b e L R Q ∧ Fr d e [j1, yJ, wN]) := by
  have hAl : d.rc sN + A.length + R.length = L.length := by
    have := congrArg List.length h.rem
    have := h.le
    simp only [List.length_drop, List.length_append] at *
    omega
  have hrem : (d.ram sN).drop (d.rc sN) = A ++ R := by rw [h.ramN]; exact h.rem
  refine Hs.seq (t1 := A.length * 5 + 4) (t2 := 1) (PrefixProg.skipS_spec C sN x hx d A R hrem hlen (by omega))
    (fun e ⟨e1, e2, e3, e4, e5, e6⟩ => ?_)
  have ewN : e.env wN = d.rc sN := by rw [e6 wN (by decide)]; exact h.cnt
  have ex : e.env x = A.length := by
    rw [e6 x (by simp; constructor <;> (intro e; rw [e] at hx; simp [j1, yJ] at hx))]; exact hlen
  refine Hs.mono (hs_add C wN x e (Ne.symm hxN) (by rw [ewN, ex]; omega)) le_rfl ?_
  rintro f rfl
  have erc : e.rc sN = d.rc sN + A.length := by rw [e3]; simp
  refine ⟨⟨?_, by show e.rc sN ≤ _; rw [erc]; omega, by simp [e2, h.ramN], by simp [e2, h.ramQ], fun m h1 h2 => by simp [e2, h.ram m h1 h2],
    by simp [e3, Function.update_of_ne (show sQ ≠ sN by decide), h.rcQ],
    fun m h1 h2 => by simp [e3, Function.update_of_ne h1, h.rc m h1 h2], by simp [ewN, ex, erc],
    by simp [e4, h.out], h.oth.trans (e5.trans ⟨rfl, rfl, rfl, rfl⟩), ?_⟩, ?_⟩
  · show L.drop (e.rc sN) = R
    rw [← h.ramN, ← e2]; exact e1
  · have := h.cst
    refine ⟨?_, ?_, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide), e6 vZ (by decide)]; exact this.z
    · rw [DS.set_env_ne _ _ (by decide), e6 v1 (by decide)]; exact this.one
    · rw [DS.set_env_ne _ _ (by decide), e6 v2 (by decide)]; exact this.two
  · exact Fr.trans (Fr.weaken e6 (by simp)) (Fr.set e _ (by simp))

/-- Copy `x` records to `sQ`, count them. -/
def cpQ (x : Fin VV) : St VV MM := .seq (PrefixProg.cpS sN sQ x) (.op (.add wN x))

theorem WS.cpQ {C : Ctx} {b d : DS VV MM} {L A R Q : List ℕ} (h : WS b d L (A ++ R) Q)
    (hL : L.length < 2 ^ C.Wd) (x : Fin VV) (hx : 38 ≤ x.val) (hxN : x ≠ wN) (hlen : d.env x = A.length) :
    Hs C (cpQ x) d (A.length * 7 + 6) (fun e => WS b e L R (Q ++ A) ∧ Fr d e [j1, yv, wN]) := by
  have hAl : d.rc sN + A.length + R.length = L.length := by
    have := congrArg List.length h.rem
    have := h.le
    simp only [List.length_drop, List.length_append] at *
    omega
  have hrem : (d.ram sN).drop (d.rc sN) = A ++ R := by rw [h.ramN]; exact h.rem
  refine Hs.seq (t1 := A.length * 7 + 4) (t2 := 1) (PrefixProg.cpS_spec C sN sQ (by decide) x hx d A R hrem hlen
    (by omega) (by rw [h.rcQ, h.ramQ])) (fun e ⟨e1, e2, e3, e4, e5, e6⟩ => ?_)
  have ewN : e.env wN = d.rc sN := by rw [e6 wN (by decide)]; exact h.cnt
  have ex : e.env x = A.length := by
    rw [e6 x (by simp; constructor <;> (intro e; rw [e] at hx; simp [j1, yv] at hx))]; exact hlen
  refine Hs.mono (hs_add C wN x e (Ne.symm hxN) (by rw [ewN, ex]; omega)) le_rfl ?_
  rintro f rfl
  have erc : e.rc sN = d.rc sN + A.length := by
    rw [e3, Function.update_of_ne (show sN ≠ sQ by decide)]; simp
  refine ⟨⟨?_, by show e.rc sN ≤ _; rw [erc]; omega, by simp [e2, h.ramN, Function.update_of_ne (show sN ≠ sQ by decide)],
    by simp [e2, h.ramQ], fun m h1 h2 => by simp [e2, Function.update_of_ne h2, h.ram m h1 h2],
    by simp [e3, h.rcQ, h.ramQ],
    fun m h1 h2 => by simp [e3, Function.update_of_ne h1, Function.update_of_ne h2, h.rc m h1 h2],
    by simp [ewN, ex, erc], by simp [e4, h.out], h.oth.trans (e5.trans ⟨rfl, rfl, rfl, rfl⟩), ?_⟩, ?_⟩
  · show L.drop (e.rc sN) = R
    have : e.ram sN = L := by rw [e2, Function.update_of_ne (show sN ≠ sQ by decide), h.ramN]
    rw [← this]; exact e1
  · have := h.cst
    refine ⟨?_, ?_, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide), e6 vZ (by decide)]; exact this.z
    · rw [DS.set_env_ne _ _ (by decide), e6 v1 (by decide)]; exact this.one
    · rw [DS.set_env_ne _ _ (by decide), e6 v2 (by decide)]; exact this.two
  · exact Fr.trans (Fr.weaken e6 (by simp)) (Fr.set e _ (by simp))

end NearCubicGates.Close.CounterMachine.CellTablesProg
