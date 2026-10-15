import Proof.Gates.Cells.Loop

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

variable {C : Ctx}

/-! ## Stores and loop counters -/

def sN : Fin MM := ⟨0, by decide⟩
def sCT : Fin MM := ⟨1, by decide⟩
def sG : Fin MM := ⟨2, by decide⟩
def sA : Fin MM := ⟨3, by decide⟩
def sP : Fin MM := ⟨4, by decide⟩
def sR : Fin MM := ⟨5, by decide⟩
def sZb : Fin MM := ⟨6, by decide⟩
def sB : Fin MM := ⟨7, by decide⟩
def sE : Fin MM := ⟨8, by decide⟩
def sX : Fin MM := ⟨9, by decide⟩

def c1 : Fin VV := ⟨15, by decide⟩
def c2 : Fin VV := ⟨16, by decide⟩
def c3 : Fin VV := ⟨17, by decide⟩
def c4 : Fin VV := ⟨18, by decide⟩
def c5 : Fin VV := ⟨19, by decide⟩
/-- Count of a `readL` list. -/
def lc : Fin VV := ⟨20, by decide⟩

/-! ## Reading naturals into `sN` -/

/-- Read one `natWord` (into `t3`) and append it to `sN`. -/
def rdStore : St VV MM := .seq rdNatI (.op (.wrM sN t3))

/-- Read `cnt` naturals. -/
def readF (cnt : Fin VV) : St VV MM := forS c1 cnt rdStore

def readT : List (Fin VV) := [c1, t0, t1, t2, t3, t4, vJ]

/-- The non-variable part after reading `L` from the cursor. -/
def Loaded (a b : DS VV MM) (L : List ℕ) : Prop :=
  b.ram = Function.update a.ram sN (a.ram sN ++ L) ∧ b.rc = Function.update a.rc sN ((a.ram sN).length + L.length) ∧
    b.ip = a.ip + (L.flatMap natWord).length ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc

theorem Loaded.set {a b : DS VV MM} {L : List ℕ} (h : Loaded a b L) (x : Fin VV) (v : ℕ) :
    Loaded a (b.set x v) L := h

theorem rdStore_spec (a : DS VV MM) (hc : Cst a) (x : ℕ) (rest : List Bool)
    (hcw : C.inp.drop a.ip = natWord x ++ rest) (hW : natBitLength x + 2 ≤ C.Wd)
    (hrc : a.rc sN = (a.ram sN).length) :
    Hs C rdStore a (30 * natBitLength x + 32) (fun b => b.env t3 = x ∧ Loaded a b [x] ∧ Cst b ∧ Fr a b rdNatT) := by
  refine Hs.mono (Hs.seq (t1 := 30 * natBitLength x + 30) (t2 := 1) (rdNatI_spec a hc x rest hcw hW)
    (fun b ⟨h1, _, h3, h4, h5⟩ => ?_)) (by omega)
    (fun _ h => h)
  simp only [Prod.mk.injEq] at h4
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := h4
  refine Hs.mono (hs_wrM C sN t3 b (by rw [o3, o2, hrc])) le_rfl ?_
  rintro d rfl
  refine ⟨by simp [DS.put, h1], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, cst_fr hc h5, ?_⟩
  · simp only [DS.put, o2, o3, hrc, h1]
    funext m; by_cases hm : m = sN
    · subst hm; simp [putAt]
    · simp [Function.update_of_ne hm]
  · simp only [DS.put, o3, o2]
    funext m; by_cases hm : m = sN
    · subst hm; simp [hrc]
    · simp [Function.update_of_ne hm]
  · simp [DS.put, h3]
  · simp [DS.put, o1]
  · simp [DS.put, o4]
  · simp [DS.put, o5]
  · simp [DS.put, o6]
  · exact h5

theorem readF_spec (cnt : Fin VV) (hcnt : cnt ∉ readT) (a : DS VV MM) (hc : Cst a) (L : List ℕ) (rest : List Bool)
    (Λ : ℕ) (hcw : C.inp.drop a.ip = L.flatMap natWord ++ rest) (hN : a.env cnt = L.length)
    (hfit : ∀ x ∈ L, natBitLength x ≤ Λ) (hΛ : Λ + 2 ≤ C.Wd) (hL : L.length < 2 ^ C.Wd)
    (hrc : a.rc sN = (a.ram sN).length) :
    Hs C (readF cnt) a (L.length * (30 * Λ + 36) + 4) (fun b => Loaded a b L ∧ Cst b ∧ Fr a b readT) := by
  have hc1 : c1 ≠ cnt := fun h => hcnt (h ▸ by decide)
  let I : ℕ → DS VV MM → Prop := fun k b => Loaded a b (L.take k) ∧ Cst b ∧ Fr a b readT
  have h := forS_spec' (C := C) c1 cnt hc1 rdStore a L.length hL I (30 * Λ + 32)
    (fun k b v ⟨h1, h2, h3⟩ => ⟨h1, Cst.of_fr h2 (Fr.set b (T := readT) v (by decide)) (by decide),
      Fr.trans h3 (Fr.set b v (by decide))⟩)
    ⟨⟨by simp, by rw [← hrc]; simp, by simp, rfl, rfl, rfl, rfl⟩, hc, Fr.refl _ _⟩ hN ?_
  · refine Hs.mono h (by nlinarith) (fun b ⟨⟨h1, h2, h3⟩, _, _⟩ => ⟨by simpa using h1, h2, h3⟩)
  · intro k hk b ⟨⟨l1, l2, l3, l4, l5, l6, l7⟩, h2, h3⟩ hbk hbm
    have hx : L.drop k = L[k] :: L.drop (k + 1) := List.drop_eq_getElem_cons hk
    have hcw' : C.inp.drop b.ip = natWord L[k] ++ ((L.drop (k + 1)).flatMap natWord ++ rest) := by
      rw [l3, ← List.drop_drop, hcw]
      have : (L.flatMap natWord) = (L.take k).flatMap natWord ++ (L.drop k).flatMap natWord := by
        rw [← List.flatMap_append, List.take_append_drop]
      rw [this, List.append_assoc, List.drop_left, hx, List.flatMap_cons, List.append_assoc]
    have hrcb : b.rc sN = (b.ram sN).length := by
      rw [l1, l2]; simp
    refine Hs.mono (rdStore_spec b h2 L[k] _ hcw' (by have := hfit _ (List.getElem_mem hk); omega) hrcb)
      (by have := hfit _ (List.getElem_mem hk); omega) ?_
    rintro d ⟨d1, ⟨e1, e2, e3, e4, e5, e6, e7⟩, d3, d4⟩
    have htk : L.take (k + 1) = L.take k ++ [L[k]] := List.take_succ_eq_append_getElem hk
    refine ⟨⟨⟨?_, ?_, ?_, by rw [e4, l4], by rw [e5, l5], by rw [e6, l6], by rw [e7, l7]⟩, d3,
      Fr.trans h3 (Fr.weaken d4 (by decide))⟩, ?_, ?_⟩
    · rw [e1, l1, htk]; funext m; by_cases hm : m = sN
      · subst hm; simp
      · simp [Function.update_of_ne hm]
    · rw [e2, l2, htk]; funext m; by_cases hm : m = sN
      · subst hm; simp [l1]; omega
      · simp [Function.update_of_ne hm, l1]
    · rw [e3, l3, htk, List.flatMap_append, List.length_append]; omega
    · rw [d4 c1 (by decide), hbk]
    · rw [d4 cnt (fun h => hcnt (by simp only [readT, rdNatT, List.mem_cons, List.not_mem_nil] at h ⊢; tauto)), hbm]

theorem Loaded.trans {a b d : DS VV MM} {L1 L2 : List ℕ} (h1 : Loaded a b L1) (h2 : Loaded b d L2) :
    Loaded a d (L1 ++ L2) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h2
  refine ⟨?_, ?_, ?_, by rw [b4, a4], by rw [b5, a5], by rw [b6, a6], by rw [b7, a7]⟩
  · rw [b1, a1]; funext m; by_cases hm : m = sN
    · subst hm; simp
    · simp [Function.update_of_ne hm]
  · rw [b2, a2, a1]; funext m; by_cases hm : m = sN
    · subst hm; simp; omega
    · simp [Function.update_of_ne hm]
  · rw [b3, a3, List.flatMap_append, List.length_append]; omega

theorem Loaded.rc_eq {a b : DS VV MM} {L : List ℕ} (h : Loaded a b L) :
    b.rc sN = (b.ram sN).length := by
  rw [h.1, h.2.1]; simp

theorem Loaded.drop {a b : DS VV MM} {L R : List ℕ} {tail : List Bool} (h : Loaded a b L)
    (hcw : C.inp.drop a.ip = (L ++ R).flatMap natWord ++ tail) : C.inp.drop b.ip = R.flatMap natWord ++ tail := by
  rw [h.2.2.1, ← List.drop_drop, hcw, List.flatMap_append, List.append_assoc, List.drop_left]

/-- Read a counted list `[c] ++ X`, `|X| = s·c` with the stride `s` in `str`. -/
def readL (str : Fin VV) : St VV MM := .seq rdStore (.seq (.op (.mul t3 str lc)) (readF lc))

def readLT : List (Fin VV) := [c1, t0, t1, t2, t3, t4, vJ, lc]

theorem readL_spec (str : Fin VV) (hstr : str ∉ readLT) (a : DS VV MM) (hc : Cst a) (c : ℕ) (X : List ℕ)
    (rest : List Bool) (Λ : ℕ) (hcw : C.inp.drop a.ip = ([c] ++ X).flatMap natWord ++ rest)
    (hX : X.length = c * a.env str) (hfit : ∀ x ∈ [c] ++ X, natBitLength x ≤ Λ) (hΛ : Λ + 2 ≤ C.Wd)
    (hL : c * a.env str < 2 ^ C.Wd) (hrc : a.rc sN = (a.ram sN).length) :
    Hs C (readL str) a (30 * Λ + 32 + 1 + (1 + (X.length * (30 * Λ + 36) + 4) + 1) + 1)
      (fun b => Loaded a b ([c] ++ X) ∧ Cst b ∧ Fr a b readLT) := by
  have hc0 := hfit c (by simp)
  refine Hs.seq (Hs.mono (rdStore_spec a hc c (X.flatMap natWord ++ rest)
    (by rw [hcw, List.flatMap_append, List.append_assoc]; simp)
    (by omega) hrc) (by omega) (fun _ h => h)) (fun b ⟨b1, b2, b3, b4⟩ => ?_)
  have bstr : b.env str = a.env str := b4 str (fun h => hstr (by
    simp only [readLT, rdNatT, List.mem_cons, List.not_mem_nil] at h ⊢; tauto))
  refine Hs.seq (hs_mul C t3 str lc b (fun h => hstr (h ▸ by decide)) (by decide)
    (fun h => hstr (h ▸ by decide)) (by rw [b1, bstr]; exact hL)) (fun d hd => ?_)
  subst hd
  have hcw2 : C.inp.drop (b.set lc (b.env t3 * b.env str)).ip = X.flatMap natWord ++ rest :=
    Loaded.drop (R := X) b2 (by rw [hcw])
  refine Hs.mono (readF_spec lc (by decide) _ (Cst.of_fr b3 (Fr.set b (T := [lc]) _ (by decide)) (by decide)) X
    rest Λ hcw2 (by simp [DS.set, b1, bstr, hX]) (fun x hx => hfit x (by simp [hx])) hΛ
    (by rw [hX]; exact hL) (Loaded.rc_eq b2)) le_rfl ?_
  rintro e ⟨e1, e2, e3⟩
  refine ⟨Loaded.trans b2 e1, e2, ?_⟩
  refine Fr.trans (Fr.weaken b4 (by decide)) (Fr.trans (Fr.set b _ (by decide)) (Fr.weaken e3 (by decide)))

end NearCubicGates.Close.Cells
