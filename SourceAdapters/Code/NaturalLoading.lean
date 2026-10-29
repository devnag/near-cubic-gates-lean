import Proof.Gates.Cells.Load

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid input loading of a counted list of natural-number words
into an arbitrary store. The loop counts records and each parser counts bits. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.NaturalLoading

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

/-- Read one `natWord` (into `t3`) and append it to the target store. -/
def step (store : Fin MM) : St VV MM := .seq rdNatI (.op (.wrM store t3))

/-- Read `cnt` naturals. -/
def script (store : Fin MM) (cnt : Fin VV) : St VV MM := forS c1 cnt (step store)

/-- The non-variable part after reading `L` from the cursor. -/
def Loaded (store : Fin MM) (a b : DS VV MM) (L : List ℕ) : Prop :=
  b.ram = Function.update a.ram store (a.ram store ++ L) ∧ b.rc = Function.update a.rc store ((a.ram store).length + L.length) ∧
    b.ip = a.ip + (L.flatMap natWord).length ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc

theorem step_runs (C : Ctx) (store : Fin MM) (a : DS VV MM) (hc : Cst a) (x : ℕ) (rest : List Bool)
    (hcw : C.inp.drop a.ip = natWord x ++ rest) (hW : natBitLength x + 2 ≤ C.Wd)
    (hrc : a.rc store = (a.ram store).length) :
    Hs C (step store) a (30 * natBitLength x + 32) (fun b => b.env t3 = x ∧ Loaded store a b [x] ∧ Cst b ∧ Fr a b rdNatT) := by
  refine Hs.mono (Hs.seq (t1 := 30 * natBitLength x + 30) (t2 := 1) (rdNatI_spec a hc x rest hcw hW)
    (fun b ⟨h1, _, h3, h4, h5⟩ => ?_)) (by omega)
    (fun _ h => h)
  simp only [Prod.mk.injEq] at h4
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := h4
  refine Hs.mono (hs_wrM C store t3 b (by rw [o3, o2, hrc])) le_rfl ?_
  rintro d rfl
  refine ⟨by simp [DS.put, h1], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, cst_fr hc h5, ?_⟩
  · simp only [DS.put, o2, o3, hrc, h1]
    funext m; by_cases hm : m = store
    · subst hm; simp [putAt]
    · simp [Function.update_of_ne hm]
  · simp only [DS.put, o3, o2]
    funext m; by_cases hm : m = store
    · subst hm; simp [hrc]
    · simp [Function.update_of_ne hm]
  · simp [DS.put, h3]
  · simp [DS.put, o1]
  · simp [DS.put, o4]
  · simp [DS.put, o5]
  · simp [DS.put, o6]
  · exact h5

theorem append_runs (C : Ctx) (store : Fin MM) (cnt : Fin VV) (hcnt : cnt ∉ readT) (a : DS VV MM) (hc : Cst a) (L : List ℕ) (rest : List Bool)
    (Λ : ℕ) (hcw : C.inp.drop a.ip = L.flatMap natWord ++ rest) (hN : a.env cnt = L.length)
    (hfit : ∀ x ∈ L, natBitLength x ≤ Λ) (hΛ : Λ + 2 ≤ C.Wd) (hL : L.length < 2 ^ C.Wd)
    (hrc : a.rc store = (a.ram store).length) :
    Hs C (script store cnt) a (L.length * (30 * Λ + 36) + 4) (fun b => Loaded store a b L ∧ Cst b ∧ Fr a b readT) := by
  have hc1 : c1 ≠ cnt := fun h => hcnt (h ▸ by decide)
  let I : ℕ → DS VV MM → Prop := fun k b => Loaded store a b (L.take k) ∧ Cst b ∧ Fr a b readT
  have h := forS_spec' (C := C) c1 cnt hc1 (step store) a L.length hL I (30 * Λ + 32)
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
    have hrcb : b.rc store = (b.ram store).length := by
      rw [l1, l2]; simp
    refine Hs.mono (step_runs C store b h2 L[k] _ hcw' (by have := hfit _ (List.getElem_mem hk); omega) hrcb)
      (by have := hfit _ (List.getElem_mem hk); omega) ?_
    rintro d ⟨d1, ⟨e1, e2, e3, e4, e5, e6, e7⟩, d3, d4⟩
    have htk : L.take (k + 1) = L.take k ++ [L[k]] := List.take_succ_eq_append_getElem hk
    refine ⟨⟨⟨?_, ?_, ?_, by rw [e4, l4], by rw [e5, l5], by rw [e6, l6], by rw [e7, l7]⟩, d3,
      Fr.trans h3 (Fr.weaken d4 (by decide))⟩, ?_, ?_⟩
    · rw [e1, l1, htk]; funext m; by_cases hm : m = store
      · subst hm; simp
      · simp [Function.update_of_ne hm]
    · rw [e2, l2, htk]; funext m; by_cases hm : m = store
      · subst hm; simp [l1]; omega
      · simp [Function.update_of_ne hm, l1]
    · rw [e3, l3, htk, List.flatMap_append, List.length_append]; omega
    · rw [d4 c1 (by decide), hbk]
    · rw [d4 cnt (fun h => hcnt (by simp only [readT, rdNatT, List.mem_cons, List.not_mem_nil] at h ⊢; tauto)), hbm]

/-- Load an exact natural-word list into an initially empty target store. -/
theorem runs (C : Ctx) (store : Fin MM) (count : Fin VV) (hcount : count ∉ readT)
    (a : DS VV MM) (hc : Cst a) (records : List ℕ) (rest : List Bool) (Λ : ℕ)
    (hin : C.inp.drop a.ip = records.flatMap natWord ++ rest)
    (hlen : a.env count = records.length)
    (hfit : ∀ x ∈ records, natBitLength x ≤ Λ) (hΛ : Λ + 2 ≤ C.Wd)
    (hwidth : records.length < 2 ^ C.Wd)
    (hempty : a.ram store = []) (hcursor : a.rc store = 0) :
    Hs C (script store count) a (records.length * (30 * Λ + 36) + 4) (fun b =>
      b.ram store = records ∧ b.rc store = records.length ∧ b.env count = records.length ∧
      b.ip = a.ip + (records.flatMap natWord).length ∧ Cst b ∧ b.out = a.out ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      (∀ q, q ≠ store → b.ram q = a.ram q ∧ b.rc q = a.rc q) ∧ Fr a b readT) := by
  have h := append_runs C store count hcount a hc records rest Λ hin hlen hfit hΛ hwidth
    (by rw [hempty, hcursor]; rfl)
  refine Hs.mono h le_rfl ?_
  rintro b ⟨⟨bm, br, bi, bo, bki, bko, bkc⟩, bc, bf⟩
  refine ⟨?_, ?_, (bf count hcount).trans hlen, bi, bc, bo, bki, bko, bkc, ?_, bf⟩
  · rw [bm, Function.update_self, hempty]; rfl
  · rw [br, Function.update_self, hempty]; simp
  · intro q hq
    rw [bm, br, Function.update_of_ne hq, Function.update_of_ne hq]
    exact ⟨rfl, rfl⟩

end NearCubicGates.Adapters.Code.NaturalLoading
