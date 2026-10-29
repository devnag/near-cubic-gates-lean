import SourceAdapters.Code.PairKeysStep

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid auxiliary-key enumeration. Pairing
uses two scratch registers, while its input index is the counted outer loop. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.PairKeys

open NearCubicGates.Close.Cells

def keys (row count : ℕ) : List ℕ :=
  (List.range count).map (fun i => 2 * Nat.pair row i + 1)

@[simp] theorem keys_length (row count : ℕ) : (keys row count).length = count := by simp [keys]

theorem keys_succ (row count : ℕ) :
    keys row (count + 1) = keys row count ++ [2 * Nat.pair row count + 1] := by
  simp [keys, List.range_succ]

def script (R : Fin 4 ↪ Fin VV) (address count : Fin VV) (store : Fin MM) : St VV MM :=
  forS (R 1) count (step R address store)

/-- Append exactly the row's odd paired auxiliary keys. Numeric values enter
only the fixed arithmetic body; the retained count is the sole loop bound. -/
theorem runs (C : Ctx) (R : Fin 4 ↪ Fin VV) (address count : Fin VV) (store : Fin MM)
    (ha : address ∉ [R 0, R 1, R 2, R 3])
    (hn : count ∉ [R 1, R 2, R 3, address])
    (hcst : vZ ∉ [R 1, R 2, R 3, address] ∧ v1 ∉ [R 1, R 2, R 3, address] ∧
      v2 ∉ [R 1, R 2, R 3, address])
    (a : DS VV MM) (hc : Cst a) (previous : List ℕ)
    (hprevious : a.ram store = previous) (hcursor : a.rc store = previous.length)
    (hcount : a.env count < 2 ^ C.Wd)
    (hwidth : ∀ i < a.env count, 2 * Nat.pair (a.env (R 0)) i + 1 < 2 ^ C.Wd) :
    Hs C (script R address count store) a (20 * a.env count + 4) (fun b =>
      b.ram store = previous ++ keys (a.env (R 0)) (a.env count) ∧
      b.rc store = previous.length + a.env count ∧
      b.env (R 0) = a.env (R 0) ∧ b.env count = a.env count ∧ b.env (R 1) = a.env count ∧
      Cst b ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      (∀ q, q ≠ store → b.ram q = a.ram q ∧ b.rc q = a.rc q) ∧
      Fr a b [R 1, R 2, R 3, address]) := by
  have ha0 : address ≠ R 0 := by intro h; apply ha; simp [h]
  have ha1 : address ≠ R 1 := by intro h; apply ha; simp [h]
  have ha3 : address ≠ R 3 := by intro h; apply ha; simp [h]
  have hni : count ≠ R 1 := by intro h; apply hn; simp [h]
  have hrow : R 0 ∉ [R 1, R 2, R 3, address] := by simp [ha0.symm]
  have hindex : R 1 ∉ [R 2, R 3, address] := by simp [ha1.symm]
  have sub : [R 2, R 3, address] ⊆ [R 1, R 2, R 3, address] :=
    fun _ h => List.mem_cons_of_mem (R 1) h
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ram = Function.update a.ram store (previous ++ keys (a.env (R 0)) k) ∧
    b.rc = Function.update a.rc store (previous.length + k) ∧
    b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
    Fr a b [R 1, R 2, R 3, address]
  have initial : I 0 a := by
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
    · funext q
      by_cases hq : q = store
      · subst q; simpa [keys] using hprevious
      · simp [hq]
    · funext q
      by_cases hq : q = store
      · subst q; simpa using hcursor
      · simp [hq]
  have loopRun := forS_spec' (C := C) (R 1) count hni.symm (step R address store)
    a (a.env count) hcount I 16
    (fun k b v ⟨bm, br, bi, bo, bki, bko, bkc, bf⟩ =>
      ⟨bm, br, bi, bo, bki, bko, bkc, bf.trans (Fr.set b v (by simp))⟩)
    initial rfl ?_
  · refine Hs.mono loopRun (by omega) ?_
    rintro b ⟨⟨bm, br, bi, bo, bki, bko, bkc, bf⟩, bindex, bcount⟩
    refine ⟨?_, ?_, bf (R 0) hrow, bcount, bindex, Cst.of_fr hc bf hcst,
      bi, bo, bki, bko, bkc, ?_, bf⟩
    · rw [bm, Function.update_self]
    · rw [br, Function.update_self]
    · intro q hq
      rw [bm, br, Function.update_of_ne hq, Function.update_of_ne hq]
      exact ⟨rfl, rfl⟩
  · intro k hk b ⟨bm, br, bi, bo, bki, bko, bkc, bf⟩ bindex bcount
    have stepRun := step_spec C R address store ha3 b (a.env (R 0)) k
      (bf (R 0) hrow) bindex (hwidth k hk) (by rw [br, bm]; simp)
    refine Hs.mono stepRun le_rfl ?_
    rintro d ⟨dm, dr, di, dout, dki, dko, dkc, df⟩
    refine ⟨⟨?_, ?_, di.trans bi, dout.trans bo, dki.trans bki, dko.trans bko, dkc.trans bkc,
      bf.trans (df.weaken sub)⟩, (df (R 1) hindex).trans bindex,
      (df count (fun h => hn (sub h))).trans bcount⟩
    · rw [dm, bm, keys_succ]
      funext q
      by_cases hq : q = store
      · subst q; simp [List.append_assoc]
      · simp [hq]
    · rw [dr, br]
      funext q
      by_cases hq : q = store
      · subst q; simp [Nat.add_assoc]
      · simp [hq]

end NearCubicGates.Adapters.Code.PairKeys
