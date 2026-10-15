import Proof.Gates.Cells.Kit

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

variable {C : Ctx}

/-- Loop counters reserved for the macros of this file. -/
def c0 : Fin VV := ⟨14, by decide⟩

/-! ## Counted loops -/

/-- `for i := 0 to m − 1 do body`. -/
def forS (i m : Fin VV) (body : St VV MM) : St VV MM :=
  .seq (.op (.zero i)) (.loop (.lt i m) (.seq body (.op (.inc i))))

theorem forS_spec (i m : Fin VV) (him : i ≠ m) (body : St VV MM) (a : DS VV MM) (N : ℕ) (hN : N < 2 ^ C.Wd)
    (I : ℕ → DS VV MM → Prop) (t : ℕ → ℕ) (hIi : ∀ k b v, I k b → I k (b.set i v)) (h0 : I 0 a)
    (hm : a.env m = N)
    (hstep : ∀ k < N, ∀ b, I k b → b.env i = k → b.env m = N →
      Hs C body b (t k) (fun d => I (k + 1) d ∧ d.env i = k ∧ d.env m = N)) :
    Hs C (forS i m body) a (1 + ((∑ k ∈ Finset.range N, (t k + 4)) + 2) + 1)
      (fun b => I N b ∧ b.env i = N ∧ b.env m = N) := by
  refine Hs.seq (hs_zero C i a) (fun b hb => ?_)
  subst hb
  have := Hs.loopNc (C := C) (c := .lt i m) (s := .seq body (.op (.inc i))) him
    (fun k b => I k b ∧ b.env i = k ∧ b.env m = N) N (fun k => t k + 2) ?_ ?_ (a.set i 0)
    ⟨hIi 0 a 0 h0, by simp [DS.set], by rw [DS.set_env_ne _ _ (Ne.symm him)]; exact hm⟩
  · refine Hs.mono this (by gcongr with k; try omega) (fun _ h => h)
  · intro k hk b ⟨hI, hi, hmb⟩
    refine ⟨by simp [Cnd.eval, hi, hmb, hk], ?_⟩
    refine Hs.seq (t1 := t k) (t2 := 1) (hstep k hk b hI hi hmb) (fun d ⟨hd, hdi, hdm⟩ => ?_)
    refine Hs.mono (hs_inc C i d (by rw [hdi]; omega)) le_rfl ?_
    rintro e rfl
    exact ⟨hIi _ _ _ hd, by simp [DS.set, hdi], by rw [DS.set_env_ne _ _ (Ne.symm him)]; exact hdm⟩
  · intro b ⟨_, hi, hmb⟩
    simp [Cnd.eval, hi, hmb]

/-- Uniform per-pass cost. -/
theorem forS_spec' (i m : Fin VV) (him : i ≠ m) (body : St VV MM) (a : DS VV MM) (N : ℕ) (hN : N < 2 ^ C.Wd)
    (I : ℕ → DS VV MM → Prop) (t : ℕ) (hIi : ∀ k b v, I k b → I k (b.set i v)) (h0 : I 0 a)
    (hm : a.env m = N)
    (hstep : ∀ k < N, ∀ b, I k b → b.env i = k → b.env m = N →
      Hs C body b t (fun d => I (k + 1) d ∧ d.env i = k ∧ d.env m = N)) :
    Hs C (forS i m body) a (N * (t + 4) + 4) (fun b => I N b ∧ b.env i = N ∧ b.env m = N) := by
  refine Hs.mono (forS_spec i m him body a N hN I (fun _ => t) hIi h0 hm hstep) ?_ (fun _ h => h)
  simp [Finset.sum_const]; omega

/-! ## Store access -/

/-- The record at index `x` of store `m` into `d` (`c0` counts, `vJ` takes the skipped records). -/
def fetch (m : Fin MM) (x d : Fin VV) : St VV MM :=
  .seq (.op (.rwM m)) (.seq (forS c0 x (.op (.rdM m vJ))) (.op (.rdM m d)))

theorem fetch_spec (m : Fin MM) (x d : Fin VV) (hx0 : x ≠ c0) (hxJ : x ≠ vJ) (a : DS VV MM)
    (hlt : a.env x < (a.ram m).length) (hW : a.env x < 2 ^ C.Wd) :
    Hs C (fetch m x d) a (a.rc m + 5 * a.env x + 9) (fun b => b.env d = (a.ram m).getD (a.env x) 0 ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = Function.update a.rc m (a.env x + 1) ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [c0, vJ, d]) := by
  set N := a.env x with hNdef
  refine Hs.mono (Hs.seq (hs_rwM C m a) (fun b hb => ?_)) (show a.rc m + 1 + (N * (1 + 4) + 4 + 1 + 1) + 1 ≤ _
    by omega) (fun _ h => h)
  subst hb
  let I : ℕ → DS VV MM → Prop := fun k e => e.ip = a.ip ∧ e.out = a.out ∧ e.ram = a.ram ∧
    e.rc = Function.update a.rc m k ∧ e.kin = a.kin ∧ e.kout = a.kout ∧ e.kc = a.kc ∧ Fr a e [c0, vJ, d]
  have hl := forS_spec' (C := C) c0 x (Ne.symm hx0) (.op (.rdM m vJ)) (a.rew m) N hW I 1
    (fun k e v ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, h7,
      Fr.trans h8 (Fr.set e v (List.mem_cons_self ..))⟩)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩ rfl ?_
  · refine Hs.seq (t1 := N * (1 + 4) + 4) (t2 := 1) hl (fun e ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, _, _⟩ => ?_)
    refine Hs.mono (hs_rdM C m d e (by rw [h4, h3]; simp; omega)) le_rfl ?_
    rintro f rfl
    refine ⟨by simp [DS.adv, DS.set, h3, h4], by simp [DS.adv, DS.set, h1], by simp [DS.adv, DS.set, h2],
      by simp [DS.adv, DS.set, h3], ?_, by simp [DS.adv, DS.set, h5], by simp [DS.adv, DS.set, h6],
      by simp [DS.adv, DS.set, h7], ?_⟩
    · simp [DS.adv, DS.set, h4]
    · exact Fr.trans h8 (fun y hy => by
        simp only [DS.adv, DS.set]
        rw [Function.update_of_ne]; intro h; apply hy; rw [h]; simp)
  · intro k hk e ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ hek hem
    refine Hs.mono (hs_rdM C m vJ e (by rw [h4, h3]; simp; omega)) le_rfl ?_
    rintro f rfl
    refine ⟨⟨by simp [DS.adv, DS.set, h1], by simp [DS.adv, DS.set, h2], by simp [DS.adv, DS.set, h3],
      by simp [DS.adv, DS.set, h4], by simp [DS.adv, DS.set, h5], by simp [DS.adv, DS.set, h6],
      by simp [DS.adv, DS.set, h7], Fr.trans h8 (fun y hy => by
        simp only [DS.adv, DS.set]
        rw [Function.update_of_ne]; intro h; apply hy; rw [h]; simp)⟩, ?_, ?_⟩
    · simp only [DS.adv, DS.set]; rw [Function.update_of_ne (by decide)]; exact hek
    · simp only [DS.adv, DS.set]; rw [Function.update_of_ne hxJ]; exact hem

end NearCubicGates.Close.Cells
