import Proof.Gates.Dispatch.ParseCirc
import Proof.Gates.Counter.Params

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates.Close.Counter

variable {C : Ctx}

/-- What a flag test must do: set `fl := [P iv]`, keep `iv`, keep the invariant. -/
def FlagTest (C : Ctx) (test : St VV) (iv fl : Fin VV) (P : ℕ → Prop) [DecidablePred P] (Inv : DS VV → Prop)
    (tc B : ℕ) : Prop :=
  ∀ a : DS VV, Inv a → a.env iv ≤ B → Hs C test a tc (fun b => b.env fl = bnat (P (a.env iv)) ∧ b.env iv = a.env iv ∧ Inv b ∧
    b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out)

/-! ## Downward scan -/

def fgScan (iv fl : Fin VV) (test : St VV) : St VV :=
  .seq test (.loop (.lt fl v1) (.ite (.eq iv vZ) (.op (.copy fl v1)) (.seq (.op (.sub iv v1)) test)))

theorem fgScan_spec (iv fl : Fin VV) (hiv : iv ≠ vZ) (hfl : fl ≠ v1) (hivfl : iv ≠ fl) (hiv1 : iv ≠ v1)
    (test : St VV) (P : ℕ → Prop) [DecidablePred P] (Inv : DS VV → Prop) (tc : ℕ)
    (hI : ∀ b, Inv b → Cst b) (hIfl : ∀ b v, Inv b → Inv (b.set fl v)) (hIiv : ∀ b v, Inv b → Inv (b.set iv v))
    (B : ℕ) (ht : FlagTest C test iv fl P Inv tc B) (a : DS VV) (ha : Inv a) (hB : a.env iv = B) :
    Hs C (fgScan iv fl test) a (tc + ((B + 1) * (tc + 3 + 2) + 2) + 1) (fun b => b.env iv = Nat.findGreatest P B ∧
      Inv b ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out) := by
  let I : DS VV → Prop := fun b => ∃ j ≤ B, b.env iv = j ∧ (∀ k, j < k → k ≤ B → ¬ P k) ∧
    (b.env fl = bnat (P j) ∨ (j = 0 ∧ b.env fl = 1)) ∧ Inv b ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out
  let μ : DS VV → ℕ := fun b => b.env iv + (1 - b.env fl)
  have l := Hs.loopM (C := C) (c := .lt fl v1)
    (s := .ite (.eq iv vZ) (.op (.copy fl v1)) (.seq (.op (.sub iv v1)) test)) hfl I μ (tc + 3) (by
      rintro b ⟨j, hjB, h1, h2, h3, h4, h5, h6, h7⟩ he
      have hc := hI b h4
      have hfl0 : b.env fl = 0 := by simp only [Cnd.eval, hc.one, decide_eq_true_eq] at he; omega
      have hnP : ¬ P j := by
        rcases h3 with h | ⟨_, h⟩
        · rw [hfl0] at h; unfold bnat at h; intro hp; simp [hp] at h
        · omega
      refine Hs.ite (c := .eq iv vZ) hiv (fun hz => ?_) (fun hz => ?_)
      · have hj : j = 0 := by simp only [Cnd.eval, hc.z, decide_eq_true_eq, h1] at hz; exact hz
        refine Hs.mono (hs_copy C fl v1 b hfl) (by omega) ?_
        rintro d rfl
        refine ⟨⟨0, by omega, by rw [DS.set_env_ne _ _ hivfl, h1, hj], fun k hk hkB => by rw [← hj] at hk; exact h2 k hk hkB,
          Or.inr ⟨rfl, by rw [DS.set_env_self, hc.one]⟩, hIfl b _ h4, h5, h6, h7⟩, ?_⟩
        show (b.set fl (b.env v1)).env iv + (1 - (b.set fl (b.env v1)).env fl) < b.env iv + (1 - b.env fl)
        rw [DS.set_env_ne _ _ hivfl, DS.set_env_self, hc.one, hfl0]; omega
      · have hj : j ≠ 0 := by simp only [Cnd.eval, hc.z, decide_eq_false_iff_not, h1] at hz; exact hz
        refine Hs.mono (Hs.seq (t2 := tc) (hs_sub C iv v1 b hiv1 (by rw [hc.one, h1]; omega)) (fun d hd => ?_))
          (by omega) (fun _ h => h)
        subst hd
        have hd : Inv (b.set iv (b.env iv - b.env v1)) := hIiv b _ h4
        refine Hs.mono (ht _ hd (by rw [DS.set_env_self, h1, hc.one]; omega)) le_rfl ?_
        rintro e ⟨e1, e2, e3, e4, e5, e6⟩
        have hiv' : (b.set iv (b.env iv - b.env v1)).env iv = j - 1 := by rw [DS.set_env_self, h1, hc.one]
        rw [hiv'] at e1 e2
        refine ⟨⟨j - 1, by omega, e2, fun k hk hkB => ?_, Or.inl e1, e3, by rw [e4, ← h5]; rfl, by rw [e5, ← h6]; rfl,
          by rw [e6, ← h7]; rfl⟩, ?_⟩
        · rcases Nat.lt_or_ge j k with h | h
          · exact h2 k h hkB
          · have : k = j := by omega
            rw [this]; exact hnP
        · show e.env iv + (1 - e.env fl) < b.env iv + (1 - b.env fl)
          rw [e2, h1, hfl0]; omega)
  refine Hs.seq (ht a ha (by rw [hB])) (fun b ⟨b1, b2, b3, b4, b5, b6⟩ => ?_)
  have hIb : I b := ⟨B, le_rfl, by rw [b2, hB], fun k h1 h2 => by omega, Or.inl (by rw [b1, hB]), b3, b4, b5, b6⟩
  have hμ : μ b ≤ B + 1 := by show b.env iv + (1 - b.env fl) ≤ B + 1; rw [b2, hB]; omega
  refine Hs.mono (l b hIb) (by nlinarith) ?_
  rintro d ⟨⟨j, hjB, h1, h2, h3, h4, h5, h6, h7⟩, hstop⟩
  have hc := hI d h4
  have hfl1 : 1 ≤ d.env fl := by simp only [Cnd.eval, hc.one, decide_eq_false_iff_not] at hstop; omega
  refine ⟨?_, h4, h5, h6, h7⟩
  rw [h1, eq_comm, Nat.findGreatest_eq_iff]
  refine ⟨hjB, fun hj0 => ?_, fun k hk hkB => h2 k hk hkB⟩
  rcases h3 with h | ⟨h, _⟩
  · rw [h] at hfl1; unfold bnat at hfl1; by_contra hp; simp [hp] at hfl1
  · exact absurd h hj0

/-! ## Upward scan -/

def lsScan (iv fl bv : Fin VV) (test : St VV) : St VV :=
  .seq test (.loop (.lt fl v1) (.ite (.lt iv bv) (.seq (.op (.inc iv)) test) (.seq (.op (.inc iv)) (.op (.copy fl v2)))))

theorem lsScan_spec (iv fl bv : Fin VV) (hivbv : iv ≠ bv) (hfl : fl ≠ v1) (hfl2 : fl ≠ v2) (hivfl : iv ≠ fl)
    (test : St VV) (Q : ℕ → Prop) [DecidablePred Q] (Inv : DS VV → Prop) (tc : ℕ)
    (hI : ∀ b, Inv b → Cst b) (hIfl : ∀ b v, Inv b → Inv (b.set fl v)) (hIiv : ∀ b v, Inv b → Inv (b.set iv v))
    (B : ℕ) (ht : FlagTest C test iv fl Q Inv tc B) (hBW : B + 1 < 2 ^ C.Wd) (a : DS VV) (ha : Inv a)
    (h0 : a.env iv = 0) (hbv : ∀ b, Inv b → b.env bv = B) :
    Hs C (lsScan iv fl bv test) a (tc + ((B + 2) * (tc + 4 + 2) + 2) + 1) (fun b => Inv b ∧ b.cp = a.cp ∧
      b.wq = a.wq ∧ b.out = a.out ∧ (∀ s, s < b.env iv → s ≤ B → ¬ Q s) ∧
      ((b.env fl = 1 ∧ b.env iv ≤ B ∧ Q (b.env iv)) ∨ (b.env fl = 2 ∧ b.env iv = B + 1))) := by
  let I : DS VV → Prop := fun b => ∃ j ≤ B + 1, b.env iv = j ∧ (∀ s, s < j → s ≤ B → ¬ Q s) ∧
    ((j ≤ B ∧ b.env fl = bnat (Q j)) ∨ (b.env fl = 2 ∧ j = B + 1)) ∧ Inv b ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
    b.out = a.out
  let μ : DS VV → ℕ := fun b => (B + 1 - b.env iv) + (1 - b.env fl)
  have l := Hs.loopM (C := C) (c := .lt fl v1)
    (s := .ite (.lt iv bv) (.seq (.op (.inc iv)) test) (.seq (.op (.inc iv)) (.op (.copy fl v2)))) hfl I μ (tc + 4) (by
      rintro b ⟨j, hjB, h1, h2, h3, h4, h5, h6, h7⟩ he
      have hc := hI b h4
      have hfl0 : b.env fl = 0 := by simp only [Cnd.eval, hc.one, decide_eq_true_eq] at he; omega
      have hjle : j ≤ B := by rcases h3 with h | h
                              · exact h.1
                              · omega
      have hnQ : ¬ Q j := by
        rcases h3 with ⟨_, h⟩ | h
        · rw [hfl0] at h; unfold bnat at h; intro hq; simp [hq] at h
        · omega
      have hb : b.env bv = B := hbv b h4
      refine Hs.ite (c := .lt iv bv) hivbv (fun hz => ?_) (fun hz => ?_)
      · have hj : j < B := by simp only [Cnd.eval, decide_eq_true_eq, h1, hb] at hz; exact hz
        refine Hs.mono (Hs.seq (t2 := tc) (hs_inc C iv b (by rw [h1]; omega)) (fun d hd => ?_)) (by omega)
          (fun _ h => h)
        subst hd
        have hd : Inv (b.set iv (b.env iv + 1)) := hIiv b _ h4
        refine Hs.mono (ht _ hd (by rw [DS.set_env_self, h1]; omega)) le_rfl ?_
        rintro e ⟨e1, e2, e3, e4, e5, e6⟩
        have hiv' : (b.set iv (b.env iv + 1)).env iv = j + 1 := by rw [DS.set_env_self, h1]
        rw [hiv'] at e1 e2
        refine ⟨⟨j + 1, by omega, e2, fun s hs hsB => ?_, Or.inl ⟨by omega, e1⟩, e3, by rw [e4, ← h5]; rfl,
          by rw [e5, ← h6]; rfl, by rw [e6, ← h7]; rfl⟩, ?_⟩
        · rcases Nat.lt_or_ge s j with h | h
          · exact h2 s h hsB
          · have : s = j := by omega
            rw [this]; exact hnQ
        · show (B + 1 - e.env iv) + (1 - e.env fl) < (B + 1 - b.env iv) + (1 - b.env fl)
          rw [e2, h1, hfl0]; omega
      · have hj : j = B := by simp only [Cnd.eval, decide_eq_false_iff_not, not_lt, h1, hb] at hz; omega
        refine Hs.mono (Hs.seq (t2 := 1) (hs_inc C iv b (by rw [h1]; omega)) (fun d hd => ?_)) (by omega)
          (fun _ h => h)
        subst hd
        refine Hs.mono (hs_copy C fl v2 _ hfl2) le_rfl ?_
        rintro e rfl
        have hc' := hI _ (hIiv b (b.env iv + 1) h4)
        refine ⟨⟨B + 1, le_rfl, by rw [DS.set_env_ne _ _ hivfl, DS.set_env_self, h1, hj], fun s hs hsB => ?_,
          Or.inr ⟨by rw [DS.set_env_self, hc'.two], rfl⟩, hIfl _ _ (hIiv b _ h4), h5, h6, h7⟩, ?_⟩
        · rcases Nat.lt_or_ge s j with h | h
          · exact h2 s h hsB
          · have : s = j := by omega
            rw [this]; exact hnQ
        · show (B + 1 - ((b.set iv (b.env iv + 1)).set fl ((b.set iv (b.env iv + 1)).env v2)).env iv) +
            (1 - ((b.set iv (b.env iv + 1)).set fl ((b.set iv (b.env iv + 1)).env v2)).env fl) <
            (B + 1 - b.env iv) + (1 - b.env fl)
          rw [DS.set_env_ne _ _ hivfl, DS.set_env_self, DS.set_env_self, hc'.two, h1, hfl0]; omega)
  refine Hs.seq (ht a ha (by rw [h0]; omega)) (fun b ⟨b1, b2, b3, b4, b5, b6⟩ => ?_)
  rw [h0] at b1 b2
  have hIb : I b := ⟨0, by omega, b2, fun s hs _ => by omega, Or.inl ⟨by omega, b1⟩, b3, b4, b5, b6⟩
  have hμ : μ b ≤ B + 2 := by show (B + 1 - b.env iv) + (1 - b.env fl) ≤ B + 2; omega
  refine Hs.mono (l b hIb) (by nlinarith) ?_
  rintro d ⟨⟨j, hjB, h1, h2, h3, h4, h5, h6, h7⟩, hstop⟩
  have hc := hI d h4
  have hfl1 : 1 ≤ d.env fl := by simp only [Cnd.eval, hc.one, decide_eq_false_iff_not] at hstop; omega
  refine ⟨h4, h5, h6, h7, by rw [h1]; exact h2, ?_⟩
  rcases h3 with ⟨hj, h⟩ | ⟨h, hj⟩
  · left
    have hq : Q j := by rw [h] at hfl1; unfold bnat at hfl1; by_contra hq; simp [hq] at hfl1
    refine ⟨by rw [h]; unfold bnat; simp [hq], by omega, by rw [h1]; exact hq⟩
  · right; exact ⟨h, by omega⟩

/-- The two outcomes as `leastUpTo`. -/
theorem lsScan_found (Q : ℕ → Prop) [DecidablePred Q] (B t : ℕ) (hQ : Q t) (ht : t ≤ B)
    (hmin : ∀ s, s < t → s ≤ B → ¬ Q s) : leastUpTo Q B = some t :=
  leastUpTo_eq Q B t ht hQ (fun s hs => hmin s hs (by omega))

theorem lsScan_none (Q : ℕ → Prop) [DecidablePred Q] (B : ℕ) (hmin : ∀ s, s < B + 1 → s ≤ B → ¬ Q s) :
    leastUpTo Q B = none := by
  cases h : leastUpTo Q B with
  | none => rfl
  | some t =>
    obtain ⟨hq, htB, _⟩ := leastUpTo_spec Q B t h
    exact absurd hq (hmin t (by omega) htB)

end NearCubicGates.Close.Dispatch
