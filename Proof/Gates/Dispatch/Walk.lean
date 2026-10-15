import Proof.Gates.Dispatch.Macros

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

variable {C : Ctx}

theorem flatMap_drop_get {α : Type} (xs : List α) (g : α → List Bool) (k : ℕ) (hk : k < xs.length) :
    (xs.drop k).flatMap g = g xs[k] ++ (xs.drop (k + 1)).flatMap g := by
  rw [List.drop_eq_getElem_cons hk, List.flatMap_cons]

theorem flatMap_take_len {α : Type} (xs : List α) (g : α → List Bool) (k : ℕ) (hk : k < xs.length) :
    ((xs.take (k + 1)).flatMap g).length = ((xs.take k).flatMap g).length + (g xs[k]).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList, List.flatMap_append, List.length_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- **The list walk.** -/
theorem walk {α : Type} (xs : List α) (g : α → List Bool) (iv nv : Fin VV) (hin : iv ≠ nv) (body : St VV)
    (P : ℕ → DS VV → Prop) (tb : ℕ) (rest : List Bool)
    (hP : ∀ k b v, P k b → P k (b.set iv v))
    (hb : ∀ k (hk : k < xs.length) (a : DS VV), P k a → a.env iv = k → a.env nv = xs.length →
       C.cw.drop a.cp = g xs[k] ++ ((xs.drop (k + 1)).flatMap g ++ rest) →
       Hs C body a tb (fun b => P (k + 1) b ∧ b.env iv = k ∧ b.env nv = xs.length ∧ b.cp = a.cp + (g xs[k]).length))
    (hlen : xs.length < 2 ^ C.Wd) :
    ∀ a, P 0 a → a.env iv = 0 → a.env nv = xs.length → C.cw.drop a.cp = xs.flatMap g ++ rest →
      Hs C (.loop (.lt iv nv) (.seq body (.op (.inc iv)))) a (xs.length * (tb + 2 + 2) + 2)
        (fun b => P xs.length b ∧ b.env iv = xs.length ∧ b.env nv = xs.length ∧
          b.cp = a.cp + (xs.flatMap g).length) := by
  intro a0 h0 hi0 hn0 hd0
  let I : ℕ → DS VV → Prop := fun k a => P k a ∧ a.env iv = k ∧ a.env nv = xs.length ∧
    C.cw.drop a.cp = (xs.drop k).flatMap g ++ rest ∧ a.cp = a0.cp + ((xs.take k).flatMap g).length
  have l := Hs.loopN (C := C) (c := .lt iv nv) (s := .seq body (.op (.inc iv))) hin I xs.length (tb + 2) ?_ ?_ a0
    ⟨h0, hi0, hn0, by simpa using hd0, by simp⟩
  · refine Hs.mono l le_rfl ?_
    rintro b ⟨b1, b2, b3, _, b5⟩
    exact ⟨b1, b2, b3, by rw [b5, List.take_length]⟩
  · intro k hk a ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by simp [Cnd.eval, h2, h3, hk], ?_⟩
    rw [flatMap_drop_get xs g k hk, List.append_assoc] at h4
    refine Hs.seq (hb k hk a h1 h2 h3 h4) (fun b ⟨b1, b2, b3, b4⟩ => ?_)
    refine Hs.mono (hs_inc C iv b (by rw [b2]; omega)) le_rfl ?_
    rintro d rfl
    refine ⟨hP _ _ _ b1, by simp [b2], by rw [DS.set_env_ne _ _ (Ne.symm hin), b3], ?_, ?_⟩
    · show C.cw.drop b.cp = _
      rw [b4, ← List.drop_drop, h4, List.drop_left]
    · show b.cp = _
      rw [b4, h5, flatMap_take_len xs g k hk]; ring
  · intro a ⟨_, h2, h3, _⟩
    simp [Cnd.eval, h2, h3]

/-! ## Integers -/

def readInt : St VV := .seq readNat (.seq (.op (.copy t8 t3)) readNat)

def readIntT : List (Fin VV) := [t0, t1, t2, t3, t4, t8, vJ, vPOS]

theorem natBitLength_le_len (v : ℕ) : natBitLength v ≤ (natWord v).length := by
  rw [natWord_length]; omega

theorem readInt_spec (a : DS VV) (hc : Cst a) (z : ℤ) (rest : List Bool)
    (hcw : C.cw.drop a.cp = Interfaces.intWord z ++ rest) (hW : C.cw.length + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C readInt a (60 * (Interfaces.intWord z).length + 70) (fun b => b.env t8 = (if z < 0 then 1 else 0) ∧
      b.env t3 = z.natAbs ∧ b.env t4 = natBitLength z.natAbs ∧ b.cp = a.cp + (Interfaces.intWord z).length ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b readIntT) := by
  have hz : Interfaces.intWord z = natWord (if z < 0 then 1 else 0) ++ natWord z.natAbs := rfl
  have hlen := congrArg List.length hcw
  rw [List.length_drop, List.length_append, hz, List.length_append] at hlen
  have hb1 := natBitLength_le_len (if z < 0 then 1 else 0)
  have hb2 := natBitLength_le_len z.natAbs
  rw [hz, List.append_assoc] at hcw
  refine Hs.mono (Hs.seq (readNat_spec a hc _ _ hcw (by omega) hL) (fun b ⟨b1, b2, b3, b4, b5, b6, b7⟩ => ?_))
    (show 30 * natBitLength (if z < 0 then 1 else 0) + 30 + (1 + (30 * natBitLength z.natAbs + 30) + 1) + 1 ≤ _ by
      rw [hz, List.length_append]; omega) (fun _ h => h)
  refine Hs.seq (hs_copy C t8 t3 b (by decide)) (fun d hd => ?_)
  subst hd
  have hcw2 : C.cw.drop (b.set t8 (b.env t3)).cp = natWord z.natAbs ++ rest := by
    show C.cw.drop b.cp = _
    rw [b3, ← List.drop_drop, hcw, List.drop_left]
  have dc : Cst (b.set t8 (b.env t3)) :=
    Cst.of_fr (T := [t8]) b6 (Fr.set b _ (by decide)) (by decide) (by vsimp [b6.pos])
  refine Hs.mono (readNat_spec _ dc _ _ hcw2 (by omega) hL) le_rfl ?_
  rintro e ⟨e1, e2, e3, e4, e5, e6, e7⟩
  refine ⟨by rw [e7 t8 (by decide)]; vsimp [b1], e1, e2, ?_, by rw [e4]; exact b4, by rw [e5]; exact b5, e6, ?_⟩
  · rw [e3]; show b.cp + _ = _; rw [b3, hz, List.length_append]; ring
  · exact Fr.trans (Fr.weaken b7 (by decide)) (Fr.trans (Fr.set b _ (by decide)) (Fr.weaken e7 (by decide)))

end NearCubicGates.Close.Dispatch
