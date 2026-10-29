import SourceAdapters.RAMACSP.GenItemsB5

/-!
# Variables read and depths of the copy, boundary and input-record printers

The conditions of `comp_spec` (`WF baseA`) and of the compiler (`Ok 0`) for the blocks (B1)–(B5): every expression
reads only the request numbers, the layout masks, the coordinate array and the loop variables in scope, and the
expression and loop depths stay below the compiler's limits.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMTrace NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary

/-- The variables in scope inside a lane-carry loop. -/
def itemAT (x : Var) : Prop := itemA x ∨ x = vT

theorem itemA_dec (x : Var) : itemA x ↔ (((20 ≤ x.val ∧ x.val ≤ 36) ∨ x = 44 ∨ x = 45 ∨ x = 48 ∨ x = 49 ∨ x = 52) ∨
    x = 50) ∨ x = 46 := Iff.rfl

instance (x : Var) : Decidable (itemA x) := decidable_of_iff _ (itemA_dec x).symm
instance (x : Var) : Decidable (itemAT x) := by unfold itemAT; infer_instance

/-- Expressions on literal variables: reads decided. -/
def rdB (ok : Var → Bool) : E → Bool
  | .v i => ok i
  | .k _ | .gk => true
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .shl a b | .shr a b | .bxor a b | .fadd a b
  | .fmul a b | .fpow a b | .lt a b | .eq a b => rdB ok a && rdB ok b
  | .finv a => rdB ok a

/-- `WF` as a Boolean check. -/
def wfB : (Var → Bool) → P → Bool
  | _, .nil => true
  | A, .num e => rdB A e
  | A, .seq a b => wfB A a && wfB A b
  | A, .loop i n b => rdB A n && decide (20 ≤ i.val) && !A i && wfB (fun x => A x || x == i) b
  | A, .bind i e b => rdB A e && decide (20 ≤ i.val) && !A i && wfB (fun x => A x || x == i) b
  | A, .ite c a b => rdB A c && wfB A a && wfB A b

theorem rdE_of_rdB' {A : Var → Prop} (ok : Var → Bool) (hok : ∀ x, ok x = true → A x) :
    ∀ e : E, rdB ok e = true → RdE A e
  | .v i, h => hok i (by simpa [rdB] using h)
  | .k _, _ => trivial
  | .gk, _ => trivial
  | .add a b, h | .sub a b, h | .mul a b, h | .div a b, h | .md a b, h | .shl a b, h | .shr a b, h
  | .bxor a b, h | .lt a b, h | .eq a b, h | .fadd a b, h | .fmul a b, h | .fpow a b, h => by
    simp only [rdB, Bool.and_eq_true] at h
    exact ⟨rdE_of_rdB' ok hok a h.1, rdE_of_rdB' ok hok b h.2⟩
  | .finv a, h => rdE_of_rdB' ok hok a h

/-- `wfB` gives `WF` for any readable set agreeing with the Boolean one. -/
theorem wf_of_wfB : ∀ (p : P) (A : Var → Prop) (ok : Var → Bool), (∀ x, ok x = true ↔ A x) → wfB ok p = true → WF A p
  | .nil, _, _, _, _ => trivial
  | .num e, A, ok, hA, h => rdE_of_rdB' ok (fun x hx => (hA x).mp hx) e h
  | .seq a b, A, ok, hA, h => by
    simp only [wfB, Bool.and_eq_true] at h
    exact ⟨wf_of_wfB a A ok hA h.1, wf_of_wfB b A ok hA h.2⟩
  | .loop i n b, A, ok, hA, h => by
    simp only [wfB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨rdE_of_rdB' ok (fun x hx => (hA x).mp hx) n h1, h2, fun hi => by rw [← hA] at hi; simp [hi] at h3,
      wf_of_wfB b _ _ (fun x => ?_) h4⟩
    simp only [Bool.or_eq_true, beq_iff_eq, hA]
  | .bind i e b, A, ok, hA, h => by
    simp only [wfB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨rdE_of_rdB' ok (fun x hx => (hA x).mp hx) e h1, h2, fun hi => by rw [← hA] at hi; simp [hi] at h3,
      wf_of_wfB b _ _ (fun x => ?_) h4⟩
    simp only [Bool.or_eq_true, beq_iff_eq, hA]
  | .ite c a b, A, ok, hA, h => by
    simp only [wfB, Bool.and_eq_true] at h
    exact ⟨rdE_of_rdB' ok (fun x hx => (hA x).mp hx) c h.1.1, wf_of_wfB a A ok hA h.1.2, wf_of_wfB b A ok hA h.2⟩

/-- `Ok` as a Boolean check. -/
def okB : ℕ → P → Bool
  | _, .nil => true
  | d, .num e => decide (dE e < 16) && decide (d < 8)
  | d, .seq a b => okB d a && okB d b
  | d, .loop _ n b => decide (dE n < 16) && decide (d < 8) && okB (d + 1) b
  | d, .bind _ e b => decide (dE e < 16) && okB d b
  | d, .ite c a b => decide (dE c < 16) && okB d a && okB d b

theorem ok_of_okB : ∀ (d : ℕ) (p : P), okB d p = true → Ok d p
  | _, .nil, _ => trivial
  | d, .num e, h => by simpa [okB, Ok] using h
  | d, .seq a b, h => by
    simp only [okB, Bool.and_eq_true] at h; exact ⟨ok_of_okB d a h.1, ok_of_okB d b h.2⟩
  | d, .loop _ n b, h => by
    simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, ok_of_okB (d + 1) b h.2⟩
  | d, .bind _ e b, h => by
    simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, ok_of_okB d b h.2⟩
  | d, .ite c a b, h => by
    simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, ok_of_okB d a h.1.2, ok_of_okB d b h.2⟩

/-- The Boolean form of `baseA`. -/
def baseB (x : Var) : Bool :=
  decide (20 ≤ x.val ∧ x.val ≤ 36) || x == vKL || x == vUK || x == vP5 || x == vP6 || x == vD

theorem baseB_iff (x : Var) : baseB x = true ↔ baseA x := by
  simp only [baseB, baseA, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  tauto

/-! ## The blocks -/

theorem wf_piece (c : Cnt) (jk : JK) (body : P)
    (hb : wfB (fun x => (baseB x || x == vI) || x == vJ) body = true) : WF baseA (Pc.prog ⟨c, jk, body⟩) := by
  apply wf_of_wfB _ baseA baseB baseB_iff
  simp only [Pc.prog, wfB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨⟨⟨?_, by decide⟩, by decide⟩, ⟨⟨?_, by decide⟩, by decide⟩, hb⟩
  · cases c <;> rfl
  · cases jk <;> rfl

theorem ok_piece (c : Cnt) (jk : JK) (body : P) (hb : okB 1 body = true) : Ok 0 (Pc.prog ⟨c, jk, body⟩) :=
  ok_of_okB 0 _ (by
    simp only [Pc.prog, okB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨dE_cnt c, by norm_num⟩, dE_jk jk, hb⟩)

variable (V : Verifier)

attribute [local irreducible] refList

theorem WF_cpBlock : WF baseA (cpBlockP V) := by
  apply WF_seqL
  intro p hp
  obtain ⟨pc, -, rfl⟩ := List.mem_map.mp hp
  exact wf_piece _ _ _ rfl

theorem Ok_cpBlock : Ok 0 (cpBlockP V) := by
  apply Ok_seqL
  intro p hp
  obtain ⟨pc, -, rfl⟩ := List.mem_map.mp hp
  exact ok_piece _ _ _ rfl

theorem all_eSetS_any (A : Var → Prop) (K L : ℕ) (Q : MI V (RamCodeWord.refW V) → Bool) :
    (eSetS V K L Q).All (Good A) := by
  apply all_sxSum
  intro i a _
  split_ifs
  · exact ⟨trivial, by simp [k0, dE]⟩
  · trivial

/-- The variables in scope inside the (B3) loop. -/
def b3A (x : Var) : Prop := baseA x ∨ x = vT

theorem WF_b3 : WF baseA (b3P V) := by
  have hT : ¬ baseA vT := by unfold baseA vT vKL vUK vP5 vP6 vD; decide
  have hlay : ∀ x, layA x → b3A x := fun x hx => Or.inl (layA_baseA x hx)
  have hlay' : ∀ x, layA x → baseA x := layA_baseA
  have hb35 : baseA 35 := Or.inl ⟨by decide, by decide⟩
  have hvA : ¬ baseA vA := by unfold baseA vA vKL vUK vP5 vP6 vD; decide
  have hh : SC.Rd b3A h3 := trivial
  have hh' : SC.Rd baseA h3 := trivial
  refine ⟨⟨Or.inl ⟨by decide, by decide⟩, by decide, hT, ?_⟩, ?_⟩
  · refine WF_itemP (Or.inl hb35) (fun h => h.elim hvA (by decide)) _ _ _ ?_ ?_
      (WF_tokP hlay h3 hh _ (all_eSetS_any V b3A (regCount V) (codeLen V) isOut).rd)
    · exact rdE_of_rdB' (fun x => baseB x || x == vT) (fun x hx => by
        simp only [Bool.or_eq_true, beq_iff_eq] at hx
        exact hx.elim (fun h => Or.inl ((baseB_iff x).mp h)) Or.inr) _ rfl
    · exact rdE_of_rdB' (fun x => baseB x || x == vT) (fun x hx => by
        simp only [Bool.or_eq_true, beq_iff_eq] at hx
        exact hx.elim (fun h => Or.inl ((baseB_iff x).mp h)) Or.inr) _ rfl
  · refine WF_itemP hb35 hvA _ _ _ ?_ ?_ (WF_tokP hlay' h3 hh' _ ⟨(all_eSetS_any V baseA (regCount V) (codeLen V) isAcc).rd, trivial⟩)
    · exact rdE_of_rdB' baseB (fun x hx => (baseB_iff x).mp hx) _ rfl
    · exact rdE_of_rdB' baseB (fun x hx => (baseB_iff x).mp hx) _ rfl

theorem Ok_b3 : Ok 0 (b3P V) := by
  have hh : h3.Dp := show dE k0 ≤ 3 by simp [k0, dE]
  refine ⟨⟨by simp [dE], by norm_num, ?_⟩, ?_⟩
  · exact Ok_itemP (by norm_num) _ _ _ (by simp [knE, lcE, pow1E, dE]) (dE_vaE _ _ _ hh (by simp [pow1E, dE])
      (by simp [k0, dE])) (Ok_tokP (by norm_num) _ hh _ (all_eSetS_any V itemA (regCount V) (codeLen V) isOut).dp)
  · exact Ok_itemP (by norm_num) _ _ _ (by simp [knE, fkE, pow1E, dE]) (dE_vaE _ _ _ hh (by simp [dE])
      (by simp [k0, dE])) (Ok_tokP (by norm_num) _ hh _ ⟨(all_eSetS_any V itemA (regCount V) (codeLen V) isAcc).dp, trivial⟩)

theorem WF_b4 : WF baseA b4P := by
  apply WF_seqL
  intro p hp
  simp only [b4P, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact wf_piece _ _ _ rfl

theorem Ok_b4 : Ok 0 b4P := by
  apply Ok_seqL
  intro p hp
  simp only [b4P, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ok_piece _ _ _ rfl

theorem WF_b5 : WF baseA b5P := by
  apply WF_seqL
  intro p hp
  simp only [b5P, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact wf_piece _ _ _ rfl

theorem Ok_b5 : Ok 0 b5P := by
  apply Ok_seqL
  intro p hp
  simp only [b5P, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ok_piece _ _ _ rfl

end NearCubicGates.Adapters.RAMACSP.Gen.Items

