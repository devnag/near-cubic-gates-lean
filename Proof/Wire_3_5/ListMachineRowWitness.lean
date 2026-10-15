import Proof.Wire_3_5.ListMachineRowsI
import Proof.Wire_3_5.ListMachineRows
import Proof.Wire_3_5.FinalPassPopBridge
import Proof.Wire_3_5.FinalPassListEvalBridge

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly pone pmul psum eval_pmul eval_psum eval_pone
  eval_congr_atoms listBit listBit_eq listBound listBound_ge)
open NearCubicWires.WireExponent3_5.FinalPass

/-! ## Substitution -/

/-- A monomial with every atom `i` replaced by `g i` (the product). -/
def msubst (g : ℕ → Poly) (m : List ℕ) : Poly := m.foldr (fun i acc => pmul (g i) acc) pone

/-- **Substitution**: every atom `i` replaced by the polynomial `g i`. -/
def psubst (p : Poly) (g : ℕ → Poly) : Poly := psum (p.map (msubst g))

theorem eval_msubst (g : ℕ → Poly) (m : List ℕ) (ρ : ℕ → Bool) :
    F2Poly.eval (msubst g m) ρ = m.all fun i => F2Poly.eval (g i) ρ := by
  induction m with
  | nil => simp [msubst]
  | cons i m ih => simp only [msubst, List.foldr_cons] at ih ⊢; rw [eval_pmul, ih]; simp

theorem eval_psubst (p : Poly) (g : ℕ → Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (psubst p g) ρ = F2Poly.eval p fun i => F2Poly.eval (g i) ρ := by
  unfold psubst
  rw [eval_psum]
  induction p with
  | nil => rfl
  | cons m p ih =>
    rw [List.map_cons, List.foldr_cons, ih, eval_msubst, NearCubicWires.WireExponent3_5.ListMachine.eval_cons]

theorem msubst_deg (g : ℕ → Poly) (e : ℕ) (hg : ∀ i, DegLe (g i) e) :
    ∀ m : List ℕ, DegLe (msubst g m) (e * m.length) := by
  intro m
  induction m with
  | nil => intro m' hm'; simp [msubst, pone] at hm'; subst hm'; simp
  | cons i m ih =>
    intro m' hm'
    simp only [msubst, List.foldr_cons, pmul, List.mem_flatMap, List.mem_map] at hm'
    obtain ⟨a, ha, b, hb, rfl⟩ := hm'
    have h1 := hg i a ha
    have h2 := ih b hb
    simp only [List.length_append, List.length_cons]
    rw [Nat.mul_succ]; omega

theorem msubst_atoms (g : ℕ → Poly) (N : ℕ) (hg : ∀ i, AtomsLt (g i) N) :
    ∀ m : List ℕ, AtomsLt (msubst g m) N := by
  intro m
  induction m with
  | nil => intro m' hm' x hx; simp [msubst, pone] at hm'; subst hm'; simp at hx
  | cons i m ih =>
    intro m' hm' x hx
    simp only [msubst, List.foldr_cons, pmul, List.mem_flatMap, List.mem_map] at hm'
    obtain ⟨a, ha, b, hb, rfl⟩ := hm'
    rcases List.mem_append.mp hx with h | h
    · exact hg i a ha x h
    · exact ih b hb x h

theorem psubst_deg (p : Poly) (g : ℕ → Poly) (d e : ℕ) (hp : DegLe p d) (hg : ∀ i, DegLe (g i) e) :
    DegLe (psubst p g) (e * d) := by
  intro m hm
  simp only [psubst, NearCubicWires.WireExponent3_5.ListMachine.psum, List.mem_flatten, List.mem_map] at hm
  obtain ⟨q, ⟨m0, hm0, rfl⟩, hmq⟩ := hm
  exact (msubst_deg g e hg m0 m hmq).trans (Nat.mul_le_mul_left e (hp m0 hm0))

theorem psubst_atoms (p : Poly) (g : ℕ → Poly) (N : ℕ) (hg : ∀ i, AtomsLt (g i) N) : AtomsLt (psubst p g) N := by
  intro m hm
  simp only [psubst, NearCubicWires.WireExponent3_5.ListMachine.psum, List.mem_flatten, List.mem_map] at hm
  obtain ⟨q, ⟨m0, _, rfl⟩, hmq⟩ := hm
  exact msubst_atoms g N hg m0 m hmq

theorem psubst_atoms' (p : Poly) (g : ℕ → Poly) (L N : ℕ) (hp : AtomsLt p L) (hg : ∀ i < L, AtomsLt (g i) N) :
    AtomsLt (psubst p g) N := by
  intro m hm
  simp only [psubst, NearCubicWires.WireExponent3_5.ListMachine.psum, List.mem_flatten, List.mem_map] at hm
  obtain ⟨q, ⟨m0, hm0, rfl⟩, hmq⟩ := hm
  have key : ∀ m0 : List ℕ, (∀ i ∈ m0, i < L) → AtomsLt (msubst g m0) N := by
    intro m0 h0
    induction m0 with
    | nil => intro m' hm' x hx; simp [msubst, pone] at hm'; subst hm'; simp at hx
    | cons i m0 ih =>
      intro m' hm' x hx
      simp only [msubst, List.foldr_cons, pmul, List.mem_flatMap, List.mem_map] at hm'
      obtain ⟨a, ha, b, hb, rfl⟩ := hm'
      rcases List.mem_append.mp hx with h | h
      · exact hg i (h0 i List.mem_cons_self) a ha x h
      · exact ih (fun j hj => h0 j (List.mem_cons_of_mem _ hj)) b hb x h
  exact key m0 (hp m0 hm0) m hmq

/-! ## The corner forms -/

def cornerPoly (sgn : Bool) (q : ℕ) : Poly :=
  (if sgn then Stars.zPlusF2 else Stars.zMinusF2).map fun m => m.map fun k => 4 * q + k.val

theorem eval_rename4 (p : F2Poly (Fin 4)) (f : Fin 4 → ℕ) (ρ : ℕ → Bool) :
    F2Poly.eval (p.map fun m => m.map f) ρ = F2Poly.eval p fun k => ρ (f k) := by
  unfold F2Poly.eval
  rw [List.foldl_map]
  congr 1
  funext acc m
  rw [List.all_map]
  rfl

theorem eval_cornerPoly (sgn : Bool) (q : ℕ) (ρ : ℕ → Bool) :
    F2Poly.eval (cornerPoly sgn q) ρ =
      F2Poly.eval (if sgn then Stars.zPlusF2 else Stars.zMinusF2) fun k : Fin 4 => ρ (4 * q + k.val) :=
  eval_rename4 _ _ ρ

theorem cornerPoly_deg (sgn : Bool) (q : ℕ) : DegLe (cornerPoly sgn q) 3 := by
  intro m hm
  simp only [cornerPoly, List.mem_map] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  rw [List.length_map]
  cases sgn <;> simp [Stars.zPlusF2, Stars.zMinusF2] at hm0 <;> rcases hm0 with h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> simp

theorem cornerPoly_atoms (sgn : Bool) (q : ℕ) : AtomsLt (cornerPoly sgn q) (4 * q + 4) := by
  intro m hm i hi
  simp only [cornerPoly, List.mem_map] at hm
  obtain ⟨m0, _, rfl⟩ := hm
  simp only [List.mem_map] at hi
  obtain ⟨k, _, rfl⟩ := hi
  have := k.isLt
  omega

/-! ## The witness -/

/-- **The list state over the corner pool**: `stateRef D L s` with each coordinate replaced by its corner form. -/
def witness35 (D : ListData) (L s : ℕ) (sgn : Bool) : Poly := psubst (stateRef D L s) (cornerPoly sgn)

theorem witness35_deg (D : ListData) (L s : ℕ) (sgn : Bool) : DegLe (witness35 D L s sgn) (3 * listBound D) := by
  have h := psubst_deg (stateRef D L s) (cornerPoly sgn) _ 3 (stateRef_size D L s).1 (cornerPoly_deg sgn)
  exact h.mono (Nat.mul_le_mul_left 3 (listBound_ge D))

theorem witness35_atoms (D : ListData) (L s : ℕ) (sgn : Bool) : AtomsLt (witness35 D L s sgn) (4 * L) :=
  psubst_atoms' (stateRef D L s) (cornerPoly sgn) L (4 * L) (stateRef_size D L s).2
    (fun q hq m hm i hi => by have := cornerPoly_atoms sgn q m hm i hi; omega)

theorem corner_witness (D : ListData) (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true) (L s : ℕ)
    (hs : s ≤ D.M) (sgn : Bool) (X : List Bool) (hX : X.length = 4 * L) :
    decide (ListEval.reportRef D.M D.J D.W (ListEval.rowsOf D L) (Pop.popBits sgn X) = s) =
      F2Poly.eval (witness35 D L s sgn) fun i => X.getD i false := by
  have hZ := Pop.popBits_length sgn L X hX
  rw [ListEval.reportRef_eq_fast D L _ hZ]
  have hl := listBit_eq D hnest L s hs (Pop.popBits sgn X) hZ
  unfold listBit at hl
  rw [hl, witness35, eval_psubst]
  apply eval_congr_atoms (stateRef_size D L s).2
  intro q hq
  rw [eval_cornerPoly]
  have hq' : q < (Pop.popBits sgn X).length := by rw [hZ]; exact hq
  rw [List.getD_eq_getElem _ _ hq', Pop.popBits_getElem sgn L X hX q hq]
  congr 1
  funext k
  rw [List.getD_eq_getElem _ _ (by have := k.isLt; omega)]

end NearCubicWires.WireExponent3_5.ListMachine.Row
