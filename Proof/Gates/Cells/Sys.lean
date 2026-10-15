import Proof.Gates.Cells.Enum
import Proof.Gates.Cells.Recs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

/-! ## Lists listing functions -/

theorem list_eq_map_idx {α : Type} [DecidableEq α] (l : List α) (hl : l.Nodup) (F : List ℚ)
    (hF : F.length = l.length) : F = l.map (fun x => F.getD (l.idxOf x) 0) := by
  apply List.ext_getElem (by simp [hF])
  intro i h1 h2
  simp only [List.getElem_map]
  rw [hl.idxOf_getElem i (by simpa using h2), List.getD_eq_getElem _ _ h1]

theorem zip_map_self {α β : Type} (l : List α) (g : α → β) : l.zip (l.map g) = l.map (fun x => (x, g x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem sum_filter_zip {α : Type} [DecidableEq α] (l : List α) (hl : l.Nodup) (g : α → ℚ) (P : α → Bool) :
    (((l.zip (l.map g)).filter fun xf => P xf.1).map Prod.snd).sum = ∑ x ∈ l.toFinset.filter (fun x => P x), g x := by
  rw [zip_map_self, List.filter_map, List.map_map]
  rw [← List.sum_toFinset _ (hl.filter _), List.toFinset_filter]
  rfl

theorem mem_vecsM' : ∀ (bs v : List ℕ), v ∈ vecsM bs ↔ v.length = bs.length ∧ ∀ i < v.length, v.getD i 0 < bs.getD i 0
  | [], v => by
    simp only [vecsM, List.mem_singleton, List.length_nil]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, _⟩; exact List.eq_nil_of_length_eq_zero h
  | b :: bs, v => by
    simp only [vecsM, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨a, ha, w, hw, rfl⟩
      obtain ⟨h1, h2⟩ := (mem_vecsM' bs w).1 hw
      refine ⟨by simp [h1], fun i hi => ?_⟩
      cases i with
      | zero => simpa using ha
      | succ i => simpa using h2 i (by simpa using hi)
    · rintro ⟨h1, h2⟩
      cases v with
      | nil => simp at h1
      | cons a w =>
        refine ⟨a, by simpa using h2 0 (by simp), w, (mem_vecsM' bs w).2 ⟨by simpa using h1, fun i hi => ?_⟩, rfl⟩
        simpa using h2 (i + 1) (by simpa using hi)

theorem getD_map_finRange {n : ℕ} (f : Fin n → ℕ) (i : ℕ) (hi : i < n) :
    ((List.finRange n).map f).getD i 0 = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map, List.getElem_finRange]; rfl

/-! ## The box as a list of points -/

section Box
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ)

/-- The side lengths of the box. -/
def boxLens : List ℕ :=
  (List.finRange (roleCount c.kind)).map fun r => (boxHi c p wt y κ r - boxLo c p wt y κ r + 1).toNat

/-- The point of offsets `v`. -/
def ptOf (v : List ℕ) : Role c → ℤ := fun r => boxLo c p wt y κ r + (v.getD r.val 0 : ℤ)

/-- The points of the box, in mixed-radix order. -/
def ptsOf : List (Role c → ℤ) := (vecsM (boxLens c p wt y κ)).map (ptOf c p wt y κ)

theorem boxLens_length : (boxLens c p wt y κ).length = roleCount c.kind := by simp [boxLens]

theorem boxLens_getD (r : Role c) :
    (boxLens c p wt y κ).getD r.val 0 = (boxHi c p wt y κ r - boxLo c p wt y κ r + 1).toNat := by
  simp [boxLens, List.getD_eq_getElem?_getD]

theorem mem_ptsOf (u : Role c → ℤ) : u ∈ ptsOf c p wt y κ ↔ u ∈ box c p wt y κ := by
  simp only [ptsOf, List.mem_map, box, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨v, hv, rfl⟩ r
    obtain ⟨h1, h2⟩ := (mem_vecsM' _ v).1 hv
    have := h2 r.val (by rw [h1, boxLens_length]; exact r.isLt)
    rw [boxLens_getD] at this
    simp only [ptOf]
    omega
  · intro hu
    refine ⟨(List.finRange (roleCount c.kind)).map fun r => (u r - boxLo c p wt y κ r).toNat, ?_, ?_⟩
    · refine (mem_vecsM' _ _).2 ⟨by simp [boxLens_length], fun i hi => ?_⟩
      simp only [List.length_map, List.length_finRange] at hi
      have := hu ⟨i, hi⟩
      rw [boxLens_getD c p wt y κ ⟨i, hi⟩, getD_map_finRange _ i hi]
      omega
    · funext r
      have := hu r
      simp only [ptOf]
      rw [getD_map_finRange _ r.val r.isLt]
      have e : (⟨r.val, r.isLt⟩ : Fin (roleCount c.kind)) = r := rfl
      rw [e]
      omega

theorem ptsOf_nodup : (ptsOf c p wt y κ).Nodup := by
  refine (vecsM_nodup _).map_on ?_
  intro v hv w hw h
  obtain ⟨hv1, -⟩ := (mem_vecsM' _ v).1 hv
  obtain ⟨hw1, -⟩ := (mem_vecsM' _ w).1 hw
  rw [boxLens_length] at hv1 hw1
  apply List.ext_getElem (by rw [hv1, hw1])
  intro i h1 h2
  have := congrFun h ⟨i, by omega⟩
  simp only [ptOf, add_right_inj, Nat.cast_inj] at this
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem ptsOf_toFinset : (ptsOf c p wt y κ).toFinset = box c p wt y κ := by
  ext u; rw [List.mem_toFinset, mem_ptsOf]

end Box

/-! ## The system -/

section System
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (κ : Role c × Fin p.J → ℤ)

/-- The rows: every prime (increasing), every residue vector `σ` (lexicographic), the tabulated joint count. -/
def rowsOf (part : Option Bool) : List (ℕ × List ℕ × ℕ) :=
  (p.primes.sort (· ≤ ·)).flatMap fun q => (vecs q (roleCount c.kind)).map fun σl =>
    (q, σl, jointCount c p wt q part y κ (fun r => (σl.getD r.val 0 : ℤ)))

def sysOf (part : Option Bool) : SysReq :=
  ⟨(ptsOf c p wt y κ).map (fun u => List.ofFn u), rowsOf c p wt y κ part⟩

theorem ofFn_inj {d : ℕ} : Function.Injective (fun u : Fin d → ℤ => List.ofFn u) := fun _ _ h => List.ofFn_injective h

theorem inClass_ofFn (q : ℕ) (σl : List ℕ) (hσ : σl.length = roleCount c.kind) (u : Role c → ℤ) :
    inClass q σl (List.ofFn u) = true ↔ ∀ r : Role c, u r ≡ (σl.getD r.val 0 : ℤ) [ZMOD (q : ℤ)] := by
  unfold inClass
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq, hσ]
  constructor
  · intro h r
    have := h r.val r.isLt
    rwa [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn] at this
  · intro h i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
    exact h ⟨i, hi⟩

/-- The function listed by `F` on the points. -/
noncomputable def funOf (F : List ℚ) : (Role c → ℤ) → ℚ := fun u =>
  F.getD (@List.idxOf (List ℤ) instBEqOfDecidableEq (List.ofFn u) ((ptsOf c p wt y κ).map fun u => List.ofFn u)) 0

theorem pts_nodup : ((ptsOf c p wt y κ).map fun u => List.ofFn u).Nodup :=
  (ptsOf_nodup c p wt y κ).map ofFn_inj

/-- The row sum of `F` is the box sum of the function it lists. -/
theorem rowSum (part : Option Bool) (F : List ℚ) (hF : F.length = (ptsOf c p wt y κ).length) (q : ℕ) (σl : List ℕ)
    (hσ : σl.length = roleCount c.kind) :
    ((((sysOf c p wt y κ part).pts.zip F).filter fun uf => inClass q σl uf.1).map Prod.snd).sum =
      ∑ u ∈ (box c p wt y κ).filter (fun u => ∀ r : Role c, u r ≡ (σl.getD r.val 0 : ℤ) [ZMOD (q : ℤ)]),
        funOf c p wt y κ F u := by
  set L := (ptsOf c p wt y κ).map fun u => List.ofFn u with hL
  have hnd := pts_nodup c p wt y κ
  have hF' : F.length = L.length := by rw [hF, hL, List.length_map]
  have e := list_eq_map_idx L hnd F hF'
  show (((L.zip F).filter fun uf => inClass q σl uf.1).map Prod.snd).sum = _
  conv_lhs => rw [e]
  rw [sum_filter_zip L hnd _ (fun pl => inClass q σl pl)]
  have hTF : L.toFinset = (box c p wt y κ).image (fun u => List.ofFn u) := by
    ext pl; simp only [List.mem_toFinset, Finset.mem_image, hL, List.mem_map, mem_ptsOf]
  rw [hTF, Finset.filter_image, Finset.sum_image (fun u _ v _ h => ofFn_inj h)]
  apply Finset.sum_congr
  · ext u; simp only [Finset.mem_filter]; rw [inClass_ofFn c q σl hσ u]
  · intro u _; rfl

theorem mem_vecs_iff (q d : ℕ) (σl : List ℕ) : σl ∈ vecs q d ↔ σl.length = d ∧ ∀ i < σl.length, σl.getD i 0 < q := by
  rw [vecs_eq_vecsM, mem_vecsM']
  simp only [List.length_replicate]
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨h1, fun i hi => ?_⟩
    have e : (List.replicate d q).getD i 0 = q := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; omega), List.getElem_replicate]
    have := h2 i hi; rwa [e] at this
  · rintro ⟨h1, h2⟩; refine ⟨h1, fun i hi => ?_⟩
    have e : (List.replicate d q).getD i 0 = q := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; omega), List.getElem_replicate]
    rw [e]; exact h2 i hi

theorem jointCount_cast (q : ℕ) (part : Option Bool) (σ : Role c → Fin q) :
    jointCount c p wt q part y κ (fun r => ((List.ofFn fun r => (σ r : ℕ)).getD r.val 0 : ℤ)) =
      jointCount c p wt q part y κ (fun r => (σ r : ℤ)) := by
  congr 1; funext r
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem sysSolves_iff (part : Option Bool) (F : List ℚ) (hF : F.length = (ptsOf c p wt y κ).length) :
    SysSolves (sysOf c p wt y κ part) F ↔ Solves c p wt part y κ (funOf c p wt y κ F) := by
  constructor
  · rintro ⟨_, hrows⟩ q hq σ
    have hrow : (q, List.ofFn (fun r => (σ r : ℕ)), jointCount c p wt q part y κ
        (fun r => ((List.ofFn fun r => (σ r : ℕ)).getD r.val 0 : ℤ))) ∈ (sysOf c p wt y κ part).rows := by
      simp only [sysOf, rowsOf, List.mem_flatMap, List.mem_map, Finset.mem_sort]
      refine ⟨q, hq, _, (mem_vecs_iff _ _ _).2 ⟨by simp, fun i hi => ?_⟩, rfl⟩
      simp only [List.length_ofFn] at hi
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]; exact (σ ⟨i, hi⟩).isLt
    have h := hrows _ hrow
    rw [rowSum c p wt y κ part F hF q _ (by simp), jointCount_cast] at h
    rw [← h]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext u; simp only [Finset.mem_filter]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, fun r => ?_⟩ <;> have := h2 r <;>
      rwa [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn] at *
  · intro hS
    refine ⟨by simp [sysOf, hF], fun row hrow => ?_⟩
    simp only [sysOf, rowsOf, List.mem_flatMap, List.mem_map, Finset.mem_sort] at hrow
    obtain ⟨q, hq, σl, hσl, rfl⟩ := hrow
    obtain ⟨hlen, hlt⟩ := (mem_vecs_iff _ _ _).1 hσl
    let σ : Role c → Fin q := fun r => ⟨σl.getD r.val 0, hlt r.val (by rw [hlen]; exact r.isLt)⟩
    have h := hS q hq σ
    rw [rowSum c p wt y κ part F hF q σl hlen]
    exact h

theorem funOf_map (g : (Role c → ℤ) → ℚ) (u : Role c → ℤ) (hu : u ∈ ptsOf c p wt y κ) :
    funOf c p wt y κ ((ptsOf c p wt y κ).map g) u = g u := by
  unfold funOf
  have hnd := pts_nodup c p wt y κ
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  set L := (ptsOf c p wt y κ).map fun u => List.ofFn u
  have hi' : i < L.length := by simpa [L] using hi
  have e : List.ofFn (ptsOf c p wt y κ)[i] = L[i] := by simp [L]
  have h1 : @List.idxOf (List ℤ) instBEqOfDecidableEq L[i] L = i := by
    have := hnd.idxOf_getElem i hi'
    convert this
  rw [e, h1, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

theorem solve_sysOf {cT : ℕ} (S : SolveMachine) (hs : Spec cT (header c) p) (ht : CellTests c p wt y)
    (part : Option Bool) (hκ : κ ∈ digitVectors c p wt y) :
    S.solve (sysOf c p wt y κ part) = some ((ptsOf c p wt y κ).map (trueDist c p wt y part κ)) := by
  set T := (ptsOf c p wt y κ).map (trueDist c p wt y part κ) with hT
  have hTsolves : SysSolves (sysOf c p wt y κ part) T := by
    refine (sysSolves_iff c p wt y κ part T (by simp [hT])).2 ?_
    intro q hq σ
    rw [← trueDist_solves c p wt y hs ht part κ hκ q hq σ]
    apply Finset.sum_congr rfl
    intro u hu
    exact funOf_map c p wt y κ _ u ((mem_ptsOf c p wt y κ u).2 (Finset.mem_filter.mp hu).1)
  cases hsol : S.solve (sysOf c p wt y κ part) with
  | none => exact absurd hTsolves (S.complete _ hsol T)
  | some F =>
    have hF := S.sound _ F hsol
    have hlen : F.length = (ptsOf c p wt y κ).length := by
      have := hF.1; simpa [sysOf] using this
    have hS := (sysSolves_iff c p wt y κ part F hlen).1 hF
    have heq := solution_eq_trueDist c p wt y hs ht part κ hκ _ hS
    congr 1
    have e := list_eq_map_idx _ (pts_nodup c p wt y κ) F (by simpa using hlen)
    rw [e, List.map_map, hT]
    apply List.map_congr_left
    intro u hu
    exact heq u ((mem_ptsOf c p wt y κ u).1 hu)

end System

end NearCubicGates.Close.Cells
