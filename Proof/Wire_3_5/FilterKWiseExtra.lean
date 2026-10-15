import Proof.Wire_3_5.FilterKWise

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Shared Finset

/-- **S3 `IdentityKWise`**: independent uniform labels are `t`-wise uniform. -/
theorem identityKWise : IdentityKWise := by
  intro L V _ _ _ _ t ls _ val
  have key : (Fintype.piFinset fun l => if l ∈ ls then ({val l} : Finset V) else Finset.univ).card *
      Fintype.card V ^ ls.card = Fintype.card (L → V) := by
    rw [Fintype.card_piFinset, Fintype.card_fun]
    have : ∀ l, (if l ∈ ls then ({val l} : Finset V) else Finset.univ).card =
        if l ∈ ls then 1 else Fintype.card V := by
      intro l; split_ifs <;> simp
    rw [Finset.prod_congr rfl fun l _ => this l, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset L)) (fun l => l ∈ ls)
    have hin : (Finset.univ.filter fun l => l ∈ ls).card = ls.card := by congr 1; ext l; simp
    rw [hin, Finset.card_univ] at hc
    rw [← pow_add, add_comm]
    congr 1
  convert key using 3
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · intro h l; split_ifs with hl
    · simp [h l hl]
    · exact Finset.mem_univ _
  · intro h l hl; have := h l; rw [if_pos hl] at this; simpa using this

/-- **S3 `ProjectKWise`**: a surjective additive projection of a `t`-wise uniform family is `t`-wise uniform. -/
theorem projectKWise : ProjectKWise := by
  intro S L V W _ _ _ _ _ _ _ t f π hπ hk ls hls val
  classical
  set m := ls.card
  -- the fibers of `π` all have `|V|/|W|` elements
  have hfib : ∀ y : W, (Finset.univ.filter fun v : V => π v = y).card * Fintype.card W = Fintype.card V := by
    intro y
    have hall : ∀ z : W, (Finset.univ.filter fun v : V => π v = z).card =
        (Finset.univ.filter fun v : V => π v = y).card := fun z =>
      AddMonoidHom.card_fiber_eq_of_mem_range π (hπ z) (hπ y)
    have hsum := Finset.card_eq_sum_card_fiberwise (f := fun v => π v) (s := (Finset.univ : Finset V))
      (t := (Finset.univ : Finset W)) (fun _ _ => Finset.mem_univ _)
    rw [Finset.sum_congr rfl fun z _ => hall z, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
    rw [Finset.card_univ] at hsum
    rw [hsum]; ring
  -- group the seeds by their values on `ls`
  let key : S → (ls → V) := fun s l => f s l
  let good : Finset (ls → V) := Fintype.piFinset fun l => Finset.univ.filter fun v : V => π v = val l
  have hcount : ∀ w : ls → V, (Finset.univ.filter fun s => key s = w).card * Fintype.card V ^ m = Fintype.card S := by
    intro w
    let v0 : V := 0
    let vall : L → V := fun l => if h : l ∈ ls then w ⟨l, h⟩ else v0
    have h := hk ls hls vall
    have heq : (Finset.univ.filter fun s => key s = w) = Finset.univ.filter fun s => ∀ l ∈ ls, f s l = vall l := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, key, vall]
      constructor
      · intro hs l hl; rw [dif_pos hl, ← hs]
      · intro hs; funext l; have := hs l l.2; rw [dif_pos l.2] at this; exact this
    rw [heq]; exact h
  have htarget : (Finset.univ.filter fun s => ∀ l ∈ ls, π (f s l) = val l) =
      Finset.univ.filter fun s => key s ∈ good := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, good, key, Fintype.mem_piFinset]
    constructor
    · intro h l; exact h l l.2
    · intro h l hl; exact h ⟨l, hl⟩
  rw [htarget]
  have hsplit : (Finset.univ.filter fun s => key s ∈ good).card =
      ∑ w ∈ good, (Finset.univ.filter fun s => key s = w).card := by
    have hfw := Finset.card_eq_sum_card_fiberwise (f := key) (s := Finset.univ.filter fun s => key s ∈ good)
      (t := good) (fun s hs => (Finset.mem_filter.mp hs).2)
    rw [hfw]
    refine Finset.sum_congr rfl fun w hw => ?_
    congr 1; ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨h ▸ hw, h⟩
  have hgood : good.card * Fintype.card W ^ m = Fintype.card V ^ m := by
    simp only [good, Fintype.card_piFinset]
    have hm : (Finset.univ : Finset ls).card = m := by rw [Finset.card_univ, Fintype.card_coe]
    calc (∏ l : ls, (Finset.univ.filter fun v : V => π v = val l).card) * Fintype.card W ^ m
        = ∏ l : ls, ((Finset.univ.filter fun v : V => π v = val l).card * Fintype.card W) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hm]
      _ = ∏ _l : ls, Fintype.card V := Finset.prod_congr rfl fun l _ => hfib (val l)
      _ = Fintype.card V ^ m := by rw [Finset.prod_const, hm]
  have hVpos : 0 < Fintype.card V ^ m := pow_pos Fintype.card_pos _
  have htot : (Finset.univ.filter fun s => key s ∈ good).card * Fintype.card V ^ m = good.card * Fintype.card S := by
    rw [hsplit, Finset.sum_mul, Finset.sum_congr rfl fun w _ => hcount w, Finset.sum_const, smul_eq_mul]
  apply Nat.eq_of_mul_eq_mul_right hVpos
  calc (Finset.univ.filter fun s => key s ∈ good).card * Fintype.card W ^ m * Fintype.card V ^ m
      = ((Finset.univ.filter fun s => key s ∈ good).card * Fintype.card V ^ m) * Fintype.card W ^ m := by ring
    _ = good.card * Fintype.card S * Fintype.card W ^ m := by rw [htot]
    _ = (good.card * Fintype.card W ^ m) * Fintype.card S := by ring
    _ = Fintype.card S * Fintype.card V ^ m := by rw [hgood]; ring

/-! ## The moment transfer (S3.1): the draft statement needs a nonempty seed space -/

/-- The draft statement `ExpectEqIndep` is false as written: with an empty seed space every family is vacuously
`t`-wise uniform, while the mean over the empty seed space is `0` and the fully independent mean of the constant `1`
is `1`. -/
theorem not_expectEqIndep : ¬ ExpectEqIndep := by
  intro h
  have hk : KWiseUniform 0 (fun (s : Fin 0) (_ : Unit) => (Fin.elim0 s : Unit)) := by
    intro ls hls val
    have : ls = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    simp
  have := h 0 (fun (s : Fin 0) (_ : Unit) => (Fin.elim0 s : Unit)) hk ∅ (by simp) (fun _ => 1)
    (fun _ _ _ => rfl)
  simp [uMean] at this

theorem expectEqIndep_of_nonempty {S L V : Type} [Fintype S] [Fintype L] [Fintype V] [DecidableEq V]
    [DecidableEq L] [Nonempty S] (t : ℕ) (f : S → L → V) (hk : KWiseUniform t f) (ls : Finset L)
    (hls : ls.card ≤ t) (g : (L → V) → ℝ) (hg : ReadsOnly ls g) :
    uMean (fun s => g (f s)) = uMean (fun w : L → V => g w) := by
  set d : L → V := f (Classical.arbitrary S)
  let ext : (ls → V) → (L → V) := fun v l => if h : l ∈ ls then v ⟨l, h⟩ else d l
  -- the fiber sum for any `t`-wise uniform family
  have hfam : ∀ {T : Type} [Fintype T] (F : T → L → V), KWiseUniform t F →
      (∑ x, g (F x)) * (Fintype.card V : ℝ) ^ ls.card = Fintype.card T * ∑ v : ls → V, g (ext v) := by
    intro T _ F hF
    let key : T → (ls → V) := fun x l => F x l
    have hcount : ∀ v : ls → V, ((Finset.univ.filter fun x => key x = v).card : ℝ) *
        (Fintype.card V : ℝ) ^ ls.card = Fintype.card T := by
      intro v
      have h := hF ls hls (ext v)
      have heq : (Finset.univ.filter fun x => key x = v) = Finset.univ.filter fun x => ∀ l ∈ ls, F x l = ext v l := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, key, ext]
        constructor
        · intro hx l hl; rw [dif_pos hl, ← hx]
        · intro hx; funext l; have := hx l l.2; rw [dif_pos l.2] at this; exact this
      rw [heq]
      norm_cast
      convert h using 3
      ext x; simp only [Finset.mem_filter]
    have hread : ∀ x, g (F x) = g (ext (key x)) := by
      intro x; apply hg; intro l hl; simp [ext, key, hl]
    simp only [hread]
    rw [← Finset.sum_fiberwise Finset.univ key (fun x => g (ext (key x))), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2], Finset.sum_const, nsmul_eq_mul,
      mul_right_comm, hcount v, mul_comm]
  have h1 := hfam f hk
  have h2 := hfam (fun (w : L → V) (l : L) => w l) (identityKWise t)
  have hS : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  have hW : (0 : ℝ) < Fintype.card (L → V) := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨d⟩)
  have hVm : (0 : ℝ) < (Fintype.card V : ℝ) ^ ls.card := by
    rcases Nat.eq_zero_or_pos ls.card with h0 | hpos
    · rw [h0, pow_zero]; exact one_pos
    · obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
      exact pow_pos (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨d l⟩)) _
  unfold uMean
  rw [div_eq_div_iff hS.ne' hW.ne']
  apply mul_right_cancel₀ hVm.ne'
  calc (∑ s, g (f s)) * (Fintype.card (L → V) : ℝ) * (Fintype.card V : ℝ) ^ ls.card
      = ((∑ s, g (f s)) * (Fintype.card V : ℝ) ^ ls.card) * Fintype.card (L → V) := by ring
    _ = (Fintype.card S * ∑ v : ls → V, g (ext v)) * Fintype.card (L → V) := by rw [h1]
    _ = Fintype.card S * ((Fintype.card (L → V) : ℝ) * ∑ v : ls → V, g (ext v)) := by ring
    _ = Fintype.card S * ((∑ w : L → V, g w) * (Fintype.card V : ℝ) ^ ls.card) := by rw [h2]
    _ = (∑ w : L → V, g w) * Fintype.card S * (Fintype.card V : ℝ) ^ ls.card := by ring

end NearCubicWires.WireExponent3_5.Filters
