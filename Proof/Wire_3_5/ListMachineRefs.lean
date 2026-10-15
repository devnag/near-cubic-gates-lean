import Proof.Wire_3_5.ListPoly
import Proof.Wire_3_5.Shared.S0

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists MvPolynomial Finset

/-! ## Explicit `𝔽₂` polynomials on coordinate indices -/

/-- An explicit `𝔽₂` polynomial over the coordinates `Z_0, Z_1, …` (S0's `F2Poly ℕ`). -/
abbrev Poly := F2Poly ℕ

def pzero : Poly := []
def pone : Poly := [[]]
def pvar (i : ℕ) : Poly := [[i]]
def padd (p q : Poly) : Poly := p ++ q
def pmul (p q : Poly) : Poly := p.flatMap fun m => q.map fun m' => m ++ m'
/-- `1 + p` over `𝔽₂`. -/
def pnot (p : Poly) : Poly := [] :: p
def pconst (b : Bool) : Poly := if b then pone else pzero
def psum (ps : List Poly) : Poly := ps.flatten

theorem eval_foldl_xor (p : Poly) (ρ : ℕ → Bool) (acc : Bool) :
    p.foldl (fun a m => xor a (m.all ρ)) acc = xor acc (F2Poly.eval p ρ) := by
  unfold F2Poly.eval
  induction p generalizing acc with
  | nil => simp
  | cons m p ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih, ih (m.all ρ)]
    simp

@[simp] theorem eval_nil (ρ : ℕ → Bool) : F2Poly.eval ([] : Poly) ρ = false := rfl

theorem eval_cons (m : List ℕ) (p : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (m :: p) ρ = xor (m.all ρ) (F2Poly.eval p ρ) := by
  show (m :: p).foldl _ false = _
  rw [List.foldl_cons, eval_foldl_xor]
  simp

theorem eval_append (p q : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (p ++ q) ρ = xor (F2Poly.eval p ρ) (F2Poly.eval q ρ) := by
  induction p with
  | nil => simp
  | cons m p ih => rw [List.cons_append, eval_cons, eval_cons, ih, Bool.xor_assoc]

@[simp] theorem eval_padd (p q : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (padd p q) ρ = xor (F2Poly.eval p ρ) (F2Poly.eval q ρ) := eval_append p q ρ

@[simp] theorem eval_pzero (ρ : ℕ → Bool) : F2Poly.eval pzero ρ = false := rfl
@[simp] theorem eval_pone (ρ : ℕ → Bool) : F2Poly.eval pone ρ = true := by simp [pone, eval_cons]
@[simp] theorem eval_pvar (i : ℕ) (ρ : ℕ → Bool) : F2Poly.eval (pvar i) ρ = ρ i := by simp [pvar, eval_cons]
@[simp] theorem eval_pnot (p : Poly) (ρ : ℕ → Bool) : F2Poly.eval (pnot p) ρ = !F2Poly.eval p ρ := by
  simp [pnot, eval_cons]
@[simp] theorem eval_pconst (b : Bool) (ρ : ℕ → Bool) : F2Poly.eval (pconst b) ρ = b := by
  cases b <;> simp [pconst]

theorem eval_map_append (m : List ℕ) (q : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (q.map fun m' => m ++ m') ρ = (m.all ρ && F2Poly.eval q ρ) := by
  induction q with
  | nil => simp
  | cons m' q ih =>
    rw [List.map_cons, eval_cons, eval_cons, ih, List.all_append]
    cases m.all ρ <;> simp

@[simp] theorem eval_pmul (p q : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (pmul p q) ρ = (F2Poly.eval p ρ && F2Poly.eval q ρ) := by
  unfold pmul
  induction p with
  | nil => simp
  | cons m p ih =>
    rw [List.flatMap_cons, eval_append, eval_map_append, ih, eval_cons]
    cases m.all ρ <;> cases F2Poly.eval p ρ <;> cases F2Poly.eval q ρ <;> rfl

theorem eval_psum (ps : List Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (psum ps) ρ = ps.foldr (fun p b => xor (F2Poly.eval p ρ) b) false := by
  unfold psum
  induction ps with
  | nil => simp
  | cons p ps ih => rw [List.flatten_cons, eval_append, ih, List.foldr_cons]

/-- A monomial as a product of coordinates `Z_0, …, Z_{L−1}` (coordinates `≥ L` are `0`). -/
noncomputable def interpMono (L : ℕ) (m : List ℕ) : MvPolynomial (Fin L) (ZMod 2) :=
  (m.map fun i => if h : i < L then X ⟨i, h⟩ else 0).prod

/-- The polynomial a monomial list denotes. -/
noncomputable def interp (L : ℕ) (p : Poly) : MvPolynomial (Fin L) (ZMod 2) := (p.map (interpMono L)).sum

/-- The coordinate assignment of an input `z : Fin L → Bool`. -/
def ext {L : ℕ} (z : Fin L → Bool) (i : ℕ) : Bool := if h : i < L then z ⟨i, h⟩ else false

theorem bitF2_and (a b : Bool) : bitF2 (a && b) = bitF2 a * bitF2 b := by cases a <;> cases b <;> rfl
theorem bitF2_xor (a b : Bool) : bitF2 (xor a b) = bitF2 a + bitF2 b := by cases a <;> cases b <;> rfl
theorem bitF2_not (a : Bool) : bitF2 (!a) = 1 + bitF2 a := by cases a <;> rfl

theorem eval_interpMono {L : ℕ} (z : Fin L → Bool) (m : List ℕ) :
    eval (fun i => bitF2 (z i)) (interpMono L m) = bitF2 (m.all (ext z)) := by
  unfold interpMono
  induction m with
  | nil => simp [bitF2]
  | cons i m ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih, List.all_cons, bitF2_and]
    congr 1
    unfold ext
    split_ifs <;> simp [bitF2]

/-- **Evaluation of the denotation is evaluation of the list.** -/
theorem eval_interp {L : ℕ} (z : Fin L → Bool) (p : Poly) :
    eval (fun i => bitF2 (z i)) (interp L p) = bitF2 (F2Poly.eval p (ext z)) := by
  unfold interp
  induction p with
  | nil => rfl
  | cons m p ih => rw [List.map_cons, List.sum_cons, map_add, ih, eval_interpMono, eval_cons, bitF2_xor]

theorem interp_padd (L : ℕ) (p q : Poly) : interp L (padd p q) = interp L p + interp L q := by
  simp [interp, padd]

theorem interp_mono_append (L : ℕ) (m m' : List ℕ) : interpMono L (m ++ m') = interpMono L m * interpMono L m' := by
  simp [interpMono]

theorem interp_pmul (L : ℕ) (p q : Poly) : interp L (pmul p q) = interp L p * interp L q := by
  unfold interp pmul
  induction p with
  | nil => simp
  | cons m p ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons, add_mul]
    congr 1
    rw [List.map_map, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro m' _
    exact interp_mono_append L m m'

@[simp] theorem interp_pzero (L : ℕ) : interp L pzero = 0 := rfl
@[simp] theorem interp_pone (L : ℕ) : interp L pone = 1 := by simp [interp, pone, interpMono]
theorem interp_pnot (L : ℕ) (p : Poly) : interp L (pnot p) = 1 + interp L p := by
  simp [interp, pnot, interpMono]
theorem interp_pconst (L : ℕ) (b : Bool) : interp L (pconst b) = C (bitF2 b) := by
  cases b <;> simp [pconst, bitF2]

theorem interp_psum (L : ℕ) (ps : List Poly) : interp L (psum ps) = (ps.map (interp L)).sum := by
  unfold psum
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [List.flatten_cons, List.map_cons, List.sum_cons, ← ih]; simp [interp]

theorem sum_range_list {R : Type} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-! ## The generalized binomial mod 2, computably -/

/-- `binom(a, t) mod 2` for every integer `a` (for `a = −(y+1)`, `binom(a,t) = (−1)^t binom(y+t, t)`). -/
def chooseMod2 : ℤ → ℕ → Bool
  | .ofNat n, t => n.choose t % 2 == 1
  | .negSucc y, t => (y + t).choose t % 2 == 1

theorem bitF2_nat_mod (n : ℕ) : bitF2 (n % 2 == 1) = ((n : ℕ) : ZMod 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h]; rw [← ZMod.natCast_mod, h]; rfl
  · rw [h]; rw [← ZMod.natCast_mod, h]; rfl

theorem bitF2_chooseMod2 (a : ℤ) (t : ℕ) : bitF2 (chooseMod2 a t) = ((Ring.choose a t : ℤ) : ZMod 2) := by
  rcases a with n | y
  · show bitF2 (n.choose t % 2 == 1) = _
    rw [bitF2_nat_mod]
    have : Ring.choose ((n : ℤ)) t = ((Nat.choose n t : ℕ) : ℤ) := Ring.choose_natCast n t
    simp only [Int.ofNat_eq_natCast] at *
    rw [this, Int.cast_natCast]
  · show bitF2 ((y + t).choose t % 2 == 1) = _
    rw [bitF2_nat_mod]
    have hc : ((y : ℤ) + 1 + ((t : ℕ) : ℤ) - 1) = (((y + t : ℕ)) : ℤ) := by push_cast; ring
    rw [show Int.negSucc y = -((y : ℤ) + 1) from rfl, Ring.choose_neg, hc, Ring.choose_natCast]
    rcases Int.units_eq_one_or (Int.negOnePow ((t : ℕ) : ℤ)) with hh | hh
    · rw [hh, one_smul]; push_cast; rfl
    · rw [hh, Units.neg_smul, one_smul]; push_cast; exact (ZMod.neg_eq_self_mod_two _).symm

/-! ## The decoder bits, decoders, recurrence and repair -/

/-- `binom(S + a, t) mod 2` in the literals `ls` by Pascal's rule (mirrors `Lists.binomPoly`). -/
def binomRef : List Poly → ℤ → ℕ → Poly
  | [], a, t => pconst (chooseMod2 a t)
  | _ :: _, _, 0 => pone
  | ℓ :: ls, a, t + 1 => padd (binomRef ls a (t + 1)) (pmul ℓ (binomRef ls a t))

theorem interp_binomRef (L : ℕ) (ls : List Poly) (a : ℤ) (t : ℕ) :
    interp L (binomRef ls a t) = binomPoly (ls.map (interp L)) a t := by
  induction ls generalizing t with
  | nil => rw [binomRef, interp_pconst, bitF2_chooseMod2]; rfl
  | cons ℓ ls ih =>
    cases t with
    | zero => simp [binomRef, binomPoly]
    | succ t => rw [binomRef, interp_padd, interp_pmul, ih, ih, List.map_cons, binomPoly]

namespace Ref
variable (D : ListData)

/-- The literal of coordinate `i` at level `j` (mirrors `ListData.levelLit`). -/
def litRef (j i : ℕ) : Poly :=
  if D.inLevel (j + 1) i then pnot (pvar i) else if D.inLevel j i then pvar i else pzero

/-- The literals of level `j` over the coordinates `i < L`. -/
def litsRef (j L : ℕ) : List Poly := (List.range L).map (litRef D j)

theorem interp_litRef (j : ℕ) {L : ℕ} (i : Fin L) : interp L (litRef D j i) = D.levelLit j i := by
  unfold litRef ListData.levelLit
  have hv : interp L (pvar i) = X i := by simp [interp, pvar, interpMono, i.isLt]
  split_ifs
  · rw [interp_pnot, hv, CharTwo.sub_eq_add]
  · exact hv
  · rfl

theorem finRange_map_val (L : ℕ) : (List.finRange L).map Fin.val = List.range L := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem interp_litsRef (j L : ℕ) : (litsRef D j L).map (interp L) = D.levelLits j L := by
  unfold litsRef ListData.levelLits
  rw [← finRange_map_val, List.map_map, List.map_map]
  apply List.map_congr_left
  intro i _
  exact interp_litRef D j i

def bitRef (L j h : ℕ) : Poly := binomRef (litsRef D j L) (D.levelOffset j L) (2 ^ h)

theorem interp_bitRef (L j : ℕ) (h : Fin (D.ell j)) : interp L (bitRef D L j h) = D.polyBit j L h := by
  unfold bitRef ListData.polyBit
  rw [interp_binomRef, interp_litsRef]

def factorRef (L j : ℕ) (d : ℤ) (h : ℕ) : Poly :=
  if (d + D.W j).toNat.testBit h then bitRef D L j h else pnot (bitRef D L j h)

/-- **The binary residue decoder** `A_{j,d} = ∏_{h<ℓ_j}(G_{j,h}+1−d_h)` on `[−W_j, −W_j+H_j−1]`, `0` off it. -/
def decoderRef (L j : ℕ) (d : ℤ) : Poly :=
  if 0 ≤ d + D.W j ∧ d + D.W j < 2 ^ D.ell j then
    (List.range (D.ell j)).foldr (fun h acc => pmul (factorRef D L j d h) acc) pone
  else pzero

theorem interp_foldr_pmul (L : ℕ) (l : List ℕ) (f : ℕ → Poly) :
    interp L (l.foldr (fun h acc => pmul (f h) acc) pone) = (l.map fun h => interp L (f h)).prod := by
  induction l with
  | nil => simp
  | cons h l ih => rw [List.foldr_cons, interp_pmul, ih, List.map_cons, List.prod_cons]

theorem prod_range_list {R : Type} [CommMonoid R] (n : ℕ) (f : ℕ → R) :
    ((List.range n).map f).prod = ∏ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

theorem interp_decoderRef (L j : ℕ) (d : ℤ) : interp L (decoderRef D L j d) = D.polyDecoder j L d := by
  unfold decoderRef ListData.polyDecoder
  split_ifs
  · rw [interp_foldr_pmul, prod_range_list, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun h _ => ?_
    unfold factorRef
    rw [← interp_bitRef D L j h]
    split_ifs with hb
    · simp [hb, bitF2]
    · rw [interp_pnot]; simp [hb, bitF2, add_comm]
  · rfl

def recurRef (M : ℕ) : List (ℤ → Poly) → ℕ → Poly
  | [] => fun s => if s = 0 then pone else pzero
  | A :: rest => fun s => psum ((List.range (M + 1)).map fun t => pmul (recurRef M rest t) (A ((s : ℤ) - 2 * t)))

theorem interp_recurRef (L M : ℕ) (As : List (ℤ → Poly)) (s : ℕ) :
    interp L (recurRef M As s) = polyRecAll M (As.map fun A d => interp L (A d)) s := by
  induction As generalizing s with
  | nil => simp only [recurRef, polyRecAll, List.map_nil]; split_ifs <;> simp
  | cons A rest ih =>
    simp only [recurRef, polyRecAll, List.map_cons]
    rw [interp_psum, List.map_map, ← sum_range_list]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp, interp_pmul, ih]

def repairRef (M : ℕ) (P : ℕ → Poly) (s : ℕ) : Poly :=
  if s = 0 then pnot (psum ((List.range M).map fun i => P (i + 1))) else P s

theorem interp_repairRef (L M : ℕ) (P : ℕ → Poly) (s : ℕ) :
    interp L (repairRef M P s) = polyRepair M (fun s => interp L (P s)) s := by
  unfold repairRef polyRepair
  split_ifs
  · rw [interp_pnot, interp_psum, List.map_map, sum_range_list]
    congr 1
    have h := Finset.sum_range_succ' (fun s => interp L (P s)) M
    have h' := Finset.add_sum_erase (range (M + 1)) (fun s => interp L (P s)) (Finset.mem_range.mpr (Nat.succ_pos M))
    simp only [Function.comp] at *
    rw [← add_left_cancel_iff (a := interp L (P 0)), h', h, add_comm]
  · rfl

/-- **The repaired states** `P_0, …, P_M` of `list:repair` as explicit monomial lists in `Z_0, …, Z_{L−1}`. -/
def stateRef (L s : ℕ) : Poly :=
  repairRef D.M (recurRef D.M ((List.range D.J).map fun j d => decoderRef D L j d)) s

theorem interp_stateRef (L s : ℕ) : interp L (stateRef D L s) = D.polyStates L s := by
  unfold stateRef ListData.polyStates
  rw [interp_repairRef]
  congr 1
  funext s'
  rw [interp_recurRef, List.map_map]
  congr 2
  funext j
  funext d
  exact interp_decoderRef D L j d

theorem stateRef_eval (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true) (L s : ℕ)
    (z : Fin L → Bool) : bitF2 (F2Poly.eval (stateRef D L s) (ext z)) = D.listStates (List.ofFn z) s := by
  rw [← eval_interp, interp_stateRef]
  exact (D.listStates_poly hnest L s).2 z

/-! ## Size: the printed monomials have the paper's degree and only the population's coordinates -/

/-- Every printed monomial has at most `e` factors. -/
def DegLe (p : Poly) (e : ℕ) : Prop := ∀ m ∈ p, m.length ≤ e

/-- Every printed monomial uses only the coordinates `Z_0, …, Z_{L−1}`. -/
def AtomsLt (p : Poly) (L : ℕ) : Prop := ∀ m ∈ p, ∀ i ∈ m, i < L

theorem DegLe.mono {p : Poly} {e e' : ℕ} (h : DegLe p e) (he : e ≤ e') : DegLe p e' :=
  fun m hm => (h m hm).trans he

theorem degLe_padd {p q : Poly} {e : ℕ} (hp : DegLe p e) (hq : DegLe q e) : DegLe (padd p q) e := by
  intro m hm
  rcases List.mem_append.mp hm with h | h
  · exact hp m h
  · exact hq m h

theorem mem_pmul {p q : Poly} {m : List ℕ} (hm : m ∈ pmul p q) : ∃ a ∈ p, ∃ b ∈ q, m = a ++ b := by
  unfold pmul at hm
  obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
  exact ⟨a, ha, b, hb, rfl⟩

theorem degLe_pmul {p q : Poly} {e f : ℕ} (hp : DegLe p e) (hq : DegLe q f) : DegLe (pmul p q) (e + f) := by
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_pmul hm
  rw [List.length_append]
  exact Nat.add_le_add (hp a ha) (hq b hb)

theorem degLe_pone (e : ℕ) : DegLe pone e := by intro m hm; simp [pone] at hm; subst hm; simp
theorem degLe_pzero (e : ℕ) : DegLe pzero e := by intro m hm; simp [pzero] at hm
theorem degLe_pvar (i : ℕ) : DegLe (pvar i) 1 := by intro m hm; simp [pvar] at hm; subst hm; simp
theorem degLe_pnot {p : Poly} {e : ℕ} (hp : DegLe p e) : DegLe (pnot p) e := by
  intro m hm
  rcases List.mem_cons.mp hm with h | h
  · subst h; simp
  · exact hp m h
theorem degLe_pconst (b : Bool) (e : ℕ) : DegLe (pconst b) e := by
  cases b
  · exact degLe_pzero e
  · exact degLe_pone e
theorem degLe_psum {ps : List Poly} {e : ℕ} (h : ∀ p ∈ ps, DegLe p e) : DegLe (psum ps) e := by
  intro m hm
  obtain ⟨p, hp, hm⟩ := List.mem_flatten.mp hm
  exact h p hp m hm

theorem atomsLt_padd {p q : Poly} {L : ℕ} (hp : AtomsLt p L) (hq : AtomsLt q L) : AtomsLt (padd p q) L := by
  intro m hm
  rcases List.mem_append.mp hm with h | h
  · exact hp m h
  · exact hq m h
theorem atomsLt_pmul {p q : Poly} {L : ℕ} (hp : AtomsLt p L) (hq : AtomsLt q L) : AtomsLt (pmul p q) L := by
  intro m hm i hi
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_pmul hm
  rcases List.mem_append.mp hi with h | h
  · exact hp a ha i h
  · exact hq b hb i h
theorem atomsLt_pone (L : ℕ) : AtomsLt pone L := by intro m hm; simp [pone] at hm; subst hm; simp
theorem atomsLt_pzero (L : ℕ) : AtomsLt pzero L := by intro m hm; simp [pzero] at hm
theorem atomsLt_pnot {p : Poly} {L : ℕ} (hp : AtomsLt p L) : AtomsLt (pnot p) L := by
  intro m hm
  rcases List.mem_cons.mp hm with h | h
  · subst h; simp
  · exact hp m h
theorem atomsLt_pconst (b : Bool) (L : ℕ) : AtomsLt (pconst b) L := by
  cases b
  · exact atomsLt_pzero L
  · exact atomsLt_pone L
theorem atomsLt_psum {ps : List Poly} {L : ℕ} (h : ∀ p ∈ ps, AtomsLt p L) : AtomsLt (psum ps) L := by
  intro m hm
  obtain ⟨p, hp, hm⟩ := List.mem_flatten.mp hm
  exact h p hp m hm

theorem binomRef_size (ls : List Poly) (L : ℕ) (hd : ∀ ℓ ∈ ls, DegLe ℓ 1) (ha : ∀ ℓ ∈ ls, AtomsLt ℓ L)
    (a : ℤ) (t : ℕ) : DegLe (binomRef ls a t) t ∧ AtomsLt (binomRef ls a t) L := by
  induction ls generalizing t with
  | nil => exact ⟨degLe_pconst _ _, atomsLt_pconst _ _⟩
  | cons ℓ ls ih =>
    have hd' : ∀ ℓ' ∈ ls, DegLe ℓ' 1 := fun ℓ' h => hd ℓ' (List.mem_cons_of_mem _ h)
    have ha' : ∀ ℓ' ∈ ls, AtomsLt ℓ' L := fun ℓ' h => ha ℓ' (List.mem_cons_of_mem _ h)
    cases t with
    | zero => exact ⟨degLe_pone 0, atomsLt_pone L⟩
    | succ t =>
      refine ⟨degLe_padd (ih hd' ha' (t + 1)).1 ?_, atomsLt_padd (ih hd' ha' (t + 1)).2
        (atomsLt_pmul (ha ℓ (List.mem_cons_self ..)) (ih hd' ha' t).2)⟩
      have := degLe_pmul (hd ℓ (List.mem_cons_self ..)) (ih hd' ha' t).1
      exact this.mono (by omega)

theorem litsRef_size (j L : ℕ) : (∀ ℓ ∈ litsRef D j L, DegLe ℓ 1) ∧ ∀ ℓ ∈ litsRef D j L, AtomsLt ℓ L := by
  constructor <;> intro ℓ hℓ <;> obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hℓ <;> unfold litRef <;> split_ifs
  · exact degLe_pnot (degLe_pvar i)
  · exact degLe_pvar i
  · exact degLe_pzero 1
  · refine atomsLt_pnot ?_
    intro m hm k hk; simp [pvar] at hm; subst hm; simp at hk; subst hk; exact List.mem_range.mp hi
  · intro m hm k hk; simp [pvar] at hm; subst hm; simp at hk; subst hk; exact List.mem_range.mp hi
  · exact atomsLt_pzero L

theorem bitRef_size (L j h : ℕ) : DegLe (bitRef D L j h) (2 ^ h) ∧ AtomsLt (bitRef D L j h) L :=
  binomRef_size _ L (litsRef_size D j L).1 (litsRef_size D j L).2 _ _

theorem sum_two_pow_range (ℓ : ℕ) : ∑ h ∈ range ℓ, 2 ^ h + 1 = 2 ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem decoderRef_size (L j : ℕ) (d : ℤ) :
    DegLe (decoderRef D L j d) (2 ^ D.ell j - 1) ∧ AtomsLt (decoderRef D L j d) L := by
  unfold decoderRef
  split_ifs
  · have key : ∀ n, n ≤ D.ell j →
        DegLe ((List.range n).foldr (fun h acc => pmul (factorRef D L j d h) acc) pone) (∑ h ∈ range n, 2 ^ h) ∧
        AtomsLt ((List.range n).foldr (fun h acc => pmul (factorRef D L j d h) acc) pone) L := by
      intro n _
      induction n with
      | zero => exact ⟨degLe_pone _, atomsLt_pone L⟩
      | succ n ih =>
        have ih := ih (by omega)
        rw [List.range_succ, List.foldr_append, Finset.sum_range_succ]
        simp only [List.foldr_cons, List.foldr_nil]
        have hf : DegLe (factorRef D L j d n) (2 ^ n) ∧ AtomsLt (factorRef D L j d n) L := by
          unfold factorRef
          split_ifs
          · exact bitRef_size D L j n
          · exact ⟨degLe_pnot (bitRef_size D L j n).1, atomsLt_pnot (bitRef_size D L j n).2⟩
        -- the fold over `range n ++ [n]` multiplies the factor of `n` onto the fold of `range n`
        have hgen : ∀ (l : List ℕ) (acc : Poly) (e : ℕ), DegLe acc e → AtomsLt acc L →
            (∀ h ∈ l, DegLe (factorRef D L j d h) (2 ^ h) ∧ AtomsLt (factorRef D L j d h) L) →
            DegLe (l.foldr (fun h acc => pmul (factorRef D L j d h) acc) acc) ((l.map (2 ^ ·)).sum + e) ∧
            AtomsLt (l.foldr (fun h acc => pmul (factorRef D L j d h) acc) acc) L := by
          intro l
          induction l with
          | nil => intro acc e hd ha _; simpa using ⟨hd, ha⟩
          | cons h l ihl =>
            intro acc e hd ha hl
            obtain ⟨hd', ha'⟩ := ihl acc e hd ha fun h' hh => hl h' (List.mem_cons_of_mem _ hh)
            simp only [List.foldr_cons, List.map_cons, List.sum_cons]
            refine ⟨(degLe_pmul (hl h (List.mem_cons_self ..)).1 hd').mono (by omega),
              atomsLt_pmul (hl h (List.mem_cons_self ..)).2 ha'⟩
        have := hgen (List.range n) (pmul (factorRef D L j d n) pone) (2 ^ n)
          ((degLe_pmul hf.1 (degLe_pone 0)).mono (by omega)) (atomsLt_pmul hf.2 (atomsLt_pone L))
          (fun h hh => by
            unfold factorRef
            split_ifs
            · exact bitRef_size D L j h
            · exact ⟨degLe_pnot (bitRef_size D L j h).1, atomsLt_pnot (bitRef_size D L j h).2⟩)
        rw [sum_range_list (f := fun h => 2 ^ h)] at this
        exact this
    obtain ⟨h1, h2⟩ := key (D.ell j) le_rfl
    refine ⟨h1.mono ?_, h2⟩
    have := sum_two_pow_range (D.ell j)
    omega
  · exact ⟨degLe_pzero _, atomsLt_pzero L⟩

theorem recurRef_size (L M : ℕ) (As : List ((ℤ → Poly) × ℕ))
    (hAs : ∀ p ∈ As, ∀ d, DegLe (p.1 d) p.2 ∧ AtomsLt (p.1 d) L) (s : ℕ) :
    DegLe (recurRef M (As.map Prod.fst) s) (As.map Prod.snd).sum ∧ AtomsLt (recurRef M (As.map Prod.fst) s) L := by
  induction As generalizing s with
  | nil =>
    simp only [List.map_nil, recurRef, List.sum_nil]
    split_ifs
    · exact ⟨degLe_pone 0, atomsLt_pone L⟩
    · exact ⟨degLe_pzero 0, atomsLt_pzero L⟩
  | cons p rest ih =>
    simp only [List.map_cons, recurRef, List.sum_cons]
    have ih' := fun t => ih (fun q hq => hAs q (List.mem_cons_of_mem _ hq)) t
    refine ⟨degLe_psum ?_, atomsLt_psum ?_⟩ <;> intro q hq <;> obtain ⟨t, _, rfl⟩ := List.mem_map.mp hq
    · have h2 := (hAs p (List.mem_cons_self ..) ((s : ℤ) - 2 * t)).1
      exact (degLe_pmul (ih' t).1 h2).mono (by omega)
    · exact atomsLt_pmul (ih' t).2 (hAs p (List.mem_cons_self ..) ((s : ℤ) - 2 * t)).2

theorem repairRef_size (L M e : ℕ) (P : ℕ → Poly) (hP : ∀ s, DegLe (P s) e ∧ AtomsLt (P s) L) (s : ℕ) :
    DegLe (repairRef M P s) e ∧ AtomsLt (repairRef M P s) L := by
  unfold repairRef
  split_ifs
  · refine ⟨degLe_pnot (degLe_psum ?_), atomsLt_pnot (atomsLt_psum ?_)⟩ <;> intro q hq <;>
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
    · exact (hP (i + 1)).1
    · exact (hP (i + 1)).2
  · exact hP s

theorem stateRef_size (L s : ℕ) :
    DegLe (stateRef D L s) (∑ j ∈ range D.J, (2 ^ D.ell j - 1)) ∧ AtomsLt (stateRef D L s) L := by
  unfold stateRef
  apply repairRef_size
  intro s'
  have := recurRef_size L D.M ((List.range D.J).map fun j => ((fun d => decoderRef D L j d), 2 ^ D.ell j - 1))
    (by
      intro p hp d
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
      exact decoderRef_size D L j d) s'
  rw [List.map_map, List.map_map] at this
  rw [← sum_range_list]
  exact this

end Ref

end NearCubicWires.WireExponent3_5.ListMachine
