import Proof.Gates.Expand.PolyTabLay

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand
open NearCubicWires.RepairRepresentation (natWord)

def intN (z : ℤ) : List ℕ := [if z < 0 then 1 else 0, z.natAbs]
def gateN {n : ℕ} (g : NormalizedThresholdGate n) : List ℕ :=
  n :: ((List.ofFn g.weight).flatMap intN ++ intN g.threshold)
def roleN {G : ℕ} (ρ : Role G) : List ℕ := [ρ.gate.val, if ρ.reference then 1 else 0]

def innerL (r : TabReq) : List ℕ := List.ofFn fun j : Fin r.k => (r.layout.symm (.inl j)).val
def outerL (r : TabReq) : List ℕ := List.ofFn fun t : Fin r.s => (r.layout.symm (.inr t)).val
def bitsL (r : TabReq) : List ℕ := List.ofFn fun c : Fin (2 ^ r.k) => if innerPoint r.k c ∈ r.H then 1 else 0

/-- The naturals of the request word before the formula. -/
def preN (r : TabReq) : List ℕ :=
  [r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k] ++ innerL r ++ [r.s] ++ outerL r ++
    [2 ^ r.k] ++ bitsL r ++ [r.V] ++ (List.ofFn r.role).flatMap roleN

theorem intWord_eq (z : ℤ) : Interfaces.intWord z = (intN z).flatMap natWord := by simp [Interfaces.intWord, intN]

theorem intWord_fun : Interfaces.intWord = fun z => (intN z).flatMap natWord := funext intWord_eq

theorem flatMap_len_const {α β : Type} (l : List α) (f : α → List β) (c : ℕ) (h : ∀ a ∈ l, (f a).length = c) :
    (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]; ring

theorem gateWord_eq {n : ℕ} (g : NormalizedThresholdGate n) : Interfaces.gateWord g = (gateN g).flatMap natWord := by
  simp only [Interfaces.gateWord, Interfaces.listWord, gateN, List.flatMap_cons, List.flatMap_append, List.length_ofFn,
    List.append_assoc, intWord_fun]
  rw [List.flatMap_assoc]

theorem listWord_nat (xs : List ℕ) : Interfaces.listWord natWord xs = (xs.length :: xs).flatMap natWord := by
  simp [Interfaces.listWord]

theorem tabWord_eq (r : TabReq) : tabWord r = (preN r).flatMap natWord ++ formulaWord ⟨r.V, r.F⟩ := by
  unfold tabWord preN
  simp only [Interfaces.listWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_ofFn, List.append_assoc, innerL, outerL, bitsL]
  have hg : (List.ofFn r.gates).flatMap Interfaces.gateWord = ((List.ofFn r.gates).flatMap gateN).flatMap natWord := by
    rw [List.flatMap_assoc]; congr 1; funext g; exact gateWord_eq g
  have hb : (List.ofFn fun c : Fin (2 ^ r.k) => decide (innerPoint r.k c ∈ r.H)).flatMap Interfaces.bitWord =
      (List.ofFn fun c : Fin (2 ^ r.k) => if innerPoint r.k c ∈ r.H then 1 else 0).flatMap natWord := by
    rw [List.ofFn_eq_map, List.ofFn_eq_map, List.flatMap_map, List.flatMap_map]
    congr 1; funext c; by_cases h : innerPoint r.k c ∈ r.H <;> simp [Interfaces.bitWord, h]
  have hr : (List.ofFn r.role).flatMap (fun ρ : Role r.G => natWord ρ.gate.val ++ Interfaces.bitWord ρ.reference) =
      ((List.ofFn r.role).flatMap roleN).flatMap natWord := by
    rw [List.flatMap_assoc]; congr 1; funext ρ; simp [roleN, Interfaces.bitWord]
  have hi : (List.ofFn fun j : Fin r.k => (r.layout.symm (.inl j)).val).flatMap natWord =
      (List.ofFn fun j : Fin r.k => (r.layout.symm (.inl j)).val).flatMap natWord := rfl
  rw [hg, hb, hr]

/-! ## The terms word -/

def monoN {V : ℕ} (t : Finset (Fin V) × ℤ) : List ℕ :=
  ((t.1.sort (· ≤ ·)).map Fin.val).length :: ((t.1.sort (· ≤ ·)).map Fin.val ++ intN t.2)

def termsN {V : ℕ} (P : Terms V) : List ℕ := P.length :: P.flatMap monoN

theorem monoWord_eq {V : ℕ} (t : Finset (Fin V) × ℤ) : monoWord t = (monoN t).flatMap natWord := by
  simp [monoWord, monoN, Interfaces.listWord, intWord_eq, List.flatMap_append]

theorem termsWord_eq {V : ℕ} (P : Terms V) : termsWord P = (termsN P).flatMap natWord := by
  simp only [termsWord, Interfaces.listWord, termsN, List.flatMap_cons]
  congr 1
  rw [List.flatMap_assoc]; congr 1; funext t; exact monoWord_eq t

/-! ## Positions -/

section Pos
variable (r : TabReq)

def pk : ℕ := 5 + r.G * (2 * r.n + 3)
def ps : ℕ := pk r + r.k + 1
def pN : ℕ := ps r + r.s + 1
def pV : ℕ := pN r + 2 ^ r.k + 1

theorem gateN_length {n : ℕ} (g : NormalizedThresholdGate n) : (gateN g).length = 2 * n + 3 := by
  simp only [gateN, List.length_cons, List.length_append]
  rw [flatMap_len_const _ _ 2 (fun _ _ => by simp [intN])]
  simp [intN]; ring

theorem gates_length : ((List.ofFn r.gates).flatMap gateN).length = r.G * (2 * r.n + 3) := by
  rw [flatMap_len_const _ _ _ (fun g _ => gateN_length g)]; simp

theorem roles_length : ((List.ofFn r.role).flatMap roleN).length = r.V * 2 := by
  rw [flatMap_len_const _ _ 2 (fun _ _ => by simp [roleN])]; simp

theorem preN_length : (preN r).length = pV r + 1 + 2 * r.V := by
  simp only [preN, List.length_append, List.length_cons, List.length_nil, gates_length, roles_length, innerL, outerL,
    bitsL, List.length_ofFn, pV, pN, ps, pk]
  ring

end Pos

theorem getElem?_mid {α : Type} (A B : List α) (x : α) (i : ℕ) (hi : i = A.length) : (A ++ x :: B)[i]? = some x := by
  subst hi; simp

theorem getElem_of_getElem? {α : Type} {L : List α} {i : ℕ} {x : α} (h : L[i]? = some x) (hi : i < L.length) :
    L[i] = x := by
  rw [List.getElem?_eq_getElem hi] at h; exact Option.some.inj h

section Idx
variable (r : TabReq)

theorem preN_hdr : (preN r)[0]? = some r.n ∧ (preN r)[1]? = some r.k ∧ (preN r)[2]? = some r.s ∧
    (preN r)[3]? = some r.B ∧ (preN r)[4]? = some r.G := by
  simp [preN]

theorem preN_pk : (preN r)[pk r]? = some r.k := by
  have e : preN r = ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN) ++ r.k :: (innerL r ++ [r.s] ++
      outerL r ++ [2 ^ r.k] ++ bitsL r ++ [r.V] ++ (List.ofFn r.role).flatMap roleN) := by simp [preN]
  rw [e]; exact getElem?_mid _ _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil, gates_length, innerL, outerL, bitsL, List.length_ofFn, pk, ps, pN, pV]; try ring)

theorem preN_ps : (preN r)[ps r]? = some r.s := by
  have e : preN r = ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k] ++ innerL r) ++
      r.s :: (outerL r ++ [2 ^ r.k] ++ bitsL r ++ [r.V] ++ (List.ofFn r.role).flatMap roleN) := by simp [preN]
  rw [e]; exact getElem?_mid _ _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil, gates_length, innerL, outerL, bitsL, List.length_ofFn, pk, ps, pN, pV]; try ring)

theorem preN_pN : (preN r)[pN r]? = some (2 ^ r.k) := by
  have e : preN r = ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k] ++ innerL r ++ [r.s] ++
      outerL r) ++ (2 ^ r.k) :: (bitsL r ++ [r.V] ++ (List.ofFn r.role).flatMap roleN) := by simp [preN]
  rw [e]; exact getElem?_mid _ _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil, gates_length, innerL, outerL, bitsL, List.length_ofFn, pk, ps, pN, pV]; try ring)

theorem preN_pV : (preN r)[pV r]? = some r.V := by
  have e : preN r = ([r.n, r.k, r.s, r.B, r.G] ++ (List.ofFn r.gates).flatMap gateN ++ [r.k] ++ innerL r ++ [r.s] ++
      outerL r ++ [2 ^ r.k] ++ bitsL r) ++ r.V :: ((List.ofFn r.role).flatMap roleN) := by simp [preN]
  rw [e]; exact getElem?_mid _ _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil, gates_length, innerL, outerL, bitsL, List.length_ofFn, pk, ps, pN, pV]; try ring)

theorem natBitLength_le_word (x : ℕ) : natBitLength x + 1 ≤ (natWord x).length := by
  rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]; omega

theorem flatMap_natWord_ge (L : List ℕ) (x : ℕ) (hx : x ∈ L) : (natWord x).length ≤ (L.flatMap natWord).length := by
  rw [List.length_flatMap]
  exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨x, hx, rfl⟩)

theorem preN_word_le : ((preN r).flatMap natWord).length ≤ (tabWord r).length := by
  rw [tabWord_eq]; simp

theorem preN_nbl (x : ℕ) (hx : x ∈ preN r) : natBitLength x + 1 ≤ (tabWord r).length :=
  (natBitLength_le_word x).trans ((flatMap_natWord_ge _ x hx).trans (preN_word_le r))

end Idx

end NearCubicGates.Close.Expand.PolyTab
