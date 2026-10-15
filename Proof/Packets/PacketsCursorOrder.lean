import Proof.Packets.PacketsLayout
import Proof.Packets.PacketsLexSucc

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsGlue
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.PacketsGlue.LexSucc
noncomputable section

/-- A digit vector of the eight key fields. -/
abbrev Digits := Fin 8 → ℕ

/-! ## Coordinate levels (a `finiteProduct`, coordinate 0 outermost) -/

/-- Levels for coordinates `0..n-1` placed at fields `k..k+n-1`, each with a constant bound. -/
def coordLevels (k n : ℕ) (h : k + n ≤ 8) (bnd : Fin n → ℕ) : List (Level (Fin 8)) :=
  List.ofFn (fun i : Fin n => (⟨⟨k + i.val, by omega⟩, fun _ => bnd i⟩ : Level (Fin 8)))

/-- Write the coordinates `t` into fields `k..k+n-1`. -/
def place : (k n : ℕ) → k + n ≤ 8 → (Fin n → ℕ) → Digits → Digits
  | _, 0, _, _, d => d
  | k, n+1, h, t, d =>
      place (k+1) n (by omega) (fun i => t i.succ) (Function.update d ⟨k, by omega⟩ (t 0))

theorem coordLevels_succ (k n : ℕ) (h : k + (n+1) ≤ 8) (bnd : Fin (n+1) → ℕ) :
    coordLevels k (n+1) h bnd =
      (⟨⟨k, by omega⟩, fun _ => bnd 0⟩ : Level (Fin 8)) ::
        coordLevels (k+1) n (by omega) (fun i => bnd i.succ) := by
  unfold coordLevels
  rw [List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext i
  have hv : k + (i.succ : Fin (n+1)).val = k + 1 + i.val := by simp only [Fin.val_succ]; omega
  simp only [hv]

theorem place_apply : ∀ (n k : ℕ) (h : k + n ≤ 8) (t : Fin n → ℕ) (d : Digits) (x : Fin 8),
    place k n h t d x = if h' : k ≤ x.val ∧ x.val < k + n then t ⟨x.val - k, by omega⟩ else d x
  | 0, k, h, t, d, x => by
    simp only [place]
    rw [dif_neg (by omega)]
  | n+1, k, h, t, d, x => by
    simp only [place]
    rw [place_apply n (k+1)]
    by_cases hx1 : k + 1 ≤ x.val ∧ x.val < k + 1 + n
    · rw [dif_pos hx1, dif_pos (by omega)]
      congr 1
      ext
      simp only [Fin.val_succ]
      omega
    · rw [dif_neg hx1]
      by_cases hxk : x.val = k
      · rw [dif_pos (by omega)]
        subst hxk
        simp only [Fin.eta, Function.update_self]
        congr 1
        ext
        simp
      · rw [dif_neg (by omega)]
        have hne : x ≠ ⟨k, by omega⟩ := fun h' => hxk (congrArg Fin.val h')
        rw [Function.update_of_ne hne]

/-- A `range` enumeration is a `finRange` enumeration of the values. -/
theorem range_flatMap {β : Type} (m : ℕ) (G : ℕ → List β) :
    (List.range m).flatMap G = (List.finRange m).flatMap (fun w => G w.val) := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]

theorem enum_coord : ∀ (n k : ℕ) (h : k + n ≤ 8) (bnd : Fin n → ℕ) (rest : List (Level (Fin 8)))
    (d : Digits),
    enum (coordLevels k n h bnd ++ rest) d =
      (Packets.finiteProduct n bnd).flatMap (fun t => enum rest (place k n h (fun i => (t i).val) d))
  | 0, k, h, bnd, rest, d => by
    simp [coordLevels, place, Packets.finiteProduct]
  | n+1, k, h, bnd, rest, d => by
    rw [coordLevels_succ, List.cons_append]
    simp only [enum]
    simp only [enum_coord n (k+1)]
    rw [range_flatMap]
    simp only [Packets.finiteProduct, List.flatMap_assoc, List.flatMap_map]
    rfl

/-! ## The cursor specs -/

/-- The prime VALUE at a prime index (`1` off range, never read at a valid code). -/
def primeAt (cutoff u : ℕ) : ℕ :=
  if h : u < Fintype.card (PrimeIndex cutoff) then ((primeIndexFinEquiv cutoff).symm ⟨u, h⟩).val else 1

theorem primeAt_pos (cutoff u : ℕ) : 0 < primeAt cutoff u := by
  unfold primeAt
  split_ifs with h
  · exact (mem_primesUpTo.mp ((primeIndexFinEquiv cutoff).symm ⟨u, h⟩).property).1.pos
  · omega

/-- The digit levels of a request, outermost first. -/
def cursorSpec (a : DecompositionAlgorithm) : Request → List (Level (Fin 8))
  | .terminal => [⟨7, fun _ => 0⟩]
  | .sym r four L target =>
      ⟨5, fun _ => (Packets.seedList (symmetricFourfoldOccurrences r)
        (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target)).length⟩ ::
      coordLevels 0 r.circuits.length (by omega) (fun i => (r.circuits.get i).bottomCount + 1)
  | .thr r four L target =>
      coordLevels 0 r.circuits.length (by omega)
        (fun i => (ThresholdRows.children a (r.circuits.get i)).length) ++
      [⟨4, fun _ => Fintype.card (PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target))⟩,
       ⟨5, fun _ => (Packets.seedList (thresholdFourfoldOccurrences r)
          (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
          (CloseoutFinalC10ThresholdRows.listDenominator a r target)).length⟩,
       ⟨6, fun d => primeAt (CloseoutFinalC10ThresholdRows.primeCutoff a r target) (d 4)⟩]

/-- **The pure successor**: the carry cascade over the request's digit levels; the done code
(`keyDigits a r none`: field 7 = 1, all others 0) past the last key. -/
def succDigits (a : DecompositionAlgorithm) (r : Request) (d : Digits) : Digits :=
  succD (cursorSpec a r) (keyDigits a r none) d

/-! ## The key list is the enumeration -/

/-- An `ofFn` enumeration through an equivalence is a `range` enumeration of indices. -/
theorem ofFn_flatMap {α β : Type} {m : ℕ} (e : α ≃ Fin m) (F : α → List β) (G : ℕ → List β)
    (hFG : ∀ w : Fin m, F (e.symm w) = G w.val) :
    (List.ofFn e.symm).flatMap F = (List.range (List.ofFn e.symm).length).flatMap G := by
  rw [List.length_ofFn, range_flatMap, List.ofFn_eq_map, List.flatMap_map]
  congr 1
  funext w
  exact hFG w

/-- The same, with the range written as the equivalence's cardinality. -/
theorem ofFn_flatMap' {α β : Type} {m : ℕ} (e : α ≃ Fin m) (F : α → List β) (G : ℕ → List β)
    (hFG : ∀ w : Fin m, F (e.symm w) = G w.val) :
    (List.ofFn e.symm).flatMap F = (List.range m).flatMap G := by
  rw [ofFn_flatMap e F G hFG, List.length_ofFn]

theorem flatMap_congr_fun {α β : Type} {F G : α → List β} (l : List α) (h : ∀ x, F x = G x) :
    l.flatMap F = l.flatMap G := by
  rw [funext h]

theorem map_eq_flatMap_singleton {α β : Type} (l : List α) (f : α → β) :
    l.map f = l.flatMap (fun x => [f x]) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- The SYM key digits, stated on the key type itself (`keyDigits_sym` is `rfl`). -/
def symDigitsOf (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : ℕ)
    (k : RCFive.RowKeys.SymKey r L target) : Digits := fun i =>
  if h : i.val < r.circuits.length then k.offset ⟨i.val, h⟩
  else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val else 0

/-- The THR key digits, stated on the key type itself (`keyDigits_thr` is `rfl`). -/
def thrDigitsOf (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) : Digits := fun i =>
  if h : i.val < r.circuits.length then (k.selection ⟨i.val, h⟩).val
  else if i.val = 4 then (primeIndexFinEquiv _ k.prime).val
  else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val
  else if i.val = 6 then k.residue.val else 0

theorem sym_digits (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    (RCFive.RowKeys.symKeys r L target).map (fun k => keyDigits a (.sym r four L target) (some k)) =
      enum (cursorSpec a (.sym r four L target)) (fun _ => 0) := by
  change (RCFive.RowKeys.symKeys r L target).map (symDigitsOf r L target) = _
  simp only [cursorSpec, enum]
  rw [RCFive.RowKeys.symKeys, List.map_flatMap]
  refine ofFn_flatMap _ _ _ ?_
  intro w
  have hc := enum_coord r.circuits.length 0 (by omega) (fun i => (r.circuits.get i).bottomCount + 1) []
    (Function.update (fun _ => 0) 5 w.val)
  rw [List.append_nil] at hc
  rw [hc]
  simp only [Packets.symOffsetList, List.map_map, enum]
  rw [map_eq_flatMap_singleton]
  congr 1
  funext t
  congr 1
  funext x
  simp only [Function.comp_apply, symDigitsOf]
  rw [place_apply]
  by_cases hx : x.val < r.circuits.length
  · rw [dif_pos hx, dif_pos (by omega)]
    simp
  · rw [dif_neg hx, dif_neg (by omega), Function.update_apply]
    by_cases h5 : x.val = 5
    · rw [if_pos h5, if_pos (Fin.ext h5), Equiv.apply_symm_apply]
    · rw [if_neg h5, if_neg (fun h' => h5 (congrArg Fin.val h'))]

theorem thr_keyDigits_map (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ) :
    (rcKeys a (.thr r four L target)).map (fun k => keyDigits a (.thr r four L target) (some k)) =
      (RCFive.RowKeys.thrKeys a r L target).map (thrDigitsOf a r L target) := by
  have h3 : (rcKeys a (.thr r four L target)).map (fun k => keyDigits a (.thr r four L target) (some k)) =
      (RCFive.RowKeys.thrKeys a r L target).map
        (fun k : RCFive.RowKeys.ThrKey a r L target => keyDigits a (.thr r four L target) (some k)) := rfl
  rw [h3]
  congr 1

theorem thr_digits (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    (RCFive.RowKeys.thrKeys a r L target).map (thrDigitsOf a r L target) =
      enum (cursorSpec a (.thr r four L target)) (fun _ => 0) := by
  simp only [cursorSpec]
  rw [enum_coord, RCFive.RowKeys.thrKeys, List.map_flatMap]
  simp only [Packets.thrSelectionList]
  refine flatMap_congr_fun _ (fun t => ?_)
  simp only [enum, List.map_flatMap]
  refine ofFn_flatMap' _ _ _ ?_
  intro u
  refine ofFn_flatMap _ _ _ ?_
  intro v
  have hu : Function.update (Function.update (place 0 r.circuits.length (by omega)
      (fun i => (t i).val) (fun _ => 0)) 4 u.val) 5 v.val 4 = u.val := by
    rw [Function.update_of_ne (by decide), Function.update_self]
  rw [hu]
  have hp : primeAt (CloseoutFinalC10ThresholdRows.primeCutoff a r target) u.val =
      ((primeIndexFinEquiv (CloseoutFinalC10ThresholdRows.primeCutoff a r target)).symm u).val := by
    unfold primeAt
    rw [dif_pos u.isLt]
  rw [hp, range_flatMap, List.map_map, map_eq_flatMap_singleton]
  refine flatMap_congr_fun _ (fun w => ?_)
  congr 1
  funext x
  simp only [Function.comp_apply, thrDigitsOf]
  simp only [Function.update_apply]
  rw [place_apply]
  by_cases hx : x.val < r.circuits.length
  · rw [dif_pos hx, dif_pos (by omega)]
    have h6 : x ≠ 6 := fun h' => by rw [h'] at hx; simp at hx; omega
    have h5 : x ≠ 5 := fun h' => by rw [h'] at hx; simp at hx; omega
    have h4 : x ≠ 4 := fun h' => by rw [h'] at hx; simp at hx; omega
    rw [if_neg h6, if_neg h5, if_neg h4]
    simp
  · rw [dif_neg hx, dif_neg (by omega)]
    by_cases h4 : x.val = 4
    · have h4' : x = 4 := Fin.ext h4
      subst h4'
      simp
    · by_cases h5 : x.val = 5
      · have h5' : x = 5 := Fin.ext h5
        subst h5'
        simp
      · by_cases h6 : x.val = 6
        · have h6' : x = 6 := Fin.ext h6
          subst h6'
          simp
        · rw [if_neg (fun h' => h6 (congrArg Fin.val h')), if_neg (fun h' => h5 (congrArg Fin.val h')),
            if_neg (fun h' => h4 (congrArg Fin.val h')), if_neg h4, if_neg h5, if_neg h6]

theorem digits_eq (a : DecompositionAlgorithm) (r : Request) :
    (rcKeys a r).map (fun k => keyDigits a r (some k)) = enum (cursorSpec a r) (fun _ => 0) := by
  cases r with
  | terminal => rfl
  | sym r four L target => exact sym_digits a r four L target
  | thr r four L target =>
    rw [thr_keyDigits_map]
    exact thr_digits a r four L target

/-! ## The order theorem -/

theorem mem_fields_coord {k n : ℕ} {h : k + n ≤ 8} {bnd : Fin n → ℕ} {f : Fin 8}
    (hf : f ∈ fields (coordLevels k n h bnd)) : k ≤ f.val ∧ f.val < k + n := by
  simp only [fields, coordLevels, List.map_ofFn, List.mem_ofFn] at hf
  obtain ⟨i, hi⟩ := hf
  rw [← hi]
  simp only [Function.comp_apply]
  omega

theorem mem_coord_bound {k n : ℕ} {h : k + n ≤ 8} {bnd : Fin n → ℕ} {l : Level (Fin 8)}
    (hl : l ∈ coordLevels k n h bnd) (d : Digits) : ∃ i, l.bound d = bnd i := by
  simp only [coordLevels, List.mem_ofFn] at hl
  obtain ⟨i, hi⟩ := hl
  exact ⟨i, by rw [← hi]⟩

theorem wf_coord : ∀ (n k : ℕ) (h : k + n ≤ 8) (bnd : Fin n → ℕ) (rest : List (Level (Fin 8))),
    WF rest → (∀ f ∈ fields rest, f.val < k ∨ k + n ≤ f.val) → WF (coordLevels k n h bnd ++ rest)
  | 0, k, h, bnd, rest, hw, _ => by
    simpa [coordLevels] using hw
  | n+1, k, h, bnd, rest, hw, hd => by
    rw [coordLevels_succ, List.cons_append]
    refine ⟨?_, fun _ _ _ => rfl, wf_coord n (k+1) (by omega) _ rest hw (fun f hf => ?_)⟩
    · intro hk
      simp only [fields, List.map_append, List.mem_append] at hk
      rcases hk with hk | hk
      · have := mem_fields_coord hk
        simp only at this
        omega
      · have := hd _ hk
        simp only at this
        omega
    · have := hd f hf
      omega

theorem cursorSpec_wf (a : DecompositionAlgorithm) (r : Request) : WF (cursorSpec a r) := by
  cases r with
  | terminal => exact ⟨by simp [fields], fun _ _ _ => rfl, trivial⟩
  | sym r four L target =>
    refine ⟨fun h5 => ?_, fun _ _ _ => rfl, ?_⟩
    · have := mem_fields_coord h5
      simp only at this
      omega
    · have hw := wf_coord r.circuits.length 0 (by omega) (fun i => (r.circuits.get i).bottomCount + 1) []
        trivial (by simp [fields])
      rw [List.append_nil] at hw
      exact hw
  | thr r four L target =>
    refine wf_coord r.circuits.length 0 (by omega) _ _ ?_ ?_
    · refine ⟨by simp [fields], fun _ _ _ => rfl, by simp [fields], fun _ _ _ => rfl, by simp [fields], ?_,
        trivial⟩
      intro d e hde
      have h4 : d 4 = e 4 := hde 4 (by simp [fields])
      simp only [h4]
    · intro f hf
      simp only [fields, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;> simp <;> omega

theorem cursorSpec_pos (a : DecompositionAlgorithm) (r : Request) (h : rcKeys a r ≠ []) :
    Pos (cursorSpec a r) := by
  obtain ⟨k, _⟩ := List.exists_mem_of_ne_nil _ h
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r four L target =>
    have hS : 0 < (Packets.seedList (symmetricFourfoldOccurrences r)
        (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target)).length := by
      simp only [Packets.seedList, List.length_ofFn]
      exact Fin.pos (canonicalWalkSampleFinEquiv _ _ (k : RCFive.RowKeys.SymKey r L target).seed)
    intro l hl d
    simp only [cursorSpec, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hS
    · obtain ⟨i, hi⟩ := mem_coord_bound hl d
      rw [hi]
      omega
  | thr r four L target =>
    have kk : RCFive.RowKeys.ThrKey a r L target := k
    have hS : 0 < (Packets.seedList (thresholdFourfoldOccurrences r)
        (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
        (CloseoutFinalC10ThresholdRows.listDenominator a r target)).length := by
      simp only [Packets.seedList, List.length_ofFn]
      exact Fin.pos (canonicalWalkSampleFinEquiv _ _ kk.seed)
    have hP : 0 < Fintype.card (PrimeIndex (CloseoutFinalC10ThresholdRows.primeCutoff a r target)) :=
      Fin.pos (primeIndexFinEquiv _ kk.prime)
    intro l hl d
    simp only [cursorSpec, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with hl | rfl | rfl | rfl
    · obtain ⟨i, hi⟩ := mem_coord_bound hl d
      rw [hi]
      exact Fin.pos (kk.selection i)
    · exact hP
    · exact hS
    · exact primeAt_pos _ _

/-- The digits of `keys[j]?` (with `done` for `none`) are the enumeration entry, or the done code. -/
theorem keyDigits_getElem? (a : DecompositionAlgorithm) (r : Request) (j : ℕ) :
    keyDigits a r (rcKeys a r)[j]? =
      ((enum (cursorSpec a r) (fun _ => 0))[j]?).getD (keyDigits a r none) := by
  rw [← digits_eq, List.getElem?_map]
  cases (rcKeys a r)[j]? <;> rfl

/-- **The cursor's order theorem (pure).** The carry cascade `succDigits` maps the digits of
`keys[j]` to the digits of `keys[j+1]?` — the done code after the last key. -/
theorem succ_spec (a : DecompositionAlgorithm) (r : Request) (j : ℕ) (hj : j < (rcKeys a r).length) :
    succDigits a r (keyDigits a r (rcKeys a r)[j]?) = keyDigits a r (rcKeys a r)[j+1]? := by
  have hne : rcKeys a r ≠ [] := by
    intro h
    rw [h] at hj
    simp at hj
  have hlen : (enum (cursorSpec a r) (fun _ => 0)).length = (rcKeys a r).length := by
    rw [← digits_eq, List.length_map]
  rw [keyDigits_getElem?, keyDigits_getElem?, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact succD_spec _ (cursorSpec_wf a r) (cursorSpec_pos a r hne) _ _ j (by omega)

end
end NearCubicWires.PacketsGlue

