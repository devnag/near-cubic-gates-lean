import Proof.Gates.CounterMachine.ReqMom
import Proof.Gates.CounterMachine.ReqLayout
import Proof.Gates.CounterMachine.PrefixSpec

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)

section Word
variable {n : ℕ}

theorem coordsOf_length (I : Finset (Fin n)) : (coordsOf I).length = I.card := by simp [coordsOf]

theorem outerCoords_length (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) : (outerCoords I).length = n - k := by
  unfold outerCoords; rw [← compl_eq_filter]; simp [card_compl_eq I hk]

theorem ofFn_inl (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) :
    List.ofFn (fun j : Fin k => ((layoutOf I hk).symm (.inl j)).val) = coordsOf I := by
  apply List.ext_getElem
  · simp [coordsOf_length, hk]
  · intro i h1 h2
    rw [List.getElem_ofFn, layoutOf_symm_inl, List.getD_eq_getElem _ _ h2]

theorem ofFn_inr (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) :
    List.ofFn (fun t : Fin (n - k) => ((layoutOf I hk).symm (.inr t)).val) = (outerCoords I).map Fin.val := by
  apply List.ext_getElem
  · simp [outerCoords_length I hk]
  · intro i h1 h2
    rw [List.getElem_ofFn, layoutOf_symm_inr, List.getD_eq_getElem _ _ h2]

theorem coordsOf_idxOf (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) (i : I) :
    (coordsOf I).idxOf i.1.val = ((I.orderIsoOfFin hk).symm i).val := by
  set j := (I.orderIsoOfFin hk).symm i with hj
  have hi : I.orderEmbOfFin hk j = i.1 := by
    have := (I.orderIsoOfFin hk).apply_symm_apply i
    rw [← hj] at this
    simpa [Finset.coe_orderIsoOfFin_apply] using congrArg Subtype.val this
  have hlen : j.val < (coordsOf I).length := by rw [coordsOf_length, hk]; exact j.isLt
  have hget : (coordsOf I)[j.val] = i.1.val := by
    rw [Finset.orderEmbOfFin_apply] at hi
    have := congrArg Fin.val hi
    simpa [coordsOf] using this
  have hnd : (coordsOf I).Nodup := by
    unfold coordsOf
    exact (Finset.sort_nodup _ _).map Fin.val_injective
  rw [← hget]
  exact List.Nodup.idxOf_getElem hnd _ hlen

theorem pointsOf_innerPoint (I : Finset (Fin n)) {k : ℕ} (hk : I.card = k) (c : Fin (2 ^ k)) :
    pointsOf I hk (innerPoint k c) = innerPt I c.val := by
  funext i
  simp only [pointsOf, innerPoint, innerPt]
  rw [coordsOf_idxOf I hk i]

end Word

section Req
variable (c : Call) (p : Params) (wt : Wit c.n)

theorem ofFn_range {α : Type} {m : ℕ} (f : ℕ → α) : List.ofFn (fun i : Fin m => f i.val) = (List.range m).map f := by
  apply List.ext_getElem <;> simp

theorem resHbits_eq (hk : wt.I.card = p.k) (part : Option Bool) :
    List.ofFn (fun x : Fin (2 ^ p.k) => decide (innerPoint p.k x ∈ partH c p wt hk part)) = resHbits c p wt part := by
  unfold resHbits
  rw [← ofFn_range]
  congr 1; funext x
  simp [partH, pointsOf_innerPoint wt.I hk x]

/-- **The residue request word** is the part's prefix and the formula. -/
theorem resReq_tabWord (hk : wt.I.card = p.k) (part : Option Bool) (q : ℕ) (κ σ : List ℕ)
    (hB : ∀ i : Fin (resGates c).length, GateBits (Call.B0 c.n) ((resGates c)[i]))
    (hc : PrintCondition p.k (c.n - p.k) (resFormula c p wt q κ σ).degree (resGates c).length
      (Tabulator.mT (c.n - p.k) (Call.B0 c.n + Nat.clog 2 (c.n + 1)))) :
    tabWord (resReq c p wt hk part q κ σ hB hc) = resPrefix c p wt part ++
      natWord (toks (resFormula c p wt q κ σ)).length ++ (toks (resFormula c p wt q κ σ)).flatMap tokWord := by
  have e0 : tabWord (resReq c p wt hk part q κ σ hB hc) = natWord c.n ++ natWord p.k ++ natWord (c.n - p.k) ++
      natWord (Call.B0 c.n) ++ listWord gateWord (List.ofFn fun i : Fin (resGates c).length => (resGates c)[i]) ++
      listWord natWord (List.ofFn fun j : Fin p.k => ((layoutOf wt.I hk).symm (.inl j)).val) ++
      listWord natWord (List.ofFn fun t : Fin (c.n - p.k) => ((layoutOf wt.I hk).symm (.inr t)).val) ++
      listWord bitWord (List.ofFn fun x : Fin (2 ^ p.k) => decide (innerPoint p.k x ∈ partH c p wt hk part)) ++
      listWord (fun ρ : Role (resGates c).length => natWord ρ.gate.val ++ bitWord ρ.reference)
        (List.ofFn fun v : Fin (resGates c).length => (⟨v, false⟩ : Role (resGates c).length)) ++
      formulaWord ⟨(resGates c).length, resFormula c p wt q κ σ⟩ := rfl
  rw [e0]
  unfold resPrefix prefixWord formulaWord
  rw [ofFn_inl wt.I hk, ofFn_inr wt.I hk, resHbits_eq c p wt hk part,
    show List.ofFn (fun i : Fin (resGates c).length => (resGates c)[i]) = resGates c from List.ofFn_getElem]
  have hro : listWord (fun ρ : Role (resGates c).length => natWord ρ.gate.val ++ bitWord ρ.reference)
      (List.ofFn fun v : Fin (resGates c).length => (⟨v, false⟩ : Role (resGates c).length)) =
      listWord (fun ρ : ℕ × Bool => natWord ρ.1 ++ bitWord ρ.2)
        ((List.range (resGates c).length).map fun v => (v, false)) := by
    unfold listWord
    simp only [List.length_ofFn, List.length_map, List.length_range]
    congr 1
    rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map, List.flatMap_map, List.flatMap_map]
    rfl
  rw [hro]
  simp [listWord, List.append_assoc]

theorem momRoles_eq (m : ℕ) :
    (List.ofFn (momRole m)).map (fun ρ => (ρ.gate.val, ρ.reference)) =
      (List.range m).map (fun v => (v, false)) ++ (List.range m).map (fun v => (v, true)) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_ofFn, momRole]
    by_cases hi : i < m
    · rw [List.getElem_append_left (by simpa using hi)]
      simp [Nat.mod_eq_of_lt hi, hi]
    · have hl : ((List.range m).map (fun v => (v, false))).length ≤ i := by simp; omega
      rw [List.getElem_append_right hl]
      simp at h1
      have hm : i % m = i - m := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      simp [hm, show m ≤ i by omega]

/-- **The moment request word** is the role's prefix and the formula. -/
theorem momReq_tabWord (hk : wt.I.card = p.k) (r : ℕ) (j : Option ℕ)
    (hB : ∀ t : Fin (circ c r).gates.length, GateBits (Call.B0 c.n) ((circ c r).gates[t]))
    (hc : PrintCondition p.k (c.n - p.k) (momF (V := 2 * (circ c r).gates.length) c p wt r j).degree
      (2 * (circ c r).gates.length) (Tabulator.mT (c.n - p.k) (Call.B0 c.n + Nat.clog 2 (c.n + 1)))) :
    tabWord (momReq c p wt hk r j hB hc) = momPrefix c p wt r ++
      natWord (toks (momF (V := 2 * (circ c r).gates.length) c p wt r j)).length ++
      (toks (momF (V := 2 * (circ c r).gates.length) c p wt r j)).flatMap tokWord := by
  have e0 : tabWord (momReq c p wt hk r j hB hc) = natWord c.n ++ natWord p.k ++ natWord (c.n - p.k) ++
      natWord (Call.B0 c.n) ++
      listWord gateWord (List.ofFn fun t : Fin (circ c r).gates.length => (circ c r).gates[t]) ++
      listWord natWord (List.ofFn fun j : Fin p.k => ((layoutOf wt.I hk).symm (.inl j)).val) ++
      listWord natWord (List.ofFn fun t : Fin (c.n - p.k) => ((layoutOf wt.I hk).symm (.inr t)).val) ++
      listWord bitWord (List.ofFn fun x : Fin (2 ^ p.k) => decide (innerPoint p.k x ∈ (Finset.univ :
        Finset (Fin p.k → Bool)))) ++
      listWord (fun ρ : Role (circ c r).gates.length => natWord ρ.gate.val ++ bitWord ρ.reference)
        (List.ofFn (momRole (circ c r).gates.length)) ++
      formulaWord ⟨2 * (circ c r).gates.length, momF (V := 2 * (circ c r).gates.length) c p wt r j⟩ := rfl
  rw [e0]
  unfold momPrefix prefixWord formulaWord
  rw [ofFn_inl wt.I hk, ofFn_inr wt.I hk,
    show List.ofFn (fun t : Fin (circ c r).gates.length => (circ c r).gates[t]) = (circ c r).gates from
      List.ofFn_getElem]
  have hh : List.ofFn (fun x : Fin (2 ^ p.k) => decide (innerPoint p.k x ∈ (Finset.univ :
      Finset (Fin p.k → Bool)))) = List.replicate (2 ^ p.k) true := by
    apply List.ext_getElem <;> simp
  have hro : listWord (fun ρ : Role (circ c r).gates.length => natWord ρ.gate.val ++ bitWord ρ.reference)
      (List.ofFn (momRole (circ c r).gates.length)) =
      listWord (fun ρ : ℕ × Bool => natWord ρ.1 ++ bitWord ρ.2)
        (((List.range (circ c r).gates.length).map fun v => (v, false)) ++
          ((List.range (circ c r).gates.length).map fun v => (v, true))) := by
    rw [← momRoles_eq]
    unfold listWord
    simp only [List.length_ofFn, List.length_map, List.flatMap_map]
  rw [hh, hro]
  simp [listWord, List.append_assoc]

end Req

end NearCubicGates.Close.CounterMachine
