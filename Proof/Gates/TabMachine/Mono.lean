import Proof.Gates.TabMachine.Occ3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open NearCubicGates.Close.Tabulator
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-! ## Value level -/

/-- The tuples (flattened) after the occurrences `os`, processed in list order. -/
def tupF (c : ℕ) (os : List Occ) : List (List ℤ) := os.foldl (fun tf o => newT (o.kids c) tf) [[]]

theorem tupF_append (c : ℕ) (os : List Occ) (o : Occ) : tupF c (os ++ [o]) = newT (o.kids c) (tupF c os) := by
  unfold tupF; rw [List.foldl_append]; rfl

theorem tupF_eq (c : ℕ) (os : List Occ) : tupF c os = (tuples (os.reverse.map fun o => o.kids c)).map List.flatten := by
  induction os using List.reverseRecOn with
  | nil => rfl
  | append_singleton os o ih =>
    rw [tupF_append, ih, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons,
      tuples_flatten]

theorem kids_length (o : Occ) (c : ℕ) : ∀ kid ∈ o.kids c, kid.length = o.outW.length + 1 :=
  compileL_length _ _

theorem tupF_mem_length (c s : ℕ) (os : List Occ) (hs : ∀ o ∈ os, o.outW.length = s) :
    ∀ t ∈ tupF c os, t.length = os.length * (s + 1) := by
  induction os using List.reverseRecOn with
  | nil => intro t ht; simp [tupF] at ht; subst ht; simp
  | append_singleton os o ih =>
    intro t ht
    rw [tupF_append] at ht
    have h1 := newT_mem_length (s + 1) (os.length * (s + 1)) (o.kids c) (tupF c os)
      (fun kid hk => by rw [kids_length o c kid hk, hs o (by simp)])
      (ih (fun o' ho' => hs o' (by simp [ho']))) t ht
    rw [h1, List.length_append, List.length_singleton]; ring

theorem tupF_length (c : ℕ) (os : List Occ) (o : Occ) :
    (tupF c (os ++ [o])).length = (o.kids c).length * (tupF c os).length := by
  rw [tupF_append, newT_length]

theorem mem_map_emb {α : Type} {k : ℕ} (Z : Fin k ↪ α) (l : List (Fin k)) (i : Fin k) : Z i ∈ l.map Z ↔ i ∈ l := by
  rw [List.mem_map]
  exact ⟨fun ⟨j, hj, e⟩ => Z.injective e ▸ hj, fun h => ⟨i, h, rfl⟩⟩

/-! ## One occurrence -/

/-- The side conditions of one occurrence step at the inner point `c`, with current tuples `tf` of `M` fields: the
block at `p` is the occurrence, the values fit the widths, `cap` is large enough. -/
structure StepOK (cap W s k : ℕ) (xs : List ℕ) (p c : ℕ) (o : Occ) (tf : List (List ℤ)) (M : ℕ) : Prop where
  blk : (xs.drop p).take (occLen o) = occRecs o
  hk : o.inW.length = k
  hs : o.outW.length = s
  hc : c < 2 ^ (W + 1)
  bound : (o.inW.map Int.natAbs).sum + o.thr.natAbs + 1 < 2 ^ W
  hB : 4 * totalL o.outW + 2 * s + 4 ≤ 2 ^ W
  ht : (rTarget o c).natAbs + totalL o.outW < 2 ^ W
  fit : ∀ kid ∈ o.kids c, ∀ y ∈ kid, y.natAbs < 2 ^ W
  cap1 : (xs.length + 1) * (2 * (W + 1) + 1) + 2 * xs.length + 2 * k + 2 * s ≤ cap
  capK : (compRecs W o.outW (rTarget o c)).length + (s + 1) * (2 * (W + 1) + 1) + 2 * s + 4 * W + 8 ≤ cap
  capE : (o.kids c).length * (2 * ((s + 1) * (W + 1)) + 1) + 2 * ((s + 1) * (W + 1)) + 2 + 2 * (s + 1) ≤ cap
  capEO : (o.kids c).length * (s + 1) * (2 * ((s + 1) * (W + 1)) + 1) + 1 ≤ cap
  capT : TCap cap ((s + 1) * (W + 1)) (s + 1) M (o.kids c).length tf.length []
  capC : (o.kids c).length * tf.length * (s + 1 + M) * (2 * ((s + 1) * (W + 1)) + 1) + 2 * ((s + 1) * (W + 1)) + 2 ≤ cap
  capR : (o.kids c).length * tf.length + 2 * (o.kids c).length + tf.length + M + s + 1 ≤ cap

section OccStep
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

def occStep : WMX ns nr := .seq (occA Z Y) (occB Z Y)

def occStepCost (W s k : ℕ) (xs : List ℕ) (p c : ℕ) (o : Occ) (T M : ℕ) : ℕ :=
  occACost W xs.length s k p (compRecs W o.outW (rTarget o c)).length + 1 + occBCost W s (o.kids c).length T M

/-- The streams one occurrence step may change. -/
def stepIdx : List (Fin 64) := occAIdx ++ occBIdx

theorem occStep_spec (cap W s k M : ℕ) (hs1 : 1 ≤ s) (σ : WState ns nr) (xs : List ℕ) (junk : List Bool)
    (p c : ℕ) (o : Occ) (tf : List (List ℤ)) (hrest : GRest Z Y cap W s k σ)
    (hpg : σ.st (Z 46) = recStream (xs.map (binary (W + 1))) ++ junk) (hpgh : σ.sh (Z 46) = 0)
    (hIDX : σ.val (Y 77) = p) (hCX : NumOn σ (Z 54) (W + 1) c)
    (htf : ∃ junk, σ.st (Z 31) = recStream ((fieldNums tf).map (binary ((s + 1) * (W + 1)))) ++ junk)
    (htfl : ∀ t ∈ tf, t.length = M) (hM : σ.val (Y 44) = M) (hNT : σ.val (Y 47) = tf.length)
    (hok : StepOK cap W s k xs p c o tf M) :
    Runs cap (occStep Z Y) σ (occStepCost W s k xs p c o tf.length M) (fun τ =>
      GRest Z Y cap W s k τ ∧
      (∃ junk', τ.st (Z 31) = recStream ((fieldNums (newT (o.kids c) tf)).map (binary ((s + 1) * (W + 1)))) ++ junk') ∧
      τ.val (Y 77) = p + occLen o ∧ τ.val (Y 44) = M + (s + 1) ∧ τ.val (Y 47) = (o.kids c).length * tf.length ∧
      SameExcept σ τ (stepIdx.map Z) [Y 77, Y 44, Y 47]) := by
  refine Runs.seq (occA_spec Z Y cap W s k σ xs junk p c o hrest hpg hpgh hok.blk hok.hk hok.hs hIDX hCX hok.hc
    hok.bound hok.hB hok.ht hok.cap1 hok.capK) fun τ1 h1 => ?_
  obtain ⟨g1, ⟨jk, hk1⟩, hk1h, h77, f1⟩ := h1
  have n31 : Z 31 ∉ occAStreams Z := by unfold occAStreams; rw [mem_map_emb]; decide
  have v1 : ∀ r : Fin 112, r ≠ 77 → τ1.val (Y r) = σ.val (Y r) := fun r hr =>
    f1.val (by simp only [List.mem_singleton]; exact Y.injective.ne hr)
  have hB := occB_spec Z Y cap W s k M hs1 τ1 (o.kids c) tf jk g1 hk1 hk1h
    (fun kid hk => by rw [kids_length o c kid hk, hok.hs]) hok.fit (by rw [f1.st n31]; exact htf) htfl
    (by rw [v1 44 (by decide)]; exact hM) (by rw [v1 47 (by decide)]; exact hNT) hok.capE hok.capEO hok.capT
    hok.capC hok.capR
  refine hB.post fun τ2 h2 => ?_
  obtain ⟨g2, ht2, h44, h47, f2⟩ := h2
  refine ⟨g2, ht2, ?_, h44, h47, ?_⟩
  · have hn : Y 77 ∉ [Y 44, Y 47] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨Y.injective.ne (by decide), Y.injective.ne (by decide)⟩
    rw [f2.val hn]
    exact h77
  · have hall := f1.comp' f2
    refine hall.weaken ?_ ?_
    · intro x hx
      unfold stepIdx; rw [List.map_append]
      simp only [List.mem_append] at hx ⊢
      unfold occAStreams occBStreams at hx
      exact hx
    · intro r hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      tauto

end OccStep

section OccLoop
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

/-- Position of occurrence `i` of a monomial whose occurrences are stored from `p0`. -/
def posOf (p0 : ℕ) (os : List Occ) (i : ℕ) : ℕ := p0 + ((os.take i).map occLen).sum

theorem posOf_succ (p0 : ℕ) (os : List Occ) (i : ℕ) (hi : i < os.length) :
    posOf p0 os (i + 1) = posOf p0 os i + occLen os[i] := by
  unfold posOf
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.map_append, List.sum_append]
  simp; ring

theorem grest_setv {cap W s k : ℕ} {σ : WState ns nr} (h : GRest Z Y cap W s k σ) (r : Fin 112) (hr : r ∉ zList)
    (hr2 : r ∉ [(13 : Fin 112), 32, 41, 66, 84, 89]) (v : ℕ) : GRest Z Y cap W s k (σ.setv (Y r) v) :=
  grest_frame Z Y h (sameExcept_setv σ (S := []) (Rg := [Y r]) (by simp) v) (fun _ _ hm => by simp at hm)
    (fun _ _ hm => by simp at hm) (fun _ _ => by simp) (fun _ _ hm => by simp at hm) (fun _ _ hm => by simp at hm)
    (fun _ _ hm => by simp at hm)
    (fun q hq hm => by
      simp only [List.mem_singleton, emb_eq_iff] at hm; subst hm; exact absurd hq hr)
    (fun q hq hm => by
      simp only [List.mem_singleton, emb_eq_iff] at hm; subst hm; exact absurd hq hr2)

/-- The loop over a monomial's `|os|` occurrences (count in `Y 98`, scratch `Y 99`). -/
def occLoop : WMX ns nr := repK (Y 98) (Y 99) (occStep Z Y)

/-- The loop invariant after `i` occurrences. -/
def OccInv (cap W s k : ℕ) (σ0 : WState ns nr) (p0 c : ℕ) (os : List Occ) (i : ℕ) (τ : WState ns nr) : Prop :=
  GRest Z Y cap W s k τ ∧
    (∃ junk, τ.st (Z 31) = recStream ((fieldNums (tupF c (os.take i))).map (binary ((s + 1) * (W + 1)))) ++ junk) ∧
    τ.val (Y 77) = posOf p0 os i ∧ τ.val (Y 44) = i * (s + 1) ∧ τ.val (Y 47) = (tupF c (os.take i)).length ∧
    SameExcept σ0 τ (stepIdx.map Z) [Y 77, Y 44, Y 47, Y 98, Y 99]

theorem occLoop_spec (cap W s k CS : ℕ) (hs1 : 1 ≤ s) (σ : WState ns nr) (xs : List ℕ) (junk : List Bool)
    (p0 c : ℕ) (os : List Occ) (hrest : GRest Z Y cap W s k σ)
    (hpg : σ.st (Z 46) = recStream (xs.map (binary (W + 1))) ++ junk) (hpgh : σ.sh (Z 46) = 0)
    (hIDX : σ.val (Y 77) = p0) (hCX : NumOn σ (Z 54) (W + 1) c)
    (htf : ∃ junk, σ.st (Z 31) = recStream (([] : List ℕ).map (binary ((s + 1) * (W + 1)))) ++ junk)
    (hM : σ.val (Y 44) = 0) (hNT : σ.val (Y 47) = 1) (hm : σ.val (Y 98) = os.length) (hm2 : σ.val (Y 99) = 0)
    (hos : ∀ o ∈ os, o.outW.length = s)
    (hok : ∀ i (hi : i < os.length), StepOK cap W s k xs (posOf p0 os i) c os[i] (tupF c (os.take i)) (i * (s + 1)))
    (hcost : ∀ i (hi : i < os.length),
      occStepCost W s k xs (posOf p0 os i) c os[i] (tupF c (os.take i)).length (i * (s + 1)) ≤ CS)
    (hcap : 2 * os.length ≤ cap) :
    Runs cap (occLoop Z Y) σ (os.length * (CS + 8) + 7 * os.length + 3) (fun τ =>
      OccInv Z Y cap W s k σ p0 c os os.length τ ∧ τ.val (Y 98) = os.length ∧ τ.val (Y 99) = 0) := by
  have n98 : Y 98 ≠ Y 99 := Y.injective.ne (by decide)
  have hst : ∀ i : Fin 64, i ∉ stepIdx → ∀ τ : WState ns nr,
      SameExcept σ τ (stepIdx.map Z) [Y 77, Y 44, Y 47, Y 98, Y 99] → τ.st (Z i) = σ.st (Z i) ∧ τ.sh (Z i) = σ.sh (Z i) :=
    fun i hi τ h => h.1 _ (by rw [mem_map_emb]; exact hi)
  refine Runs.rep (cap := cap) (body := occStep Z Y) n98 CS os.length (OccInv Z Y cap W s k σ p0 c os) hcap
    ?_ ?_ ?_ σ ?_ hm hm2
  · rintro i τ v ⟨g, ht, h77, h44, h47, f⟩
    refine ⟨grest_setv Z Y g 98 (by decide) (by decide) v, ht, ?_, ?_, ?_, ?_⟩
    · rw [WState.setv_val, Function.update_of_ne (Y.injective.ne (by decide))]; exact h77
    · rw [WState.setv_val, Function.update_of_ne (Y.injective.ne (by decide))]; exact h44
    · rw [WState.setv_val, Function.update_of_ne (Y.injective.ne (by decide))]; exact h47
    · exact SameExcept.trans (S := stepIdx.map Z) (Rg := [Y 77, Y 44, Y 47, Y 98, Y 99]) f (sameExcept_setv τ (by simp) v)
  · rintro i τ v ⟨g, ht, h77, h44, h47, f⟩
    refine ⟨grest_setv Z Y g 99 (by decide) (by decide) v, ht, ?_, ?_, ?_, ?_⟩
    · rw [WState.setv_val, Function.update_of_ne (Y.injective.ne (by decide))]; exact h77
    · rw [WState.setv_val, Function.update_of_ne (Y.injective.ne (by decide))]; exact h44
    · rw [WState.setv_val, Function.update_of_ne (Y.injective.ne (by decide))]; exact h47
    · exact SameExcept.trans (S := stepIdx.map Z) (Rg := [Y 77, Y 44, Y 47, Y 98, Y 99]) f (sameExcept_setv τ (by simp) v)
  · intro i hi τ ⟨g, ht, h77, h44, h47, f⟩
    have e46 := hst 46 (by decide) τ f
    have e54 := hst 54 (by decide) τ f
    have hstep := occStep_spec Z Y cap W s k (i * (s + 1)) hs1 τ xs junk (posOf p0 os i) c os[i]
      (tupF c (os.take i)) g (by rw [e46.1]; exact hpg) (by rw [e46.2]; exact hpgh) h77
      ⟨by rw [e54.1]; exact hCX.1, by rw [e54.2]; exact hCX.2⟩ ht
      (by
        have := tupF_mem_length c s (os.take i) (fun o ho => hos o (List.mem_of_mem_take ho))
        rwa [List.length_take, min_eq_left hi.le] at this) h44 h47 (hok i hi)
    refine (hstep.cost (hcost i hi)).post fun τ' ⟨g', ht', h77', h44', h47', f'⟩ => ?_
    have htake : os.take (i + 1) = os.take i ++ [os[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
    have n98' : Y 98 ∉ [Y 77, Y 44, Y 47] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨Y.injective.ne (by decide), Y.injective.ne (by decide), Y.injective.ne (by decide)⟩
    have n99' : Y 99 ∉ [Y 77, Y 44, Y 47] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨Y.injective.ne (by decide), Y.injective.ne (by decide), Y.injective.ne (by decide)⟩
    refine ⟨⟨g', ?_, ?_, ?_, ?_, ?_⟩, f'.val n98', f'.val n99'⟩
    · rw [htake, tupF_append]; exact ht'
    · rw [posOf_succ p0 os i hi]; exact h77'
    · rw [h44']; ring
    · rw [htake, tupF_length]; exact h47'
    · exact f.trans (f'.weaken (fun x hx => hx) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto))
  · refine ⟨hrest, ?_, ?_, ?_, ?_, SameExcept.refl _ _ _⟩
    · simpa [tupF, fieldNums] using htf
    · simp [posOf, hIDX]
    · simp [hM]
    · simp [tupF, hNT]

end OccLoop

end NearCubicGates.Close.TabMachine
