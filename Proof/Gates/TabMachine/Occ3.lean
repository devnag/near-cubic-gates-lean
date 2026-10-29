import Proof.Gates.TabMachine.Occ2

/-! # One variable occurrence, part 3: **`occB_spec`** (explode, tuple step, copy-back, counts)

Proof of lem:print: after the compiler has written the occurrence's exact children (`occA_spec`), the children are
split into fields (`explode`), every child is put before every current tuple (`tupleStep`), the new tuples are copied
back onto the tuple stream, and the counts are updated: tuple count `NT := NK · NT`, tuple width `M := M + (s + 1)`,
child count `NK := 0`. -/

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

/-! ## Helpers -/

/-- `closeOut` as a postcondition: the stream holds `out ++ [false]` then junk, head `0`, counter `0`. -/
theorem closeOut_runs (cap : ℕ) {O : Fin (ns + 1)} {CO : Fin nr} (σ : WState ns nr) (out L0 : List Bool)
    (hO : OutOn σ O CO out L0) (hcap : out.length ≤ cap) :
    Runs cap (closeOutX O CO) σ (5 * out.length + 3) (fun τ =>
      (∃ junk, τ.st O = out ++ [false] ++ junk) ∧ τ.sh O = 0 ∧ τ.val CO = 0 ∧ SameExcept σ τ [O] [CO]) := by
  refine Runs.of (WXExec.wm (closeOut_spec cap σ out L0 hO hcap)) ⟨⟨L0.drop (out ++ [false]).length, ?_⟩, ?_, ?_, ?_⟩
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]; rfl
  · simp
  · simp
  · refine ⟨fun x hx => ?_, fun r hr => ?_, by simp⟩
    · have hx' : x ≠ O := by simpa using hx
      simp [Function.update_of_ne hx']
    · have hr' : r ≠ CO := by simpa using hr
      simp [Function.update_of_ne hr']

theorem fr_st (Z : Fin 64 ↪ Fin (ns + 1)) {σ τ : WState ns nr} {l : List (Fin 64)} {R : List (Fin nr)}
    (h : SameExcept σ τ (l.map Z) R) (i : Fin 64) (hi : i ∉ l) : τ.st (Z i) = σ.st (Z i) ∧ τ.sh (Z i) = σ.sh (Z i) :=
  h.1 _ (fun hm => hi (by obtain ⟨j, hj, e⟩ := List.mem_map.mp hm; exact Z.injective e ▸ hj))

theorem fr_val (Y : Fin 112 ↪ Fin nr) {σ τ : WState ns nr} {S : List (Fin (ns + 1))} {l : List (Fin 112)}
    (h : SameExcept σ τ S (l.map Y)) (r : Fin 112) (hr : r ∉ l) : τ.val (Y r) = σ.val (Y r) :=
  h.2.1 _ (fun hm => hr (by obtain ⟨j, hj, e⟩ := List.mem_map.mp hm; exact Y.injective e ▸ hj))

theorem fr_numOn (Z : Fin 64 ↪ Fin (ns + 1)) {σ τ : WState ns nr} {l : List (Fin 64)} {R : List (Fin nr)}
    (h : SameExcept σ τ (l.map Z) R) (i : Fin 64) (hi : i ∉ l) {W v : ℕ} (hn : NumOn σ (Z i) W v) :
    NumOn τ (Z i) W v := ⟨by rw [(fr_st Z h i hi).1]; exact hn.1, by rw [(fr_st Z h i hi).2]; exact hn.2⟩

theorem fieldsRecs_length (L N : ℕ) (l : List (List ℤ)) (h : ∀ c ∈ l, c.length = N) :
    (fieldsRecs L l).length = l.length * N * (2 * L + 1) := by
  unfold fieldsRecs
  rw [fieldRecs_length]
  have := flatten_take_length N l l.length h le_rfl
  rw [List.take_of_length_le le_rfl] at this
  rw [this]

theorem newT_length (kf tf : List (List ℤ)) : (newT kf tf).length = kf.length * tf.length := by
  unfold newT
  induction kf with
  | nil => simp
  | cons a kf ih => simp only [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons]; ring

theorem newT_mem_length (N M : ℕ) (kf tf : List (List ℤ)) (hk : ∀ c ∈ kf, c.length = N)
    (ht : ∀ c ∈ tf, c.length = M) : ∀ u ∈ newT kf tf, u.length = N + M := by
  intro u hu
  unfold newT at hu
  simp only [List.mem_flatMap, List.mem_map] at hu
  obtain ⟨a, ha, t, ht', rfl⟩ := hu
  rw [List.length_append, hk a ha, ht t ht']

theorem recFrames_eq (L : ℕ) (xs : List ℕ) :
    xs.flatMap (fun x => frame (binary L x)) ++ [false] = recStream (xs.map (binary L)) := by
  unfold recStream; rw [List.flatMap_map]

section OccB
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

/-- Explode the children into fields, the tuple step (new tuples on `Z 32`). -/
def occB1 : WMX ns nr :=
  .seq (explode (zE Z) (yG Y))
  (.seq (closeOutX (Z 30) (Y 31))
  (.seq (tupleStep (zP Z) (yQ Y)) (closeOutX (Z 32) (Y 40))))

/-- Copy the new tuples back onto the tuple stream `Z 31`. -/
def occB2 : WMX ns nr :=
  .seq (copyAll (Z 32) (Z 33) (Z 31) (Y 91) (Y 92) (Y 93) (Y 95)) (closeOutX (Z 31) (Y 95))

/-- The counts: `NT := NK · NT`, `NK := 0`, `M := M + (s + 1)`. -/
def occB3 : WMX ns nr :=
  .seq (mulR (Y 34) (Y 96) (Y 47) (Y 97) (Y 91))
  (.seq (.wm (WM.clear (Y 47)))
  (.seq (.wm (WM.move (Y 97) (Y 47)))
  (.seq (.wm (WM.clear (Y 34))) (addR (Y 41) (Y 44) (Y 91)))))

def occB : WMX ns nr := .seq (occB1 Z Y) (.seq (occB2 Z Y) (occB3 Y))

/-- The stream indices `occB` may change. -/
def occBIdx : List (Fin 64) := [24, 25, 27, 28, 29, 30, 31, 32, 33]

def occBStreams : List (Fin (ns + 1)) := occBIdx.map Z

def occB1Cost (W s K T M : ℕ) : ℕ :=
  K * (exBodyCost ((s + 1) * (W + 1)) (s + 1) + (50 * ((s + 1) * (W + 1)) + 30)) + 3 + 1 +
  (5 * (K * (s + 1) * (2 * ((s + 1) * (W + 1)) + 1)) + 3 + 1 +
  (tupleCost ((s + 1) * (W + 1)) (s + 1) M K T + 1 +
  (5 * (K * T * (s + 1 + M) * (2 * ((s + 1) * (W + 1)) + 1)) + 3)))

def occB2Cost (L N : ℕ) : ℕ := N * (40 * L + 11 + (50 * L + 30)) + 3 + 1 + (5 * (N * (2 * L + 1)) + 3)

def occB3Cost (s K T : ℕ) : ℕ :=
  K * (18 * T + 3 + 8) + 7 * K + 3 + 1 + (3 * T + 1 + 1 + (7 * (K * T) + 1 + 1 + (3 * K + 1 + 1 + (18 * (s + 1) + 3))))

/-- `occB`'s cost (`K` children, `T` current tuples of `M` fields, `Lc = (s + 1)(W + 1)`). -/
def occBCost (W s K T M : ℕ) : ℕ :=
  occB1Cost W s K T M + 1 + (occB2Cost ((s + 1) * (W + 1)) (K * T * (s + 1 + M)) + 1 + occB3Cost s K T)

theorem occB1_spec (cap W s k M : ℕ) (hs1 : 1 ≤ s) (σ : WState ns nr) (css tf : List (List ℤ)) (junk : List Bool)
    (hrest : GRest Z Y cap W s k σ)
    (hkd : σ.st (Z 2) = recStream (css.map (recBits W)) ++ junk) (hkdh : σ.sh (Z 2) = 0)
    (hlen : ∀ c ∈ css, c.length = s + 1) (hfit : ∀ c ∈ css, ∀ y ∈ c, y.natAbs < 2 ^ W)
    (htf : ∃ junk, σ.st (Z 31) = recStream ((fieldNums tf).map (binary ((s + 1) * (W + 1)))) ++ junk)
    (htfl : ∀ t ∈ tf, t.length = M) (hM : σ.val (Y 44) = M) (hNT : σ.val (Y 47) = tf.length)
    (hcapE : css.length * (2 * ((s + 1) * (W + 1)) + 1) + 2 * ((s + 1) * (W + 1)) + 2 + 2 * (s + 1) ≤ cap)
    (hcapEO : css.length * (s + 1) * (2 * ((s + 1) * (W + 1)) + 1) + 1 ≤ cap)
    (hcapT : TCap cap ((s + 1) * (W + 1)) (s + 1) M css.length tf.length []) :
    Runs cap (occB1 Z Y) σ (occB1Cost W s css.length tf.length M) (fun τ =>
      (∃ j, τ.st (Z 32) = recStream ((fieldNums (newT css tf)).map (binary ((s + 1) * (W + 1)))) ++ j) ∧
      τ.sh (Z 32) = 0 ∧ τ.sh (Z 30) = 0 ∧ τ.val (Y 34) = css.length ∧
      τ.sh (Z 33) = 0 ∧ (τ.st (Z 33)).length ≤ 2 * ((s + 1) * (W + 1)) + 1 ∧
      τ.sh (Z 24) = 0 ∧ (τ.st (Z 24)).length ≤ 2 * ((s + 1) * (W + 1)) + 1 ∧
      (∀ i ∈ ([25, 27, 28, 29] : List (Fin 64)), ∃ v, NumOn τ (Z i) ((s + 1) * (W + 1)) v) ∧
      SameExcept σ τ (([24, 25, 27, 28, 29, 30, 33, 32] : List (Fin 64)).map Z) (([34] : List (Fin 112)).map Y)) := by
  have hz := hrest.zero
  have hLc1 : 1 ≤ (s + 1) * (W + 1) := by nlinarith
  -- (1) explode
  have hO1 : OutOn σ (zE Z 7) (yG Y 7) [] (σ.st (zE Z 7)) :=
    outOn_start σ _ _ (hrest.closed 30 (by simp)) (hz 31 (by decide))
  have h1 := explode_spec (zE Z) (yG Y) cap W (s + 1) (by omega) σ css junk [] (σ.st (zE Z 7)) 0 hlen hfit
    hkd hkdh (hrest.workc 24 (by simp)).1 (hrest.workc 24 (by simp)).2 (hrest.wc 25 (by decide)) hrest.c26
    hrest.exWords (hz 24 (by decide)) (hz 25 (by decide)) (hz 26 (by decide)) (hz 27 (by decide))
    (hz 28 (by decide)) (hz 29 (by decide)) (hz 30 (by decide)) hO1 hrest.r32 (hz 33 (by decide))
    (hz 34 (by decide)) (by omega) (by simp only [List.length_nil]; omega)
  refine Runs.seq h1 fun τ1 hτ1 => ?_
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hτ1
  replace a2 : τ1.val (Y 34) = 0 + css.length := a2
  replace a5 : τ1.sh (Z 24) = 0 := a5
  replace a6 : (τ1.st (Z 24)).length ≤ 2 * ((s + 1) * (W + 1)) + 1 := a6
  have f1 : SameExcept σ τ1 (([24, 25, 27, 28, 29, 30] : List (Fin 64)).map Z) (([31, 34] : List (Fin 112)).map Y) :=
    a7
  -- (2) close the field stream
  rw [List.nil_append] at a1
  have hfl : (css.flatten.flatMap (fieldRec ((s + 1) * (W + 1)))).length =
      css.length * (s + 1) * (2 * ((s + 1) * (W + 1)) + 1) := fieldsRecs_length _ (s + 1) css hlen
  have h2 := closeOut_runs cap τ1 _ _ a1 (by rw [hfl]; omega)
  rw [hfl] at h2
  refine Runs.seq h2 fun τ2 hτ2 => ?_
  obtain ⟨⟨j2, b1⟩, b2, b3, b4⟩ := hτ2
  replace b1 : τ2.st (Z 30) = _ := b1
  replace b2 : τ2.sh (Z 30) = 0 := b2
  replace b3 : τ2.val (Y 31) = 0 := b3
  have f2 : SameExcept τ1 τ2 (([30] : List (Fin 64)).map Z) (([31] : List (Fin 112)).map Y) := b4
  have f12 := f1.comp' f2
  -- (3) the tuple step
  have hkf2 : ∃ junk, τ2.st (Z 30) = recStream ((fieldNums css).map (binary ((s + 1) * (W + 1)))) ++ junk :=
    ⟨j2, by rw [b1, recStream_fieldNums]; rfl⟩
  have st12 : ∀ i : Fin 64, i ∉ ([24, 25, 27, 28, 29, 30] ++ [30] : List (Fin 64)) →
      τ2.st (Z i) = σ.st (Z i) ∧ τ2.sh (Z i) = σ.sh (Z i) := fun i hi => fr_st Z (by rw [List.map_append]; exact f12) i hi
  have v12 : ∀ r : Fin 112, r ∉ ([31, 34] ++ [31] : List (Fin 112)) → τ2.val (Y r) = σ.val (Y r) :=
    fun r hr => fr_val Y (by rw [List.map_append]; exact f12) r hr
  have hTP : TPre (zP Z) (yQ Y) ((s + 1) * (W + 1)) (s + 1) M css tf τ2 := by
    obtain ⟨jt, hjt⟩ := htf
    refine ⟨hkf2, b2, ⟨jt, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show τ2.st (Z 31) = _; rw [(st12 31 (by decide)).1]; exact hjt
    · show τ2.sh (Z 31) = 0; rw [(st12 31 (by decide)).2]; exact hrest.closed 31 (by simp)
    · show τ2.sh (Z 33) = 0; rw [(st12 33 (by decide)).2]; exact (hrest.workc 33 (by simp)).1
    · show (τ2.st (Z 33)).length ≤ _; rw [(st12 33 (by decide)).1]; exact (hrest.workc 33 (by simp)).2
    · show τ2.val (Y 35) = 0; rw [v12 35 (by decide)]; exact hz 35 (by decide)
    · show τ2.val (Y 36) = 0; rw [v12 36 (by decide)]; exact hz 36 (by decide)
    · show τ2.val (Y 38) = 0; rw [v12 38 (by decide)]; exact hz 38 (by decide)
    · show τ2.val (Y 39) = 0; rw [v12 39 (by decide)]; exact hz 39 (by decide)
    · show τ2.val (Y 42) = 0; rw [v12 42 (by decide)]; exact hz 42 (by decide)
    · show τ2.val (Y 45) = 0; rw [v12 45 (by decide)]; exact hz 45 (by decide)
    · show τ2.val (Y 50) = 0; rw [v12 50 (by decide)]; exact hz 50 (by decide)
    · show τ2.val (Y 41) = s + 1; rw [v12 41 (by decide)]; exact hrest.r41
    · show τ2.val (Y 44) = M; rw [v12 44 (by decide)]; exact hM
  have hO3 : OutOn τ2 (zP Z 2) (yQ Y 5) [] (τ2.st (zP Z 2)) := outOn_start τ2 _ _
    (by show τ2.sh (Z 32) = 0; rw [(st12 32 (by decide)).2]; exact hrest.closed 32 (by simp))
    (by show τ2.val (Y 40) = 0; rw [v12 40 (by decide)]; exact hz 40 (by decide))
  have hNK2 : τ2.val (Y 34) = css.length := by
    rw [fr_val Y f2 34 (by decide), a2, Nat.zero_add]
  have h3 := tupleStep_spec (zP Z) (yQ Y) cap ((s + 1) * (W + 1)) (s + 1) M hLc1 css tf τ2 [] (τ2.st (zP Z 2))
    hlen htfl hTP
    (by show τ2.val (Y 37) = 0; rw [v12 37 (by decide)]; exact hz 37 (by decide))
    (by show τ2.val (Y 43) = 0; rw [v12 43 (by decide)]; exact hz 43 (by decide))
    (by show τ2.val (Y 49) = 0; rw [v12 49 (by decide)]; exact hz 49 (by decide)) hNK2
    (by show τ2.val (Y 46) = 0; rw [v12 46 (by decide)]; exact hz 46 (by decide))
    (by show τ2.val (Y 47) = tf.length; rw [v12 47 (by decide)]; exact hNT)
    (by show τ2.val (Y 48) = 0; rw [v12 48 (by decide)]; exact hz 48 (by decide)) hO3 hcapT
  refine Runs.seq h3 fun τ3 hτ3 => ?_
  obtain ⟨c1, c2, c3⟩ := hτ3
  have f3 : SameExcept τ2 τ3 (([33, 32] : List (Fin 64)).map Z) (([40] : List (Fin 112)).map Y) := c3
  -- (4) close the new tuple stream
  rw [List.nil_append] at c2
  have hnl : (fieldsRecs ((s + 1) * (W + 1)) (newT css tf)).length =
      css.length * tf.length * (s + 1 + M) * (2 * ((s + 1) * (W + 1)) + 1) := by
    rw [fieldsRecs_length _ (s + 1 + M) _ (newT_mem_length (s + 1) M css tf hlen htfl), newT_length]
  obtain ⟨-, -, t3, -⟩ := hcapT
  have t3' : css.length * tf.length * (s + 1 + M) * (2 * ((s + 1) * (W + 1)) + 1) + 1 ≤ cap := by
    have e : css.length * tf.length * ((s + 1 + M) * (2 * ((s + 1) * (W + 1)) + 1)) =
      css.length * tf.length * (s + 1 + M) * (2 * ((s + 1) * (W + 1)) + 1) := by ring
    simp only [List.length_nil, Nat.zero_add] at t3; omega
  have h4 := closeOut_runs cap τ3 _ _ c2 (by rw [hnl]; omega)
  rw [hnl] at h4
  refine h4.post fun τ4 hτ4 => ?_
  obtain ⟨⟨j4, d1⟩, d2, d3, d4⟩ := hτ4
  replace d1 : τ4.st (Z 32) = _ := d1
  replace d2 : τ4.sh (Z 32) = 0 := d2
  replace d3 : τ4.val (Y 40) = 0 := d3
  have f4 : SameExcept τ3 τ4 (([32] : List (Fin 64)).map Z) (([40] : List (Fin 112)).map Y) := d4
  have f34 := f3.comp' f4
  have st4 : ∀ i : Fin 64, i ∉ ([33, 32] ++ [32] : List (Fin 64)) →
      τ4.st (Z i) = τ2.st (Z i) ∧ τ4.sh (Z i) = τ2.sh (Z i) := fun i hi => fr_st Z (by rw [List.map_append]; exact f34) i hi
  have v4 : ∀ r : Fin 112, r ∉ ([40] ++ [40] : List (Fin 112)) → τ4.val (Y r) = τ2.val (Y r) :=
    fun r hr => fr_val Y (by rw [List.map_append]; exact f34) r hr
  have s2 : ∀ i : Fin 64, i ∈ ([24, 25, 27, 28, 29] : List (Fin 64)) →
      τ4.st (Z i) = τ1.st (Z i) ∧ τ4.sh (Z i) = τ1.sh (Z i) := by
    intro i hi
    have n4 : i ∉ ([33, 32] ++ [32] : List (Fin 64)) := by revert i; decide
    have n2 : i ∉ ([30] : List (Fin 64)) := by revert i; decide
    rw [(st4 i n4).1, (st4 i n4).2, (fr_st Z f2 i n2).1, (fr_st Z f2 i n2).2]
    exact ⟨rfl, rfl⟩
  refine ⟨⟨j4, by rw [d1, recStream_fieldNums]⟩, d2, by rw [(st4 30 (by decide)).2]; exact b2,
    by rw [v4 34 (by decide)]; exact hNK2, by rw [(fr_st Z f4 33 (by decide)).2]; exact c1.wh,
    by rw [(fr_st Z f4 33 (by decide)).1]; exact c1.wl, by rw [(s2 24 (by decide)).2]; exact a5,
    by rw [(s2 24 (by decide)).1]; exact a6, ?_, ?_⟩
  · intro i hi
    have e := s2 i (by revert i; decide)
    have hc : i = 25 ∨ i = 27 ∨ i = 28 ∨ i = 29 := by simpa using hi
    rcases hc with rfl | rfl | rfl | rfl
    · obtain ⟨v, hv⟩ := a3; exact ⟨v, by rw [e.1]; exact hv.1, by rw [e.2]; exact hv.2⟩
    · obtain ⟨v, hv⟩ := a4.q; exact ⟨v, by rw [e.1]; exact hv.1, by rw [e.2]; exact hv.2⟩
    · obtain ⟨v, hv⟩ := a4.m; exact ⟨v, by rw [e.1]; exact hv.1, by rw [e.2]; exact hv.2⟩
    · obtain ⟨v, hv⟩ := a4.x; exact ⟨v, by rw [e.1]; exact hv.1, by rw [e.2]; exact hv.2⟩
  · have hall := (f12.comp' f3).comp' f4
    refine ⟨fun x hx => hall.1 x ?_, fun r hr => ?_, hall.2.2⟩
    · intro hm; apply hx
      simp only [List.mem_append] at hm
      rcases hm with ((h | h) | h) | h
      · exact map_subset Z ([24, 25, 27, 28, 29, 30] : List (Fin 64)) _ (by decide) x h
      · exact map_subset Z ([30] : List (Fin 64)) _ (by decide) x h
      · exact map_subset Z ([33, 32] : List (Fin 64)) _ (by decide) x h
      · exact map_subset Z ([32] : List (Fin 64)) _ (by decide) x h
    · by_cases h31 : r = Y 31
      · subst h31; rw [v4 31 (by decide), b3]; exact (hz 31 (by decide)).symm
      · by_cases h40 : r = Y 40
        · subst h40; rw [d3]; exact (hz 40 (by decide)).symm
        · refine hall.2.1 r ?_
          simp only [List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr ⊢
          tauto

theorem occB2_spec (cap L : ℕ) (hL : 1 ≤ L) (σ : WState ns nr) (xs : List ℕ) (j : List Bool)
    (hI : σ.st (Z 32) = recStream (xs.map (binary L)) ++ j) (hIh : σ.sh (Z 32) = 0)
    (hWh : σ.sh (Z 33) = 0) (hWl : (σ.st (Z 33)).length ≤ 2 * L + 1) (hOh : σ.sh (Z 31) = 0)
    (h91 : σ.val (Y 91) = 0) (h92 : σ.val (Y 92) = 0) (h93 : σ.val (Y 93) = 0) (h95 : σ.val (Y 95) = 0)
    (hcap : xs.length * (2 * L + 1) + 2 * L + 2 ≤ cap) :
    Runs cap (occB2 Z Y) σ (occB2Cost L xs.length) (fun τ =>
      (∃ j', τ.st (Z 31) = recStream (xs.map (binary L)) ++ j') ∧ τ.sh (Z 31) = 0 ∧
      τ.sh (Z 33) = 0 ∧ (τ.st (Z 33)).length ≤ 2 * L + 1 ∧
      SameExcept σ τ (([33, 31] : List (Fin 64)).map Z) (([] : List (Fin 112)).map Y)) := by
  have hO5 : OutOn σ (Z 31) (Y 95) [] (σ.st (Z 31)) := outOn_start σ _ _ hOh h95
  have h5 := copyAll_spec cap (I := Z 32) (Wk := Z 33) (O := Z 31) (CI := Y 91) (CW := Y 92) (CS := Y 93)
    (CO := Y 95) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) L hL xs σ j [] (σ.st (Z 31)) hI hIh h91 h92 h93
    hWh hWl hO5 hcap (by simp only [List.length_nil]; omega)
  refine Runs.seq h5 fun τ5 hτ5 => ?_
  obtain ⟨e1, e2, e3, e4⟩ := hτ5
  rw [List.nil_append] at e1
  have hcl : (xs.flatMap fun x => frame (binary L x)).length = xs.length * (2 * L + 1) := by
    have : ∀ l : List ℕ, (l.flatMap fun x => frame (binary L x)).length = l.length * (2 * L + 1) := by
      intro l
      induction l with
      | nil => simp
      | cons x l ih => simp only [List.flatMap_cons, List.length_append, ih, frame_length, binary_length,
          List.length_cons]; ring
    exact this xs
  have h6 := closeOut_runs cap τ5 _ _ e1 (by rw [hcl]; omega)
  rw [hcl] at h6
  refine h6.post fun τ6 hτ6 => ?_
  obtain ⟨⟨j6, g1⟩, g2, g3, g4⟩ := hτ6
  have hall := e4.comp' g4
  refine ⟨⟨j6, by rw [g1, recFrames_eq]⟩, g2, ?_, ?_, ?_⟩
  · rw [g4.sh (by simp [emb_eq_iff])]; exact e2
  · rw [g4.st (by simp [emb_eq_iff])]; exact e3
  · refine ⟨fun x hx => hall.1 x ?_, fun r _ => ?_, hall.2.2⟩
    · intro hm; apply hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      tauto
    · by_cases h : r = Y 95
      · subst h; rw [g3]; exact h95.symm
      · exact hall.2.1 r (by simp [h])

theorem occB3_spec (cap s K T M : ℕ) (σ : WState ns nr) (h34 : σ.val (Y 34) = K) (h47 : σ.val (Y 47) = T)
    (h97 : σ.val (Y 97) = 0) (h96 : σ.val (Y 96) = 0) (h91 : σ.val (Y 91) = 0) (h41 : σ.val (Y 41) = s + 1)
    (h44 : σ.val (Y 44) = M) (hcap : K * T + 2 * K + T + M + s + 1 ≤ cap) :
    Runs cap (occB3 Y) σ (occB3Cost s K T) (fun τ =>
      τ.val (Y 47) = K * T ∧ τ.val (Y 44) = M + (s + 1) ∧ τ.val (Y 34) = 0 ∧
      SameExcept σ τ (([] : List (Fin 64)).map Z) (([34, 47, 44] : List (Fin 112)).map Y)) := by
  have n47_97 : Y 47 ≠ Y 97 := Y.injective.ne (by decide)
  have n97_47 : Y 97 ≠ Y 47 := Y.injective.ne (by decide)
  have h7 := mulR_spec cap (A := Y 34) (A2 := Y 96) (B := Y 47) (C := Y 97) (T := Y 91) (by simp [emb_eq_iff]) σ
    h96 h91 (by rw [h34, h47, h97]; omega) (by rw [h34]; omega)
  rw [h34, h47, h97, Nat.zero_add] at h7
  refine Runs.seqE h7 ?_
  set τ7 := σ.setv (Y 97) (K * T) with hτ7
  have e47 : τ7.val (Y 47) = T := by simp only [hτ7, WState.setv_val, Function.update_of_ne n47_97, h47]
  have h8 := wclear_spec (cap := cap) (Y 47) T τ7 e47 (by rw [e47]; omega)
  refine Runs.seqE (WXExec.wm h8) ?_
  set τ8 := τ7.setv (Y 47) 0 with hτ8
  have e97 : τ8.val (Y 97) = K * T := by
    simp only [hτ8, hτ7, WState.setv_val, Function.update_of_ne n97_47, Function.update_self]
  have e47' : τ8.val (Y 47) = 0 := by simp only [hτ8, WState.setv_val, Function.update_self]
  have h9 := wmove_spec (cap := cap) (Y 97) (Y 47) n97_47 (K * T) τ8 e97 (by rw [e97]; omega)
    (by rw [e97, e47']; omega)
  rw [e97, e47', Nat.zero_add] at h9
  refine Runs.seqE (WXExec.wm h9) ?_
  set τ9 := (τ8.setv (Y 97) 0).setv (Y 47) (K * T) with hτ9
  have v9 : ∀ r : Fin 112, r ∉ ([97, 47] : List (Fin 112)) → τ9.val (Y r) = σ.val (Y r) := by
    intro r hr
    have a : Y r ≠ Y 97 := Y.injective.ne (fun e => hr (by simp [e]))
    have b : Y r ≠ Y 47 := Y.injective.ne (fun e => hr (by simp [e]))
    simp only [hτ9, hτ8, hτ7, WState.setv_val, Function.update_of_ne a, Function.update_of_ne b]
  have e34 : τ9.val (Y 34) = K := by rw [v9 34 (by decide)]; exact h34
  have h10 := wclear_spec (cap := cap) (Y 34) K τ9 e34 (by rw [e34]; omega)
  refine Runs.seqE (WXExec.wm h10) ?_
  set τ10 := τ9.setv (Y 34) 0 with hτ10
  have v10 : ∀ r : Fin 112, r ∉ ([97, 47, 34] : List (Fin 112)) → τ10.val (Y r) = σ.val (Y r) := by
    intro r hr
    have a : Y r ≠ Y 34 := Y.injective.ne (fun e => hr (by simp [e]))
    rw [hτ10, WState.setv_val, Function.update_of_ne a]
    exact v9 r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto))
  have e41 : τ10.val (Y 41) = s + 1 := by rw [v10 41 (by decide)]; exact h41
  have e44 : τ10.val (Y 44) = M := by rw [v10 44 (by decide)]; exact h44
  have e91 : τ10.val (Y 91) = 0 := by rw [v10 91 (by decide)]; exact h91
  have h11 := addR_spec cap (A := Y 41) (B := Y 44) (T := Y 91) (Y.injective.ne (by decide))
    (Y.injective.ne (by decide)) (Y.injective.ne (by decide)) τ10 e91 (by rw [e41, e44]; omega)
  rw [e41, e44] at h11
  refine Runs.of h11 ?_
  have n44_97 : Y 44 ≠ Y 97 := Y.injective.ne (by decide)
  have n44_47 : Y 44 ≠ Y 47 := Y.injective.ne (by decide)
  have n44_34 : Y 44 ≠ Y 34 := Y.injective.ne (by decide)
  have n34_47 : Y 34 ≠ Y 47 := Y.injective.ne (by decide)
  have n34_97 : Y 34 ≠ Y 97 := Y.injective.ne (by decide)
  refine ⟨?_, ?_, ?_, fun x _ => by simp [hτ10, hτ9, hτ8, hτ7], fun r hr => ?_, by simp [hτ10, hτ9, hτ8, hτ7]⟩
  · rw [WState.setv_val, Function.update_of_ne n44_47.symm, hτ10, WState.setv_val,
      Function.update_of_ne n34_47.symm, hτ9, WState.setv_val, Function.update_self]
  · rw [WState.setv_val, Function.update_self]
  · rw [WState.setv_val, Function.update_of_ne n44_34.symm, hτ10, WState.setv_val, Function.update_self]
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n34, n47, n44⟩ := hr
    by_cases h : r = Y 97
    · subst h
      rw [WState.setv_val, Function.update_of_ne n44_97.symm, hτ10, WState.setv_val,
        Function.update_of_ne n34_97.symm, hτ9, WState.setv_val, Function.update_of_ne n47_97.symm,
        WState.setv_val, Function.update_self, h97]
    · simp only [hτ10, hτ9, hτ8, hτ7, WState.setv_val, Function.update_of_ne n44, Function.update_of_ne n34,
        Function.update_of_ne n47, Function.update_of_ne h]

/-- `GRest` after `occB`, from its frame and the facts its parts return. -/
theorem occB_rest {cap W s k : ℕ} {σ τ : WState ns nr} (hrest : GRest Z Y cap W s k σ)
    (hfr : SameExcept σ τ (occBStreams Z) [Y 44, Y 47])
    (hw : ∀ i ∈ ([25, 27, 28, 29] : List (Fin 64)), ∃ v, NumOn τ (Z i) ((s + 1) * (W + 1)) v)
    (h24 : τ.sh (Z 24) = 0 ∧ (τ.st (Z 24)).length ≤ 2 * ((s + 1) * (W + 1)) + 1)
    (h33 : τ.sh (Z 33) = 0 ∧ (τ.st (Z 33)).length ≤ 2 * ((s + 1) * (W + 1)) + 1)
    (h30 : τ.sh (Z 30) = 0) (h31 : τ.sh (Z 31) = 0) (h32 : τ.sh (Z 32) = 0) : GRest Z Y cap W s k τ := by
  have hmem : ∀ i : Fin 64, Z i ∈ occBStreams Z ↔ i ∈ occBIdx := fun i => by
    unfold occBStreams; rw [List.mem_map]
    exact ⟨fun ⟨j, hj, e⟩ => Z.injective e ▸ hj, fun h => ⟨i, h, rfl⟩⟩
  refine grest_frame Z Y hrest hfr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi hm; rw [hmem] at hm
    exact absurd hm ((by decide : ∀ i ∈ w1List, i ∉ occBIdx) i hi)
  · intro i hi hm
    rw [hmem] at hm
    exact hw i ((by decide : ∀ i ∈ wcList, i ∈ occBIdx → i ∈ ([25, 27, 28, 29] : List (Fin 64))) i hi hm)
  · intro i hi hm; rw [hmem] at hm
    exact absurd hm ((by decide : ∀ i ∈ [(20 : Fin 64), 21, 53, 26, 44, 45, 55], i ∉ occBIdx) i hi)
  · intro i hi hm; rw [hmem] at hm
    exact absurd hm ((by decide : ∀ i ∈ [(3 : Fin 64), 47], i ∉ occBIdx) i hi)
  · intro i hi _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact h24
    · exact h33
  · intro i hi hm
    rw [hmem] at hm
    have hc : i = 30 ∨ i = 31 ∨ i = 32 :=
      (by decide : ∀ i ∈ [(0 : Fin 64), 2, 30, 31, 32], i ∈ occBIdx → i = 30 ∨ i = 31 ∨ i = 32) i hi hm
    rcases hc with rfl | rfl | rfl
    · exact h30
    · exact h31
    · exact h32
  · intro r hr hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, emb_eq_iff] at hm
    rcases hm with rfl | rfl
    · exact absurd hr (by decide)
    · exact absurd hr (by decide)
  · intro r hr hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, emb_eq_iff] at hm
    exact absurd hm ((by decide : ∀ r ∈ [(13 : Fin 112), 32, 41, 66, 84, 89], ¬ (r = 44 ∨ r = 47)) r hr)

/-- **One occurrence, second half.** From the children on `Z 2` and the current tuples `tf` (of `M` fields each) on
`Z 31`, the tuple stream becomes `newT css tf`, `NT = |css|·|tf|`, `M := M + (s + 1)`. -/
theorem occB_spec (cap W s k M : ℕ) (hs1 : 1 ≤ s) (σ : WState ns nr) (css tf : List (List ℤ)) (junk : List Bool)
    (hrest : GRest Z Y cap W s k σ)
    (hkd : σ.st (Z 2) = recStream (css.map (recBits W)) ++ junk) (hkdh : σ.sh (Z 2) = 0)
    (hlen : ∀ c ∈ css, c.length = s + 1) (hfit : ∀ c ∈ css, ∀ y ∈ c, y.natAbs < 2 ^ W)
    (htf : ∃ junk, σ.st (Z 31) = recStream ((fieldNums tf).map (binary ((s + 1) * (W + 1)))) ++ junk)
    (htfl : ∀ t ∈ tf, t.length = M) (hM : σ.val (Y 44) = M) (hNT : σ.val (Y 47) = tf.length)
    (hcapE : css.length * (2 * ((s + 1) * (W + 1)) + 1) + 2 * ((s + 1) * (W + 1)) + 2 + 2 * (s + 1) ≤ cap)
    (hcapEO : css.length * (s + 1) * (2 * ((s + 1) * (W + 1)) + 1) + 1 ≤ cap)
    (hcapT : TCap cap ((s + 1) * (W + 1)) (s + 1) M css.length tf.length [])
    (hcapC : css.length * tf.length * (s + 1 + M) * (2 * ((s + 1) * (W + 1)) + 1) + 2 * ((s + 1) * (W + 1)) + 2 ≤ cap)
    (hcapR : css.length * tf.length + 2 * css.length + tf.length + M + s + 1 ≤ cap) :
    Runs cap (occB Z Y) σ (occBCost W s css.length tf.length M) (fun τ =>
      GRest Z Y cap W s k τ ∧
      (∃ junk', τ.st (Z 31) = recStream ((fieldNums (newT css tf)).map (binary ((s + 1) * (W + 1)))) ++ junk') ∧
      τ.val (Y 44) = M + (s + 1) ∧ τ.val (Y 47) = css.length * tf.length ∧
      SameExcept σ τ (occBStreams Z) [Y 44, Y 47]) := by
  have hz := hrest.zero
  have hLc1 : 1 ≤ (s + 1) * (W + 1) := by nlinarith
  refine Runs.seq (occB1_spec Z Y cap W s k M hs1 σ css tf junk hrest hkd hkdh hlen hfit htf htfl hM hNT hcapE
    hcapEO hcapT) fun τ1 h1 => ?_
  obtain ⟨⟨j1, a1⟩, a2, a3, a4, a5, a6, a7, a8, a9, f1⟩ := h1
  have v1 : ∀ r : Fin 112, r ≠ 34 → τ1.val (Y r) = σ.val (Y r) := fun r hr => fr_val Y f1 r (by simpa using hr)
  have hxl : (fieldNums (newT css tf)).length = css.length * tf.length * (s + 1 + M) := by
    rw [fieldNums_length (s + 1 + M) _ (newT_mem_length (s + 1) M css tf hlen htfl), newT_length]
  have h2 := occB2_spec Z Y cap ((s + 1) * (W + 1)) hLc1 τ1 (fieldNums (newT css tf)) j1 a1 a2 a5 a6
    (by rw [(fr_st Z f1 31 (by decide)).2]; exact hrest.closed 31 (by simp))
    (by rw [v1 91 (by decide)]; exact hz 91 (by decide)) (by rw [v1 92 (by decide)]; exact hz 92 (by decide))
    (by rw [v1 93 (by decide)]; exact hz 93 (by decide)) (by rw [v1 95 (by decide)]; exact hz 95 (by decide))
    (by rw [hxl]; omega)
  rw [hxl] at h2
  refine Runs.seq h2 fun τ2 h2' => ?_
  obtain ⟨⟨j2, b1⟩, b2, b3, b4, f2⟩ := h2'
  have v2 : ∀ r : Fin 112, τ2.val (Y r) = τ1.val (Y r) := fun r => fr_val Y f2 r (by simp)
  have h3 := occB3_spec Z Y cap s css.length tf.length M τ2 (by rw [v2]; exact a4)
    (by rw [v2, v1 47 (by decide)]; exact hNT) (by rw [v2, v1 97 (by decide)]; exact hz 97 (by decide))
    (by rw [v2, v1 96 (by decide)]; exact hz 96 (by decide)) (by rw [v2, v1 91 (by decide)]; exact hz 91 (by decide))
    (by rw [v2, v1 41 (by decide)]; exact hrest.r41) (by rw [v2, v1 44 (by decide)]; exact hM) hcapR
  refine h3.post fun τ3 h3' => ?_
  obtain ⟨c1, c2, c3, f3⟩ := h3'
  have st3 : ∀ i : Fin 64, τ3.st (Z i) = τ2.st (Z i) ∧ τ3.sh (Z i) = τ2.sh (Z i) := fun i => fr_st Z f3 i (by simp)
  have st2 : ∀ i : Fin 64, i ∉ ([33, 31] : List (Fin 64)) →
      τ3.st (Z i) = τ1.st (Z i) ∧ τ3.sh (Z i) = τ1.sh (Z i) := fun i hi =>
    ⟨(st3 i).1.trans (fr_st Z f2 i hi).1, (st3 i).2.trans (fr_st Z f2 i hi).2⟩
  have hall := (f1.comp' f2).comp' f3
  have hfr : SameExcept σ τ3 (occBStreams Z) [Y 44, Y 47] := by
    refine ⟨fun x hx => hall.1 x ?_, fun r hr => ?_, hall.2.2⟩
    · intro hm; apply hx
      simp only [List.mem_append] at hm
      unfold occBStreams
      rcases hm with (h | h) | h
      · exact map_subset Z ([24, 25, 27, 28, 29, 30, 33, 32] : List (Fin 64)) occBIdx (by decide) x h
      · exact map_subset Z ([33, 31] : List (Fin 64)) occBIdx (by decide) x h
      · simp at h
    · by_cases h34 : r = Y 34
      · subst h34; rw [c3]; exact (hz 34 (by decide)).symm
      · refine hall.2.1 r ?_
        simp only [List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr ⊢
        tauto
  refine ⟨occB_rest Z Y hrest hfr ?_ ?_ ?_ ?_ ?_ ?_, ⟨j2, by rw [(st3 31).1]; exact b1⟩, c2, c1, hfr⟩
  · intro i hi
    have e := st2 i ((by decide : ∀ i ∈ ([25, 27, 28, 29] : List (Fin 64)), i ∉ ([33, 31] : List (Fin 64))) i hi)
    obtain ⟨v, hv⟩ := a9 i hi
    exact ⟨v, by rw [e.1]; exact hv.1, by rw [e.2]; exact hv.2⟩
  · rw [(st2 24 (by decide)).1, (st2 24 (by decide)).2]; exact ⟨a7, a8⟩
  · rw [(st3 33).1, (st3 33).2]; exact ⟨b3, b4⟩
  · rw [(st2 30 (by decide)).2]; exact a3
  · rw [(st3 31).2]; exact b2
  · rw [(st2 32 (by decide)).2]; exact a2

end OccB

end NearCubicGates.Close.TabMachine
