import Proof.Wire_3_5.SeedFixFacCopy
import Proof.Wire_3_5.SeedFixSampExpr
import Proof.Wire_3_5.BlockCopy

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)

/-! ## The coefficient of a product term -/

theorem coefWord_unit (c : ℤ) (hc : c = 1 ∨ c = -1) : coefWord c = [true, decide (c < 0), true, true, false] := by
  rcases hc with rfl | rfl <;> rfl

/-- **The product's coefficient word**: the left sign xor the right sign, then the left magnitude's frame. -/
theorem coefWord_mul (c c' : ℤ) (hc : c ≠ 0) (hc' : c' = 1 ∨ c' = -1) :
    coefWord (c * c') = [true, xor (decide (c < 0)) (decide (c' < 0))] ++ frame (Nat.bits c.natAbs) := by
  rcases hc' with rfl | rfl
  · simp [coefWord, frame]
  · have hs : decide (c * -1 < 0) = !decide (c < 0) := by
      rcases lt_or_gt_of_ne hc with h | h
      · have h1 : ¬ c * -1 < 0 := by omega
        rw [decide_eq_false h1, decide_eq_true h]; rfl
      · have h1 : c * -1 < 0 := by omega
        have h2 : ¬ c < 0 := by omega
        rw [decide_eq_true h1, decide_eq_false h2]; rfl
    have hn : (c * -1).natAbs = c.natAbs := by simp
    rw [coefWord, hs, hn]
    simp [frame]

theorem coefWord_split (c : ℤ) : coefWord c = [true, decide (c < 0)] ++ frame (Nat.bits c.natAbs) := rfl

theorem termWord_eq (t : ℤ × List (List (List ℕ))) : termWord t = coefWord t.1 ++ (facRecs t.2 ++ [false]) := rfl

/-! ## Small cell machines -/

namespace CopyCell
open NearCubicWires.WireExponent3_5.GF2.Two (act cfg)

/-- Copy the source cell to the output, both heads one cell right. -/
def machine : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q sc => if q.val = 0 then some (act 1 (none) (some (sc 0)) .right .right) else none

theorem run (S : List Bool) (h : ℕ) (o B : List Bool) :
    Step machine 1 ![h, o.length] ![S, overlay o B] ![h + 1, o.length + 1] ![S, overlay (o ++ [readTapeBit S h]) B] := by
  have s1 : step machine (cfg 0 S (overlay o B) h o.length) =
      some (cfg 1 S (overlay (o ++ [readTapeBit S h]) B) (h + 1) (o.length + 1)) := by
    rw [Two.step_cfg machine 0 1 S (overlay o B) h o.length none (some (readTapeBit S h)) .right .right
      (by simp [machine])]
    simp only [Two.wr, HeadMove.apply, overlay_write]
  obtain ⟨r, hr, hf, hs⟩ := (Timed.single (p := machine) rfl s1).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end CopyCell

namespace SignCell
open NearCubicWires.WireExponent3_5.GF2.Three (act cfg)

/-- Tapes `0` the left term (its coefficient frame at cell 0), `1` the right term (at its marker), `2` the output:
write the term marker, the frame marker and the xor of the two signs, then step the right head past its coefficient. -/
def machine : Machine 3 7 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 6
  rule := fun q sc =>
    if q.val = 0 then some (act 1 none none (some true) .right .right .right)
    else if q.val = 1 then some (act 2 none none (some true) .stay .right .right)
    else if q.val = 2 then some (act 3 none none (some (xor (sc 0) (sc 1))) .right .right .right)
    else if q.val = 3 then some (act 4 none none none .stay .right .stay)
    else if q.val = 4 then some (act 5 none none none .stay .right .stay)
    else if q.val = 5 then some (act 6 none none none .stay .right .stay)
    else none

theorem run (T S : List Bool) (h : ℕ) (o B : List Bool) :
    Step machine 6 ![0, h, o.length] ![T, S, overlay o B] ![2, h + 6, o.length + 3]
      ![T, S, overlay (o ++ [true, true, xor (readTapeBit T 1) (readTapeBit S (h + 2))]) B] := by
  set x := xor (readTapeBit T 1) (readTapeBit S (h + 2))
  have s1 : step machine (cfg 0 T S (overlay o B) 0 h o.length) =
      some (cfg 1 T S (overlay (o ++ [true]) B) 1 (h + 1) (o.length + 1)) := by
    rw [Three.step_cfg machine 0 1 T S (overlay o B) 0 h o.length none none (some true) .right .right .right
      (by simp [machine])]
    simp only [Two.wr, HeadMove.apply, overlay_write]
  have s2 : step machine (cfg 1 T S (overlay (o ++ [true]) B) 1 (h + 1) (o.length + 1)) =
      some (cfg 2 T S (overlay (o ++ [true, true]) B) 1 (h + 2) (o.length + 2)) := by
    rw [Three.step_cfg machine 1 2 T S (overlay (o ++ [true]) B) 1 (h + 1) (o.length + 1) none none (some true)
      .stay .right .right (by simp [machine])]
    simp only [Two.wr, HeadMove.apply]
    have := overlay_write (o ++ [true]) B true
    rw [List.length_append, List.length_singleton] at this
    rw [this, List.append_assoc]
    rfl
  have s3 : step machine (cfg 2 T S (overlay (o ++ [true, true]) B) 1 (h + 2) (o.length + 2)) =
      some (cfg 3 T S (overlay (o ++ [true, true, x]) B) 2 (h + 3) (o.length + 3)) := by
    rw [Three.step_cfg machine 2 3 T S (overlay (o ++ [true, true]) B) 1 (h + 2) (o.length + 2) none none (some x)
      .right .right .right (by simp [machine, x])]
    simp only [Two.wr, HeadMove.apply]
    have := overlay_write (o ++ [true, true]) B x
    rw [List.length_append] at this
    rw [show o.length + [true, true].length = o.length + 2 by rfl] at this
    rw [this, List.append_assoc]
    rfl
  have s4 : step machine (cfg 3 T S (overlay (o ++ [true, true, x]) B) 2 (h + 3) (o.length + 3)) =
      some (cfg 4 T S (overlay (o ++ [true, true, x]) B) 2 (h + 4) (o.length + 3)) := by
    rw [Three.step_cfg machine 3 4 T S _ 2 (h + 3) (o.length + 3) none none none .stay .right .stay
      (by simp [machine])]
    rfl
  have s5 : step machine (cfg 4 T S (overlay (o ++ [true, true, x]) B) 2 (h + 4) (o.length + 3)) =
      some (cfg 5 T S (overlay (o ++ [true, true, x]) B) 2 (h + 5) (o.length + 3)) := by
    rw [Three.step_cfg machine 4 5 T S _ 2 (h + 4) (o.length + 3) none none none .stay .right .stay
      (by simp [machine])]
    rfl
  have s6 : step machine (cfg 5 T S (overlay (o ++ [true, true, x]) B) 2 (h + 5) (o.length + 3)) =
      some (cfg 6 T S (overlay (o ++ [true, true, x]) B) 2 (h + 6) (o.length + 3)) := by
    rw [Three.step_cfg machine 5 6 T S _ 2 (h + 5) (o.length + 3) none none none .stay .right .stay
      (by simp [machine])]
    rfl
  have t := (((((Timed.single (p := machine) rfl s1).trans (Timed.single (p := machine) rfl s2)).trans
    (Timed.single (p := machine) rfl s3)).trans (Timed.single (p := machine) rfl s4)).trans
    (Timed.single (p := machine) rfl s5)).trans (Timed.single (p := machine) rfl s6)
  obtain ⟨r, hr, hf, hs⟩ := t.run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end SignCell

/-! ## The inner body: one product term (tapes 0 the left term register, 1 the right expression, 2 the output) -/

def i3AC : Fin 2 → Fin 3 := ![0, 2]

theorem install_i3AC (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install i3AC A v = ![v 0, A 1, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_i3AC (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH i3AC H v = ![v 0, H 1, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def i3A : Fin 1 → Fin 3 := ![0]

theorem install_i3A (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install i3A A v = ![v 0, A 1, A 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_i3A (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH i3A H v = ![v 0, H 1, H 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def i3BC : Fin 2 → Fin 3 := ![1, 2]

theorem install_i3BC (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install i3BC A v = ![A 0, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_i3BC (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH i3BC H v = ![H 0, v 0, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

theorem facRecs_append (x y : List (List (List ℕ))) : facRecs (x ++ y) = facRecs x ++ facRecs y := by
  simp [facRecs]

/-- One product term. -/
noncomputable def innerBody :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    SignCell.machine (RecoveryFocus.machine i3AC CopyO.machine)) (RecoveryFocus.machine i3A nudgeM))
    (RecoveryFocus.machine i3AC (FacCopy.machine true))) (RecoveryFocus.machine i3BC (FacCopy.machine true)))
    (RecoveryFocus.machine i3BC CopyCell.machine)

/-- The product term of two terms. -/
def prodTerm (a b : ℤ × List (List (List ℕ))) : ℤ × List (List (List ℕ)) := (a.1 * b.1, a.2 ++ b.2)

def mInnerCost (a b : ℤ × List (List (List ℕ))) : ℕ :=
  6 + 1 + (2 * (Nat.bits a.1.natAbs).length + 1) + 1 + 1 + 1 + ((facRecs a.2).length + 1) + 1 +
    ((facRecs b.2).length + 1) + 1 + 1

/-- The left register's head after one product term. -/
def innerAT (a : ℤ × List (List (List ℕ))) : ℕ := 2 + 2 * (Nat.bits a.1.natAbs).length + 1 + (facRecs a.2).length

theorem inner_step (a b : ℤ × List (List (List ℕ))) (ha : a.1 ≠ 0) (hb : b.1 = 1 ∨ b.1 = -1)
    (ATs PB SB o BC : List Bool) :
    Step innerBody (mInnerCost a b) ![0, PB.length, o.length]
      ![termWord a ++ ATs, PB ++ (true :: termWord b) ++ SB, overlay o BC]
      ![innerAT a, PB.length + (true :: termWord b).length, (o ++ true :: termWord (prodTerm a b)).length]
      ![termWord a ++ ATs, PB ++ (true :: termWord b) ++ SB, overlay (o ++ true :: termWord (prodTerm a b)) BC] := by
  set sa := decide (a.1 < 0)
  set sb := decide (b.1 < 0)
  set bits := Nat.bits a.1.natAbs
  set T := termWord a ++ ATs
  set S := PB ++ (true :: termWord b) ++ SB
  have eT : T = [true, sa] ++ frame bits ++ (facRecs a.2 ++ false :: ATs) := by
    simp only [T, termWord_eq, coefWord_split, List.append_assoc]; rfl
  have eS : S = PB ++ [true, true, sb, true, true, false] ++ (facRecs b.2 ++ false :: SB) := by
    simp [S, termWord_eq, coefWord_unit b.1 hb, sb]
  have hT1 : readTapeBit T 1 = sa := by rw [eT]; rfl
  have hS2 : readTapeBit S (PB.length + 2) = sb := by
    rw [eS]
    have := Streaming.read_append (PB ++ [true, true]) ([true, true, false] ++ (facRecs b.2 ++ false :: SB)) sb
    simpa [List.append_assoc] using this
  -- 1: marker, frame marker, sign
  have s1 := SignCell.run T S PB.length o BC
  rw [hT1, hS2] at s1
  set x := xor sa sb
  -- 2: the left magnitude's frame
  obtain ⟨cr, hcr, hcrf⟩ := CopyO.copy_run [true, sa] bits (facRecs a.2 ++ false :: ATs) (o ++ [true, true, x]) BC
  rw [← eT] at hcr hcrf
  have hc2 : Step CopyO.machine (2 * bits.length + 1) ![2, (o ++ [true, true, x]).length]
      ![T, overlay (o ++ [true, true, x]) BC] ![2 + 2 * bits.length, (o ++ [true, true, x] ++ frame bits).length]
      ![T, overlay (o ++ [true, true, x] ++ frame bits) BC] := by
    refine ⟨cr, hcr, ?_, ?_, runFrom_steps_le _ _ _ _ hcr⟩
    · rw [hcrf]; funext j; fin_cases j <;> simp [CopyO.config, frame_length]
    · rw [hcrf]; funext j; fin_cases j <;> rfl
  have s2 := dockRun hc2 i3AC (by decide) ![2, PB.length + 6, (o ++ [true, true, x]).length]
    ![T, S, overlay (o ++ [true, true, x]) BC] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_i3AC, install_i3AC] at s2
  -- 3: past the frame's end
  have s3 := dockRun (nudge_run T (2 + 2 * bits.length)) i3A (by decide)
    ![2 + 2 * bits.length, PB.length + 6, (o ++ [true, true, x] ++ frame bits).length]
    ![T, S, overlay (o ++ [true, true, x] ++ frame bits) BC] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_i3A, install_i3A] at s3
  -- 4: the left factors
  have hf4 := FacCopy.run true ([true, sa] ++ frame bits) a.2 ATs (o ++ [true, true, x] ++ frame bits) BC
  have eT4 : [true, sa] ++ frame bits ++ facRecs a.2 ++ false :: ATs = T := by rw [eT]; simp
  rw [eT4] at hf4
  have ep4 : ([true, sa] ++ frame bits).length = 2 + 2 * bits.length + 1 := by simp [frame_length]; omega
  rw [ep4] at hf4
  simp only [owC, if_true] at hf4
  have s4 := dockRun hf4 i3AC (by decide)
    ![2 + 2 * bits.length + 1, PB.length + 6, (o ++ [true, true, x] ++ frame bits).length]
    ![T, S, overlay (o ++ [true, true, x] ++ frame bits) BC] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_i3AC, install_i3AC] at s4
  -- 5: the right factors
  set O4 := o ++ [true, true, x] ++ frame bits ++ facRecs a.2
  have hf5 := FacCopy.run true (PB ++ [true, true, sb, true, true, false]) b.2 SB O4 BC
  have eS5 : PB ++ [true, true, sb, true, true, false] ++ facRecs b.2 ++ false :: SB = S := by
    rw [eS]; simp
  rw [eS5] at hf5
  have ep5 : (PB ++ [true, true, sb, true, true, false]).length = PB.length + 6 := by simp
  rw [ep5] at hf5
  simp only [owC, if_true] at hf5
  have s5 := dockRun hf5 i3BC (by decide)
    ![2 + 2 * bits.length + 1 + (facRecs a.2).length, PB.length + 6, O4.length] ![T, S, overlay O4 BC]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_i3BC, install_i3BC] at s5
  -- 6: the terminator
  set O5 := O4 ++ facRecs b.2
  have hS6 : readTapeBit S (PB.length + 6 + (facRecs b.2).length) = false := by
    rw [eS, show PB.length + 6 + (facRecs b.2).length = (PB ++ [true, true, sb, true, true, false] ++ facRecs b.2).length
      by simp; omega]
    have := Streaming.read_append (PB ++ [true, true, sb, true, true, false] ++ facRecs b.2) SB false
    simpa [List.append_assoc] using this
  have hc6 := CopyCell.run S (PB.length + 6 + (facRecs b.2).length) O5 BC
  rw [hS6] at hc6
  have s6 := dockRun hc6 i3BC (by decide)
    ![2 + 2 * bits.length + 1 + (facRecs a.2).length, PB.length + 6 + (facRecs b.2).length, O5.length]
    ![T, S, overlay O5 BC] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_i3BC, install_i3BC] at s6
  have e2 : o.length + 3 = (o ++ [true, true, x]).length := by simp
  have hall := (((((s1.congr (hout' := ![2, PB.length + 6, (o ++ [true, true, x]).length]) (by
      funext j; fin_cases j <;> simp) rfl).seq (s2.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq
    (s3.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq
    (s4.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq
    (s5.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq
    (s6.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  have eOut : O5 ++ [false] = o ++ true :: termWord (prodTerm a b) := by
    simp only [O5, O4, prodTerm, termWord_eq, coefWord_mul a.1 b.1 ha hb, facRecs_append, List.append_assoc]
    rfl
  have eLen : (true :: termWord b).length = 6 + (facRecs b.2).length + 1 := by
    rw [List.length_cons, termWord_eq, coefWord_unit b.1 hb]; simp; omega
  unfold mInnerCost
  refine hall.congr ?_ ?_
  · funext j; fin_cases j
    · rfl
    · show PB.length + 6 + (facRecs b.2).length + 1 = PB.length + (true :: termWord b).length
      rw [eLen]; omega
    · show O5.length + 1 = (o ++ true :: termWord (prodTerm a b)).length
      rw [← eOut]; simp
  · funext j; fin_cases j
    · rfl
    · rfl
    · show overlay (O5 ++ [false]) BC = _
      rw [eOut]
      rfl

/-! ## The inner loop: the left term times every right term -/

/-- A term's record in an expression word. -/
def recT (t : ℤ × List (List (List ℕ))) : List Bool := true :: termWord t

theorem exprWord_eq (V : List (ℤ × List (List (List ℕ)))) : exprWord V = V.flatMap recT ++ [false] := rfl

theorem exprWord_split (V : List (ℤ × List (List (List ℕ)))) (S : List Bool) (j : ℕ) (hj : j < V.length) :
    exprWord V ++ S = (V.take j).flatMap recT ++ recT V[j] ++ ((V.drop (j + 1)).flatMap recT ++ false :: S) := by
  have e : V = V.take j ++ V[j] :: V.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  calc exprWord V ++ S = exprWord (V.take j ++ V[j] :: V.drop (j + 1)) ++ S := congrArg (fun W => exprWord W ++ S) e
    _ = _ := by simp only [exprWord_eq, List.flatMap_append, List.flatMap_cons, List.append_assoc, List.cons_append,
      List.nil_append]

theorem exprWord_read (V : List (ℤ × List (List (List ℕ)))) (S : List Bool) (j : ℕ) (hj : j ≤ V.length) :
    readTapeBit (exprWord V ++ S) ((V.take j).flatMap recT).length = decide (j < V.length) := by
  by_cases h : j < V.length
  · rw [exprWord_split V S j h, decide_eq_true h, List.append_assoc]
    exact Streaming.read_append _ _ _
  · have hj' : j = V.length := by omega
    subst hj'
    rw [decide_eq_false h, List.take_length, exprWord_eq, List.append_assoc]
    exact Streaming.read_append _ _ _

theorem recT_le_flatMap : ∀ (V : List (ℤ × List (List (List ℕ)))) (b : ℤ × List (List (List ℕ))), b ∈ V →
    (recT b).length ≤ (V.flatMap recT).length
  | [], _, hb => absurd hb List.not_mem_nil
  | c :: V, b, hb => by
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hb with rfl | h
    · omega
    · have := recT_le_flatMap V b h; omega

theorem termWord_le_exprWord (V : List (ℤ × List (List (List ℕ)))) (b : ℤ × List (List (List ℕ))) (hb : b ∈ V) :
    (termWord b).length ≤ (exprWord V).length := by
  have h := recT_le_flatMap V b hb
  rw [exprWord_eq, List.length_append]
  simp only [recT, List.length_cons] at h
  omega

theorem mInnerCost_eq (a b : ℤ × List (List (List ℕ))) (hb : b.1 = 1 ∨ b.1 = -1) :
    mInnerCost a b = (termWord a).length + (termWord b).length + 6 := by
  unfold mInnerCost
  rw [termWord_eq, termWord_eq, coefWord_split, coefWord_unit b.1 hb]
  simp [frame_length]
  omega

def selAT : Fin 3 → Bool := ![true, false, false]

/-- One product term, the left register rewound. -/
noncomputable def innerM := MaskedReset.machine innerBody selAT

noncomputable def innerLoopM := StreamController.machine innerM 1

/-- The uniform cost bound of one product term against the right expression `W`. -/
def innerBound (a : ℤ × List (List (List ℕ))) (W : List (ℤ × List (List (List ℕ)))) : ℕ :=
  (termWord a).length + (exprWord W).length + 6

/-- The product terms of `a` with the first `j` right terms, as records. -/
def outs (a : ℤ × List (List (List ℕ))) (W : List (ℤ × List (List (List ℕ)))) (j : ℕ) : List Bool :=
  (W.take j).flatMap fun b => recT (prodTerm a b)

theorem outs_succ (a : ℤ × List (List (List ℕ))) (W : List (ℤ × List (List (List ℕ)))) (j : ℕ) (hj : j < W.length) :
    outs a W (j + 1) = outs a W j ++ recT (prodTerm a W[j]) := by
  unfold outs
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append]
  simp

def mInnerH (W : List (ℤ × List (List (List ℕ)))) (o : List Bool) (a : ℤ × List (List (List ℕ))) (j : ℕ) : Fin 4 → ℕ :=
  ![0, ((W.take j).flatMap recT).length, (o ++ outs a W j).length, 0]

def mInnerA (W : List (ℤ × List (List (List ℕ)))) (SB o BC ATs : List Bool) (a : ℤ × List (List (List ℕ))) (cT : ℕ)
    (j : ℕ) : Fin 4 → List Bool :=
  ![termWord a ++ ATs, exprWord W ++ SB, overlay (o ++ outs a W j) BC, List.replicate cT false]

theorem innerM_step (a : ℤ × List (List (List ℕ))) (W : List (ℤ × List (List (List ℕ)))) (ha : a.1 ≠ 0)
    (hW : ∀ b ∈ W, b.1 = 1 ∨ b.1 = -1) (SB o BC ATs : List Bool) (cT : ℕ) (hcT : innerBound a W ≤ cT) (j : ℕ)
    (hj : j < W.length) :
    Step innerM (2 * innerBound a W + 2) (mInnerH W o a j) (mInnerA W SB o BC ATs a cT j)
      (mInnerH W o a (j + 1)) (mInnerA W SB o BC ATs a cT (j + 1)) := by
  have hb := hW W[j] (List.getElem_mem hj)
  have hs := inner_step a W[j] ha hb ATs ((W.take j).flatMap recT) ((W.drop (j + 1)).flatMap recT ++ false :: SB)
    (o ++ outs a W j) BC
  have hle : mInnerCost a W[j] ≤ innerBound a W := by
    rw [mInnerCost_eq a W[j] hb]; unfold innerBound
    have := termWord_le_exprWord W W[j] (List.getElem_mem hj); omega
  have hm := (hs.enlarge hle).mask (cap := cT) selAT (by intro i hi; fin_cases i <;> first | rfl | simp [selAT] at hi)
    (le_trans le_rfl hcT)
  have eB := exprWord_split W SB j hj
  have eO : o ++ outs a W j ++ true :: termWord (prodTerm a W[j]) = o ++ outs a W (j + 1) := by
    rw [outs_succ a W j hj]; simp [recT]
  have eP : ((W.take j).flatMap recT).length + (true :: termWord W[j]).length =
      ((W.take (j + 1)).flatMap recT).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append]; simp [recT]
  refine (hm.congr_in ?_ ?_).congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · rfl
    · show _ = exprWord W ++ SB
      rw [eB]; rfl
    · rfl
    · rfl
  · funext i; fin_cases i
    · rfl
    · exact eP
    · show (o ++ outs a W j ++ true :: termWord (prodTerm a W[j])).length = _
      rw [eO]; rfl
    · rfl
  · funext i; fin_cases i
    · rfl
    · show _ = exprWord W ++ SB
      rw [eB]; rfl
    · show overlay (o ++ outs a W j ++ true :: termWord (prodTerm a W[j])) BC = _
      rw [eO]; rfl
    · rfl

/-- **The left term times every right term**: the product terms appended to the output. -/
theorem innerLoop_run (a : ℤ × List (List (List ℕ))) (W : List (ℤ × List (List (List ℕ)))) (ha : a.1 ≠ 0)
    (hW : ∀ b ∈ W, b.1 = 1 ∨ b.1 = -1) (SB o BC ATs : List Bool) (cT : ℕ) (hcT : innerBound a W ≤ cT) :
    Step innerLoopM (W.length * (2 * innerBound a W + 2 + 2) + 1) (mInnerH W o a 0) (mInnerA W SB o BC ATs a cT 0)
      (mInnerH W o a W.length) (mInnerA W SB o BC ATs a cT W.length) := by
  let L : WhileBody 4 _ :=
    { body := innerM
      tape := 1
      bound := W.length
      H := mInnerH W o a
      A := mInnerA W SB o BC ATs a cT
      cost := fun _ => 2 * innerBound a W + 2
      step := fun j hj => innerM_step a W ha hW SB o BC ATs cT hcT j hj
      cont := fun j hj => by
        show readTapeBit (exprWord W ++ SB) ((W.take j).flatMap recT).length = true
        rw [exprWord_read W SB j (by omega)]; simpa using hj
      halt := by
        show readTapeBit (exprWord W ++ SB) ((W.take W.length).flatMap recT).length = false
        rw [exprWord_read W SB W.length (le_refl _)]; simp }
  have h := L.run
  rw [L.rest_const (2 * innerBound a W + 2) (fun _ => rfl)] at h
  exact h

/-! ## Copying a term into the register (tapes 0 the source, 1 the register) -/

def t2S : Fin 1 → Fin 2 := ![0]

theorem install_t2S (A : Fin 2 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install t2S A v = ![v 0, A 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t2S (H : Fin 2 → ℕ) (v : Fin 1 → ℕ) :
    dockH t2S H v = ![v 0, H 1] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

/-- A term copied: its coefficient frame, past the frame's end, its factor records, its terminator. -/
noncomputable def termCopyM :=
  Composition.machine (Composition.machine (Composition.machine CopyO.machine (RecoveryFocus.machine t2S nudgeM))
    (FacCopy.machine true)) CopyCell.machine

def termCopyCost (a : ℤ × List (List (List ℕ))) : ℕ :=
  2 * (decide (a.1 < 0) :: Nat.bits a.1.natAbs).length + 1 + 1 + 1 + 1 + ((facRecs a.2).length + 1) + 1 + 1

theorem termCopy_run (a : ℤ × List (List (List ℕ))) (pre tail o B : List Bool) :
    Step termCopyM (termCopyCost a) ![pre.length, o.length] ![pre ++ termWord a ++ tail, overlay o B]
      ![pre.length + (termWord a).length, (o ++ termWord a).length]
      ![pre ++ termWord a ++ tail, overlay (o ++ termWord a) B] := by
  set w := decide (a.1 < 0) :: Nat.bits a.1.natAbs
  set S := pre ++ termWord a ++ tail
  have eC : coefWord a.1 = frame w := rfl
  have eS : S = pre ++ frame w ++ (facRecs a.2 ++ false :: tail) := by
    simp [S, termWord_eq, eC, List.append_assoc]
  -- 1: the coefficient frame
  obtain ⟨cr, hcr, hcrf⟩ := CopyO.copy_run pre w (facRecs a.2 ++ false :: tail) o B
  rw [← eS] at hcr hcrf
  have h1 : Step CopyO.machine (2 * w.length + 1) ![pre.length, o.length] ![S, overlay o B]
      ![pre.length + 2 * w.length, (o ++ frame w).length] ![S, overlay (o ++ frame w) B] := by
    refine ⟨cr, hcr, ?_, ?_, runFrom_steps_le _ _ _ _ hcr⟩
    · rw [hcrf]; funext j; fin_cases j <;> rfl
    · rw [hcrf]; funext j; fin_cases j <;> rfl
  -- 2: past the frame's end
  have h2 := dockRun (nudge_run S (pre.length + 2 * w.length)) t2S (by decide)
    ![pre.length + 2 * w.length, (o ++ frame w).length] ![S, overlay (o ++ frame w) B]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_t2S, install_t2S] at h2
  -- 3: the factor records
  have h3 := FacCopy.run true (pre ++ frame w) a.2 tail (o ++ frame w) B
  have eS3 : pre ++ frame w ++ facRecs a.2 ++ false :: tail = S := by rw [eS]; simp
  rw [eS3] at h3
  simp only [owC, if_true] at h3
  have ep3 : (pre ++ frame w).length = pre.length + 2 * w.length + 1 := by simp [frame_length]; omega
  rw [ep3] at h3
  -- 4: the terminator
  have hr4 : readTapeBit S (pre.length + 2 * w.length + 1 + (facRecs a.2).length) = false := by
    rw [eS, show pre.length + 2 * w.length + 1 + (facRecs a.2).length = (pre ++ frame w ++ facRecs a.2).length by
      simp [frame_length]; omega]
    simpa [List.append_assoc] using Streaming.read_append (pre ++ frame w ++ facRecs a.2) tail false
  have h4 := CopyCell.run S (pre.length + 2 * w.length + 1 + (facRecs a.2).length) (o ++ frame w ++ facRecs a.2) B
  rw [hr4] at h4
  have hall := ((h1.seq (h2.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq h3).seq h4
  have eW : o ++ frame w ++ facRecs a.2 ++ [false] = o ++ termWord a := by
    rw [termWord_eq, eC]; simp
  unfold termCopyCost
  refine hall.congr ?_ ?_
  · funext j; fin_cases j
    · show pre.length + 2 * w.length + 1 + (facRecs a.2).length + 1 = pre.length + (termWord a).length
      rw [termWord_eq, eC]; simp [frame_length]; omega
    · show (o ++ frame w ++ facRecs a.2).length + 1 = (o ++ termWord a).length
      rw [← eW]; simp; omega
  · funext j; fin_cases j
    · rfl
    · show overlay (o ++ frame w ++ facRecs a.2 ++ [false]) B = overlay (o ++ termWord a) B
      rw [eW]

/-! ## The outer loop: every left term (tapes 0 the left expression, 1 the right expression, 2 the output, 3 the
register, 4 and 5 rewind logs) -/

def o6A : Fin 1 → Fin 6 := ![0]

theorem install_o6A (A : Fin 6 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install o6A A v = ![v 0, A 1, A 2, A 3, A 4, A 5] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_o6A (H : Fin 6 → ℕ) (v : Fin 1 → ℕ) :
    dockH o6A H v = ![v 0, H 1, H 2, H 3, H 4, H 5] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def o6T : Fin 3 → Fin 6 := ![0, 3, 5]

theorem install_o6T (A : Fin 6 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install o6T A v = ![v 0, A 1, A 2, v 1, A 4, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_o6T (H : Fin 6 → ℕ) (v : Fin 3 → ℕ) :
    dockH o6T H v = ![v 0, H 1, H 2, v 1, H 4, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def o6I : Fin 5 → Fin 6 := ![3, 1, 2, 5, 4]

theorem install_o6I (A : Fin 6 → List Bool) (v : Fin 5 → List Bool) :
    RecoveryRootRound.install o6I A v = ![A 0, v 1, v 2, v 0, v 4, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_o6I (H : Fin 6 → ℕ) (v : Fin 5 → ℕ) :
    dockH o6I H v = ![H 0, v 1, v 2, v 0, v 4, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_other _ _ _ _ (by decide)

def o6C : Fin 1 → Fin 6 := ![2]

theorem install_o6C (A : Fin 6 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install o6C A v = ![A 0, A 1, v 0, A 3, A 4, A 5] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_o6C (H : Fin 6 → ℕ) (v : Fin 1 → ℕ) :
    dockH o6C H v = ![H 0, H 1, v 0, H 3, H 4, H 5] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def selReg : Fin 2 → Bool := ![false, true]
def selB : Fin 4 → Bool := ![false, true, false, false]

/-- One left term: past its marker, into the register (rewound), times every right term (the right head rewound). -/
noncomputable def outerBody :=
  Composition.machine (Composition.machine (RecoveryFocus.machine o6A nudgeM)
    (RecoveryFocus.machine o6T (MaskedReset.machine termCopyM selReg)))
    (RecoveryFocus.machine o6I (MaskedReset.machine innerLoopM selB))

noncomputable def outerLoopM := StreamController.machine outerBody 0

/-- Cost bounds, uniform over the terms. -/
def tcBound (V : List (ℤ × List (List (List ℕ)))) : ℕ := (exprWord V).length + 5
def ibound (V W : List (ℤ × List (List (List ℕ)))) : ℕ := (exprWord V).length + (exprWord W).length + 6
def ilBound (V W : List (ℤ × List (List (List ℕ)))) : ℕ := W.length * (2 * ibound V W + 2 + 2) + 1
def mOuterCost (V W : List (ℤ × List (List (List ℕ)))) : ℕ := 1 + 1 + (2 * tcBound V + 2) + 1 + (2 * ilBound V W + 2)

theorem termCopyCost_le (V : List (ℤ × List (List (List ℕ)))) (a : ℤ × List (List (List ℕ))) (ha : a ∈ V) :
    termCopyCost a ≤ tcBound V := by
  have h := termWord_le_exprWord V a ha
  have e : (termWord a).length = 2 * (decide (a.1 < 0) :: Nat.bits a.1.natAbs).length + 1 + (facRecs a.2).length + 1 := by
    rw [termWord_eq]; simp [coefWord, frame_length]; omega
  unfold termCopyCost tcBound
  omega

theorem innerBound_le (V W : List (ℤ × List (List (List ℕ)))) (a : ℤ × List (List (List ℕ))) (ha : a ∈ V) :
    innerBound a W ≤ ibound V W := by
  have h := termWord_le_exprWord V a ha
  unfold innerBound ibound
  omega

/-- The register after the first `i` left terms. -/
def mRegAt (V : List (ℤ × List (List (List ℕ)))) (AT0 : List Bool) (i : ℕ) : List Bool :=
  (V.take i).foldl (fun R a => overlay (termWord a) R) AT0

/-- The product records of the first `i` left terms. -/
def outsAll (V W : List (ℤ × List (List (List ℕ)))) (i : ℕ) : List Bool :=
  (V.take i).flatMap fun a => outs a W W.length

def mOuterH (V W : List (ℤ × List (List (List ℕ)))) (o : List Bool) (i : ℕ) : Fin 6 → ℕ :=
  ![((V.take i).flatMap recT).length, 0, (o ++ outsAll V W i).length, 0, 0, 0]

def mOuterA (V W : List (ℤ × List (List (List ℕ)))) (SA SB o BC AT0 : List Bool) (cI cT : ℕ) (i : ℕ) : Fin 6 → List Bool :=
  ![exprWord V ++ SA, exprWord W ++ SB, overlay (o ++ outsAll V W i) BC, mRegAt V AT0 i, List.replicate cI false,
    List.replicate cT false]

theorem outer_step (V W : List (ℤ × List (List (List ℕ)))) (hV : ∀ a ∈ V, a.1 ≠ 0) (hW : ∀ b ∈ W, b.1 = 1 ∨ b.1 = -1)
    (SA SB o BC AT0 : List Bool) (cI cT : ℕ) (hcT : tcBound V ≤ cT) (hcT' : ibound V W ≤ cT) (hcI : ilBound V W ≤ cI)
    (i : ℕ) (hi : i < V.length) :
    Step outerBody (mOuterCost V W) (mOuterH V W o i) (mOuterA V W SA SB o BC AT0 cI cT i)
      (mOuterH V W o (i + 1)) (mOuterA V W SA SB o BC AT0 cI cT (i + 1)) := by
  set a := V[i] with ha
  have haV : a ∈ V := List.getElem_mem hi
  set PA := (V.take i).flatMap recT
  set restA := (V.drop (i + 1)).flatMap recT ++ false :: SA
  set R := mRegAt V AT0 i
  set o' := o ++ outsAll V W i
  have eA : exprWord V ++ SA = PA ++ [true] ++ termWord a ++ restA := by
    rw [exprWord_split V SA i hi]; simp only [recT, PA, restA, List.append_assoc, List.cons_append, List.nil_append, ha]
  -- 1: past the marker
  have s1 := dockRun (nudge_run (exprWord V ++ SA) PA.length) o6A (by decide) (mOuterH V W o i)
    (mOuterA V W SA SB o BC AT0 cI cT i) (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_o6A, install_o6A] at s1
  -- 2: the left term into the register
  have hc := termCopy_run a (PA ++ [true]) restA [] R
  rw [← eA] at hc
  have hc0 : Step termCopyM (termCopyCost a) ![PA.length + 1, 0] ![exprWord V ++ SA, R]
      ![PA.length + 1 + (termWord a).length, (termWord a).length] ![exprWord V ++ SA, overlay (termWord a) R] := by
    refine (hc.congr_in ?_ rfl).congr ?_ rfl
    · funext j; fin_cases j <;> simp
    · funext j; fin_cases j <;> simp
  have hc' := (hc0.enlarge (termCopyCost_le V a haV)).mask (cap := cT) selReg
    (by intro j hj; fin_cases j <;> first | rfl | simp [selReg] at hj) hcT
  have hc'' : Step (MaskedReset.machine termCopyM selReg) (2 * tcBound V + 2) ![PA.length + 1, 0, 0]
      ![exprWord V ++ SA, R, List.replicate cT false] ![PA.length + 1 + (termWord a).length, 0, 0]
      ![exprWord V ++ SA, overlay (termWord a) R, List.replicate cT false] := by
    refine (hc'.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
  have s2 := dockRun hc'' o6T (by decide)
    ![PA.length + 1, 0, o'.length, 0, 0, 0] ![exprWord V ++ SA, exprWord W ++ SB, overlay o' BC, R,
      List.replicate cI false, List.replicate cT false] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_o6T, install_o6T] at s2
  -- 3: times every right term
  have hl := innerLoop_run a W (hV a haV) hW SB o' BC (R.drop (termWord a).length) cT
    (le_trans (innerBound_le V W a haV) hcT')
  have hl0 : Step innerLoopM (W.length * (2 * innerBound a W + 2 + 2) + 1) ![0, 0, o'.length, 0]
      ![overlay (termWord a) R, exprWord W ++ SB, overlay o' BC, List.replicate cT false]
      ![0, (W.flatMap recT).length, (o' ++ outs a W W.length).length, 0]
      ![overlay (termWord a) R, exprWord W ++ SB, overlay (o' ++ outs a W W.length) BC, List.replicate cT false] := by
    refine (hl.congr_in ?_ ?_).congr ?_ ?_
    · funext j; fin_cases j <;> simp [mInnerH, outs]
    · funext j; fin_cases j <;> simp [mInnerA, outs, overlay]
    · funext j; fin_cases j <;> simp [mInnerH]
    · funext j; fin_cases j <;> simp [mInnerA, overlay]
  have hl' := (hl0.enlarge (show W.length * (2 * innerBound a W + 2 + 2) + 1 ≤ ilBound V W by
    unfold ilBound
    have := innerBound_le V W a haV
    have : 2 * innerBound a W + 2 + 2 ≤ 2 * ibound V W + 2 + 2 := by omega
    have := Nat.mul_le_mul_left W.length this
    omega)).mask (cap := cI) selB (by intro j hj; fin_cases j <;> first | rfl | simp [selB] at hj) hcI
  have hl'' : Step (MaskedReset.machine innerLoopM selB) (2 * ilBound V W + 2) ![0, 0, o'.length, 0, 0]
      ![overlay (termWord a) R, exprWord W ++ SB, overlay o' BC, List.replicate cT false, List.replicate cI false]
      ![0, 0, (o' ++ outs a W W.length).length, 0, 0]
      ![overlay (termWord a) R, exprWord W ++ SB, overlay (o' ++ outs a W W.length) BC, List.replicate cT false,
        List.replicate cI false] := by
    refine (hl'.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
  have s3 := dockRun hl'' o6I (by decide)
    ![PA.length + 1 + (termWord a).length, 0, o'.length, 0, 0, 0] ![exprWord V ++ SA, exprWord W ++ SB, overlay o' BC,
      overlay (termWord a) R, List.replicate cI false, List.replicate cT false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_o6I, install_o6I] at s3
  have hall := ((s1.congr (hout' := ![PA.length + 1, 0, o'.length, 0, 0, 0])
      (tout' := ![exprWord V ++ SA, exprWord W ++ SB, overlay o' BC, R, List.replicate cI false,
        List.replicate cT false]) (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).seq
    (s2.congr (hout' := ![PA.length + 1 + (termWord a).length, 0, o'.length, 0, 0, 0])
      (tout' := ![exprWord V ++ SA, exprWord W ++ SB, overlay o' BC, overlay (termWord a) R, List.replicate cI false,
        List.replicate cT false]) (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq s3
  have eP : PA.length + 1 + (termWord a).length = ((V.take (i + 1)).flatMap recT).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.flatMap_append, ← ha]; simp [recT, PA]
    omega
  have eO : o' ++ outs a W W.length = o ++ outsAll V W (i + 1) := by
    unfold outsAll
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.flatMap_append, ← ha]
    simp [o', outsAll]
  have eR : overlay (termWord a) R = mRegAt V AT0 (i + 1) := by
    unfold mRegAt
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]; rfl
  unfold mOuterCost
  refine hall.congr ?_ ?_
  · funext j; fin_cases j
    · exact eP
    · rfl
    · show (o' ++ outs a W W.length).length = _
      rw [eO]; rfl
    · rfl
    · rfl
    · rfl
  · funext j; fin_cases j
    · rfl
    · rfl
    · show overlay (o' ++ outs a W W.length) BC = _
      rw [eO]; rfl
    · exact eR
    · rfl
    · rfl

/-- **The outer loop**: every left term times every right term. -/
theorem outerLoop_run (V W : List (ℤ × List (List (List ℕ)))) (hV : ∀ a ∈ V, a.1 ≠ 0)
    (hW : ∀ b ∈ W, b.1 = 1 ∨ b.1 = -1) (SA SB o BC AT0 : List Bool) (cI cT : ℕ) (hcT : tcBound V ≤ cT)
    (hcT' : ibound V W ≤ cT) (hcI : ilBound V W ≤ cI) :
    Step outerLoopM (V.length * (mOuterCost V W + 2) + 1) (mOuterH V W o 0) (mOuterA V W SA SB o BC AT0 cI cT 0)
      (mOuterH V W o V.length) (mOuterA V W SA SB o BC AT0 cI cT V.length) := by
  let L : WhileBody 6 _ :=
    { body := outerBody
      tape := 0
      bound := V.length
      H := mOuterH V W o
      A := mOuterA V W SA SB o BC AT0 cI cT
      cost := fun _ => mOuterCost V W
      step := fun i hi => outer_step V W hV hW SA SB o BC AT0 cI cT hcT hcT' hcI i hi
      cont := fun i hi => by
        show readTapeBit (exprWord V ++ SA) ((V.take i).flatMap recT).length = true
        rw [exprWord_read V SA i (by omega)]; simpa using hi
      halt := by
        show readTapeBit (exprWord V ++ SA) ((V.take V.length).flatMap recT).length = false
        rw [exprWord_read V SA V.length (le_refl _)]; simp }
  have h := L.run
  rw [L.rest_const (mOuterCost V W) (fun _ => rfl)] at h
  exact h

/-! ## The product -/

/-- Write `false` under the head, without moving. -/
def putF : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => some false, fun _ => .stay⟩ else none

theorem putF_run (X B : List Bool) : Step putF 1 ![X.length] ![overlay X B] ![X.length] ![overlay (X ++ [false]) B] := by
  have hs : step putF ⟨putF.start, ![X.length], ![overlay X B]⟩ = some ⟨1, ![X.length], ![overlay (X ++ [false]) B]⟩ := by
    simp [step, putF]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction, overlay_write]
  obtain ⟨r, hr, hf, hs'⟩ := (Timed.single (p := putF) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

def selAC : Fin 6 → Bool := ![true, false, true, false, false, false]

/-- **The product machine**: every left term times every right term, the expression's terminator, the left and output
heads rewound. -/
noncomputable def exprMulM :=
  MaskedReset.machine (Composition.machine outerLoopM (RecoveryFocus.machine o6C putF)) selAC

def mulCost (V W : List (ℤ × List (List (List ℕ)))) : ℕ := 2 * (V.length * (mOuterCost V W + 2) + 1 + 1 + 1) + 2

theorem smul_flatMap (V W : List (ℤ × List (List (List ℕ)))) :
    (smul V W).flatMap recT = outsAll V W V.length := by
  unfold smul outsAll outs
  simp only [List.take_length, List.flatMap_assoc]
  refine List.flatMap_congr fun a _ => ?_
  rw [List.flatMap_map]
  rfl

theorem exprWord_smul (V W : List (ℤ × List (List (List ℕ)))) :
    exprWord (smul V W) = outsAll V W V.length ++ [false] := by
  rw [exprWord_eq, smul_flatMap]

/-- The product's coefficients are nonzero when the left ones are and the right ones are units. -/
theorem smul_ne_zero (V W : List (ℤ × List (List (List ℕ)))) (hV : ∀ a ∈ V, a.1 ≠ 0)
    (hW : ∀ b ∈ W, b.1 = 1 ∨ b.1 = -1) : ∀ t ∈ smul V W, t.1 ≠ 0 := by
  intro t ht
  unfold smul at ht
  obtain ⟨a, ha, hat⟩ := List.mem_flatMap.mp ht
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hat
  rcases hW b hb with h | h <;> simp [h, hV a ha]

/-- **The product of two printed expressions** (unit coefficients on the right): from every head at cell 0, the output
tape ends as `exprWord (smul V W)` over its old content, every head back at cell 0. -/
theorem exprMul_run (V W : List (ℤ × List (List (List ℕ)))) (hV : ∀ a ∈ V, a.1 ≠ 0)
    (hW : ∀ b ∈ W, b.1 = 1 ∨ b.1 = -1) (SA SB BC AT0 : List Bool) (cI cT cA : ℕ) (hcT : tcBound V ≤ cT)
    (hcT' : ibound V W ≤ cT) (hcI : ilBound V W ≤ cI) (hcA : V.length * (mOuterCost V W + 2) + 1 + 1 + 1 ≤ cA) :
    Step exprMulM (mulCost V W) (fun _ => 0)
      ![exprWord V ++ SA, exprWord W ++ SB, BC, AT0, List.replicate cI false, List.replicate cT false,
        List.replicate cA false]
      (fun _ => 0)
      ![exprWord V ++ SA, exprWord W ++ SB, overlay (exprWord (smul V W)) BC, mRegAt V AT0 V.length,
        List.replicate cI false, List.replicate cT false, List.replicate cA false] := by
  have hl := outerLoop_run V W hV hW SA SB [] BC AT0 cI cT hcT hcT' hcI
  set O := outsAll V W V.length
  have hp := dockRun (putF_run O BC) o6C (by decide) (mOuterH V W [] V.length)
    (mOuterA V W SA SB [] BC AT0 cI cT V.length) (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_o6C, install_o6C] at hp
  have hs := hl.seq hp
  have hm := hs.mask (cap := cA) selAC (by intro j _; fin_cases j <;> rfl) hcA
  unfold mulCost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j
    · rfl
    · rfl
    · show overlay (O ++ [false]) BC = overlay (exprWord (smul V W)) BC
      rw [exprWord_smul]
    · rfl
    · rfl
    · rfl
    · rfl

/-- **The product's port**: after `exprMulM`, the output tape holds `exprWord (smul V W)` over its old content. -/
theorem exprMul_ports (V W : List (ℤ × List (List (List ℕ)))) (hV : ∀ a ∈ V, a.1 ≠ 0)
    (hW : ∀ b ∈ W, b.1 = 1 ∨ b.1 = -1) (SA SB BC AT0 : List Bool) (cI cT cA : ℕ) (hcT : tcBound V ≤ cT)
    (hcT' : ibound V W ≤ cT) (hcI : ilBound V W ≤ cI) (hcA : V.length * (mOuterCost V W + 2) + 1 + 1 + 1 ≤ cA) :
    ∃ A' : Fin 7 → List Bool, Step exprMulM (mulCost V W) (fun _ => 0)
      ![exprWord V ++ SA, exprWord W ++ SB, BC, AT0, List.replicate cI false, List.replicate cT false,
        List.replicate cA false] (fun _ => 0) A' ∧
      A' 2 = overlay (exprWord (smul V W)) BC := by
  exact ⟨_, exprMul_run V W hV hW SA SB BC AT0 cI cT cA hcT hcT' hcI hcA, rfl⟩

end NearCubicWires.WireExponent3_5.SeedFix
