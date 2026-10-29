import Proof.Gates.ENP.TableCircuit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.ENP.TCirc

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.SourceInterfaces NearCubicGates.Close.Outer

variable {ℓ : ℕ}

/-! ## Folding node lists -/

/-- Fold a node list onto an array of values. -/
def ev (r : BitInput (T ℓ)) (ds : List (BooleanNode (T ℓ))) (V : Array Bool) : Array Bool :=
  ds.foldl (pushEval r) V

theorem ev_append (r : BitInput (T ℓ)) (ds es : List (BooleanNode (T ℓ))) (V : Array Bool) :
    ev r (ds ++ es) V = ev r es (ev r ds V) := by
  simp [ev, List.foldl_append]

theorem ev_size (r : BitInput (T ℓ)) (ds : List (BooleanNode (T ℓ))) (V : Array Bool) :
    (ev r ds V).size = V.size + ds.length := foldl_pushEval_size r ds V

theorem ev_prefix (r : BitInput (T ℓ)) (ds : List (BooleanNode (T ℓ))) (V : Array Bool) (p : ℕ)
    (hp : p < V.size) : (ev r ds V)[p]? = V[p]? := foldl_pushEval_prefix r ds V p hp

theorem ev_single (r : BitInput (T ℓ)) (nd : BooleanNode (T ℓ)) (V : Array Bool) :
    ev r [nd] V = V.push (nd.eval r V) := rfl

theorem push_last (V : Array Bool) (b : Bool) : (V.push b)[V.size]? = some b := by simp

theorem push_prefix (V : Array Bool) (b : Bool) (p : ℕ) (hp : p < V.size) : (V.push b)[p]? = V[p]? := by
  simp [Array.getElem?_push, show p ≠ V.size by omega]

/-- A value known at index `p`. -/
def Has (V : Array Bool) (p : ℕ) (b : Bool) : Prop := V[p]? = some b

theorem Has.read {V : Array Bool} {p : ℕ} {b : Bool} (h : Has V p b) : V[p]?.getD false = b := by
  rw [h]; rfl

theorem Has.lt {V : Array Bool} {p : ℕ} {b : Bool} (h : Has V p b) : p < V.size := by
  by_contra hc
  unfold Has at h
  rw [Array.getElem?_eq_none (by omega)] at h
  cases h

theorem Has.ev {V : Array Bool} {p : ℕ} {b : Bool} (h : Has V p b) (r : BitInput (T ℓ))
    (ds : List (BooleanNode (T ℓ))) : Has (ev r ds V) p b := by
  unfold Has
  rw [ev_prefix r ds V p h.lt]
  exact h

theorem Has.push {V : Array Bool} {p : ℕ} {b : Bool} (h : Has V p b) (c : Bool) : Has (V.push c) p b := by
  unfold Has
  rw [push_prefix V c p h.lt]
  exact h

/-! ## The multiplexer -/

/-- The table bit at a numeric address. -/
def tget (t : BitInput (T ℓ)) (a : ℕ) : Bool := if h : a < T ℓ then t ⟨a, h⟩ else false

/-- `[addr = bin(a)]` on the first `k` address bits. -/
def matchK (addr : ℕ → Bool) (a k : ℕ) : Bool := (List.range k).all (fun j => addr j == a.testBit j)

theorem matchK_succ (addr : ℕ → Bool) (a k : ℕ) :
    matchK addr a (k + 1) = (matchK addr a k && (addr k == a.testBit k)) := by
  simp [matchK, List.range_succ, List.all_append]

theorem lit_eval (r : BitInput (T ℓ)) (V : Array Bool) (b : Bool) (w : ℕ) (x : Bool) (hw : Has V w x) :
    (lit b w : BooleanNode (T ℓ)).eval r V = (x == b) := by
  unfold lit
  cases b <;> simp [BooleanNode.eval, hw.read]

variable (C : OracleCircuit ℓ ℓ)

/-- **One multiplexer group.** -/
theorem group_ev (r : BitInput (T ℓ)) (z c : ℕ) (args : Fin ℓ → ℕ) (a : ℕ) (ha : a < T ℓ) (V : Array Bool)
    (addr : ℕ → Bool) (ob : Bool)
    (hsize : V.size = gs C z c a) (hin : Has V (1 + a) (r ⟨a, ha⟩))
    (haddr : ∀ j (hj : j < ℓ), Has V (img C z (args ⟨j, hj⟩)) (addr j))
    (hO : Has V (oPrev C z c a) ob) :
    (ev r (group C z c args a) V).size = V.size + (2 * ℓ + 1) ∧
      Has (ev r (group C z c args a) V) (gs C z c a + 2 * ℓ) (ob || (r ⟨a, ha⟩ && matchK addr a ℓ)) := by
  -- the pairs
  have pairs : ∀ k ≤ ℓ,
      (ev r ((List.range k).flatMap (fun j =>
        [lit (a.testBit j) (img C z (if h : j < ℓ then args ⟨j, h⟩ else 0)),
          (.and (gIdx C z c a j) (gs C z c a + 2 * j) : BooleanNode (T ℓ))])) V).size = V.size + 2 * k ∧
      Has (ev r ((List.range k).flatMap (fun j =>
        [lit (a.testBit j) (img C z (if h : j < ℓ then args ⟨j, h⟩ else 0)),
          (.and (gIdx C z c a j) (gs C z c a + 2 * j) : BooleanNode (T ℓ))])) V) (gIdx C z c a k)
        (r ⟨a, ha⟩ && matchK addr a k) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨by simp [ev], ?_⟩
      simp only [List.range_zero, List.flatMap_nil, gIdx, if_pos]
      simpa [matchK, ev] using hin
    | succ k ih =>
      intro hk
      obtain ⟨hs, hg⟩ := ih (by omega)
      rw [List.range_succ, List.flatMap_append, ev_append]
      set W := ev r ((List.range k).flatMap (fun j =>
        [lit (a.testBit j) (img C z (if h : j < ℓ then args ⟨j, h⟩ else 0)),
          (.and (gIdx C z c a j) (gs C z c a + 2 * j) : BooleanNode (T ℓ))])) V with hW
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hkl : k < ℓ := by omega
      have hw : Has W (img C z (if h : k < ℓ then args ⟨k, h⟩ else 0)) (addr k) := by
        rw [dif_pos hkl]; exact (haddr k hkl).ev r _
      have hL := lit_eval r W (a.testBit k) _ (addr k) hw
      rw [show [lit (a.testBit k) (img C z (if h : k < ℓ then args ⟨k, h⟩ else 0)),
          (.and (gIdx C z c a k) (gs C z c a + 2 * k) : BooleanNode (T ℓ))] =
          [lit (a.testBit k) (img C z (if h : k < ℓ then args ⟨k, h⟩ else 0))] ++
          [(.and (gIdx C z c a k) (gs C z c a + 2 * k) : BooleanNode (T ℓ))] from rfl, ev_append, ev_single,
        ev_single]
      set W1 := W.push ((lit (a.testBit k) (img C z (if h : k < ℓ then args ⟨k, h⟩ else 0)) :
        BooleanNode (T ℓ)).eval r W) with hW1
      have hW1L : Has W1 (gs C z c a + 2 * k) (addr k == a.testBit k) := by
        unfold Has; rw [hW1, show gs C z c a + 2 * k = W.size by omega, push_last, hL]
      have hW1G : Has W1 (gIdx C z c a k) (r ⟨a, ha⟩ && matchK addr a k) := hg.push _
      have hW1s : W1.size = W.size + 1 := by rw [hW1]; simp
      refine ⟨by simp only [Array.size_push]; rw [hW1s, hs]; omega, ?_⟩
      have hidx : gIdx C z c a (k + 1) = W1.size := by
        unfold gIdx
        rw [if_neg (by omega), hW1s, hs, hsize]
        omega
      unfold Has
      rw [hidx, push_last]
      simp only [BooleanNode.eval, hW1L.read, hW1G.read, matchK_succ, Bool.and_assoc]
  obtain ⟨hs, hg⟩ := pairs ℓ le_rfl
  unfold group
  rw [ev_append, ev_single]
  set W := ev r ((List.range ℓ).flatMap (fun j =>
      [lit (a.testBit j) (img C z (if h : j < ℓ then args ⟨j, h⟩ else 0)),
        (.and (gIdx C z c a j) (gs C z c a + 2 * j) : BooleanNode (T ℓ))])) V with hW
  refine ⟨by simp [hs]; omega, ?_⟩
  have hOW : Has W (oPrev C z c a) ob := hO.ev r _
  unfold Has
  rw [show gs C z c a + 2 * ℓ = W.size by omega, push_last]
  simp only [BooleanNode.eval, hOW.read, hg.read]

/-- The running disjunction after `a` groups. -/
def anyUpTo (r : BitInput (T ℓ)) (addr : ℕ → Bool) (a : ℕ) : Bool :=
  (List.range a).any (fun a' => tget r a' && matchK addr a' ℓ)

/-- **The multiplexer block of an oracle gate.** -/
theorem oracleBlock_ev (r : BitInput (T ℓ)) (z c : ℕ) (args : Fin ℓ → ℕ) (V : Array Bool) (addr : ℕ → Bool)
    (hsize : V.size = bs C z c) (hz : Has V 0 false) (hin : ∀ a (ha : a < T ℓ), Has V (1 + a) (r ⟨a, ha⟩))
    (haddr : ∀ j (hj : j < ℓ), Has V (img C z (args ⟨j, hj⟩)) (addr j)) :
    (ev r ((List.range (T ℓ)).flatMap (group C z c args)) V).size = V.size + K ℓ ∧
      Has (ev r ((List.range (T ℓ)).flatMap (group C z c args)) V) (img C z c) (anyUpTo r addr (T ℓ)) := by
  have step : ∀ a ≤ T ℓ, (ev r ((List.range a).flatMap (group C z c args)) V).size = V.size + a * (2 * ℓ + 1) ∧
      Has (ev r ((List.range a).flatMap (group C z c args)) V) (oPrev C z c a) (anyUpTo r addr a) := by
    intro a
    induction a with
    | zero =>
      intro _
      refine ⟨by simp [ev], ?_⟩
      simpa [oPrev, anyUpTo, ev] using hz
    | succ a ih =>
      intro ha
      obtain ⟨hs, ho⟩ := ih (by omega)
      rw [List.range_succ, List.flatMap_append, ev_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hg := group_ev C r z c args a (by omega) _ addr (anyUpTo r addr a) (by rw [hs, hsize])
        ((hin a (by omega)).ev r _) (fun j hj => (haddr j hj).ev r _) ho
      refine ⟨by rw [hg.1, hs]; ring, ?_⟩
      have hidx : oPrev C z c (a + 1) = gs C z c a + 2 * ℓ := by
        unfold oPrev; rw [if_neg (by omega)]; unfold gs; rw [Nat.succ_mul]; omega
      rw [hidx]
      have hany : anyUpTo r addr (a + 1) = (anyUpTo r addr a || (r ⟨a, by omega⟩ && matchK addr a ℓ)) := by
        simp [anyUpTo, List.range_succ, List.any_append, tget, show a < T ℓ by omega]
      rw [hany]
      exact hg.2
  obtain ⟨hs, ho⟩ := step (T ℓ) le_rfl
  refine ⟨by rw [hs], ?_⟩
  have hidx : img C z c = oPrev C z c (T ℓ) := by
    have hT : T ℓ ≠ 0 := by positivity
    unfold oPrev img gs bs K; rw [if_neg hT]
    have : 1 ≤ T ℓ * (2 * ℓ + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  rw [hidx]
  exact ho

/-- The bits of a numeric address below `2^ℓ`. -/
theorem binaryAddress_val_testBit (bits : BitInput ℓ) (j : Fin ℓ) : (binaryAddress bits).val.testBit j.val = bits j := by
  have hlt : encodeBitInput bits < 2 ^ ℓ := by rw [encodeBitInput_eq_ofBits]; exact Nat.ofBits_lt_two_pow bits
  have hb : (fun j : Fin ℓ => (encodeBitInput bits).testBit j.val) = bits := by
    funext j; rw [encodeBitInput_eq_ofBits]; exact Nat.testBit_ofBits_lt bits j.val j.isLt
  have h := binaryAddress_testBit (width := ℓ) hlt
  rw [hb] at h
  rw [h]
  exact congrFun hb j

theorem matchK_iff (addr : ℕ → Bool) (a : ℕ) (ha : a < T ℓ) :
    matchK addr a ℓ = true ↔ a = (binaryAddress (fun j : Fin ℓ => addr j.val)).val := by
  set a0 := (binaryAddress (fun j : Fin ℓ => addr j.val)).val with ha0
  have h0 : ∀ j (hj : j < ℓ), a0.testBit j = addr j := fun j hj =>
    binaryAddress_val_testBit (fun j : Fin ℓ => addr j.val) ⟨j, hj⟩
  have ha0lt : a0 < T ℓ := (binaryAddress _).isLt
  unfold matchK
  rw [List.all_eq_true]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < ℓ
    · have := h j (List.mem_range.mpr hj)
      rw [beq_iff_eq] at this
      rw [← this, h0 j hj]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha0lt (Nat.pow_le_pow_right (by decide) (by omega)))]
  · rintro rfl j hj
    rw [beq_iff_eq, h0 j (List.mem_range.mp hj)]

/-- **The multiplexer value**: the table at the address. -/
theorem anyUpTo_eq (r : BitInput (T ℓ)) (addr : ℕ → Bool) :
    anyUpTo r addr (T ℓ) = r (binaryAddress (fun j : Fin ℓ => addr j.val)) := by
  set a0 := binaryAddress (fun j : Fin ℓ => addr j.val) with ha0
  unfold anyUpTo
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, ha, h⟩
    have hal := List.mem_range.mp ha
    rw [Bool.and_eq_true] at h
    have he := (matchK_iff addr a hal).mp h.2
    have : a0 = ⟨a, hal⟩ := Fin.ext he.symm
    rw [this]
    simpa [tget, hal] using h.1
  · intro h
    refine ⟨a0.val, List.mem_range.mpr a0.isLt, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨by simpa [tget, a0.isLt] using h, (matchK_iff addr a0.val a0.isLt).mpr rfl⟩

/-! ## The values of `C` -/

/-- The seed `bin(z)`. -/
def seedIn (z : ℕ) : BitInput ℓ := fun i => z.testBit i.val

/-- The oracle given by the table `r` (address order). -/
def tOr (r : BitInput (T ℓ)) : BitInput ℓ → Bool := fun a => r (binaryAddress a)

/-- `C`'s node values at seed `z` with the table oracle. -/
def CV (r : BitInput (T ℓ)) (z : ℕ) : Array Bool := C.values (tOr r) (seedIn z)

/-- `C`'s value at node `c`. -/
def cv (r : BitInput (T ℓ)) (z c : ℕ) : Bool := (CV C r z)[c]?.getD false

theorem ofold_size (O : BitInput ℓ → Bool) (rC : BitInput ℓ) :
    ∀ (ds : List (OracleNode ℓ ℓ)) (P : Array Bool), (ds.foldl (oPush O rC) P).size = P.size + ds.length
  | [], P => by simp
  | d :: ds, P => by
      simp only [List.foldl_cons, List.length_cons]
      rw [ofold_size O rC ds]
      simp [oPush]
      omega

theorem ofold_prefix (O : BitInput ℓ → Bool) (rC : BitInput ℓ) :
    ∀ (ds : List (OracleNode ℓ ℓ)) (P : Array Bool) (p : ℕ), p < P.size → (ds.foldl (oPush O rC) P)[p]? = P[p]?
  | [], P, p, _ => by simp
  | d :: ds, P, p, hp => by
      simp only [List.foldl_cons]
      rw [ofold_prefix O rC ds _ p (by simp [oPush]; omega)]
      simp [oPush, Array.getElem?_push, show p ≠ P.size by omega]

theorem values_fold (O : BitInput ℓ → Bool) (rC : BitInput ℓ) :
    C.values O rC = C.nodes.foldl (oPush O rC) #[] := rfl

/-- The prefix of `C`'s values. -/
def pre (r : BitInput (T ℓ)) (z c : ℕ) : Array Bool := (C.nodes.take c).foldl (oPush (tOr r) (seedIn z)) #[]

theorem pre_size (r : BitInput (T ℓ)) (z c : ℕ) (hc : c ≤ C.nodes.length) : (pre C r z c).size = c := by
  unfold pre; rw [ofold_size]; simp; omega

theorem pre_agree (r : BitInput (T ℓ)) (z c : ℕ) (hc : c ≤ C.nodes.length) (p : ℕ) (hp : p < c) :
    (pre C r z c)[p]?.getD false = cv C r z p := by
  unfold cv CV
  rw [values_fold]
  conv_rhs => rw [← List.take_append_drop c C.nodes]
  rw [List.foldl_append, ofold_prefix _ _ _ _ p (by rw [ofold_size]; simp; omega)]
  rfl

theorem cv_node (r : BitInput (T ℓ)) (z c : ℕ) (hc : c < C.nodes.length) :
    cv C r z c = (C.nodes[c]).eval (tOr r) (seedIn z) (pre C r z c) := by
  unfold cv CV
  rw [values_fold]
  conv_lhs => rw [← List.take_append_drop c C.nodes]
  rw [List.foldl_append, List.drop_eq_getElem_cons hc, List.foldl_cons,
    ofold_prefix _ _ _ _ c (by simp [oPush]; rw [← pre, pre_size C r z c hc.le])]
  simp only [oPush]
  rw [show (List.take c C.nodes).foldl (oPush (tOr r) (seedIn z)) #[] = pre C r z c from rfl]
  rw [Array.getElem?_push, if_pos (by rw [pre_size C r z c hc.le])]
  rfl

theorem node_wf (c : ℕ) (hc : c < C.nodes.length) : (C.nodes[c]).WellFormedAt c := C.wellFormed ⟨c, hc⟩

/-! ## The other blocks -/

theorem ev_replicate (r : BitInput (T ℓ)) (k : ℕ) (V : Array Bool) :
    (ev r (List.replicate k (.const false)) V).size = V.size + k := by rw [ev_size]; simp

/-- **A non-oracle block**: its last node is the translation, evaluated after the fillers. -/
theorem plainBlock_ev (r : BitInput (T ℓ)) (z c : ℕ) (nd : OracleNode ℓ ℓ) (V : Array Bool)
    (hsize : V.size = bs C z c) (hnd : ∀ args, nd ≠ .oracle args) :
    (ev r (block C z c nd) V).size = V.size + K ℓ ∧
      Has (ev r (block C z c nd) V) (img C z c)
        ((translate C z nd).eval r (ev r (List.replicate (K ℓ - 1) (.const false)) V)) := by
  have hK : 1 ≤ K ℓ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hb : block C z c nd = List.replicate (K ℓ - 1) (.const false) ++ [translate C z nd] := by
    cases nd with
    | oracle args => exact absurd rfl (hnd args)
    | _ => rfl
  rw [hb, ev_append, ev_single]
  refine ⟨by simp [ev_replicate]; omega, ?_⟩
  unfold Has
  rw [show img C z c = (ev r (List.replicate (K ℓ - 1) (.const false)) V).size by
    rw [ev_replicate, hsize], push_last]

/-! ## One seed -/

/-- The start facts of a value array: zero wire, table inputs. -/
structure StartFacts (r : BitInput (T ℓ)) (V : Array Bool) : Prop where
  zero : Has V 0 false
  inp : ∀ a (ha : a < T ℓ), Has V (1 + a) (r ⟨a, ha⟩)

theorem StartFacts.ev {r : BitInput (T ℓ)} {V : Array Bool} (h : StartFacts r V) (ds : List (BooleanNode (T ℓ))) :
    StartFacts r (ev r ds V) := ⟨h.zero.ev r ds, fun a ha => (h.inp a ha).ev r ds⟩

/-- **The blocks of seed `z`**: the image of every node of `C` carries `C`'s value at seed `z`. -/
theorem blocks_ev (r : BitInput (T ℓ)) (z : ℕ) (V : Array Bool) (hsize : V.size = base C z)
    (hst : StartFacts r V) :
    ∀ c ≤ C.nodes.length,
      (ev r ((List.range c).flatMap (fun c => block C z c (C.nodes.getD c (.const false)))) V).size =
        V.size + c * K ℓ ∧
      ∀ c' < c, Has (ev r ((List.range c).flatMap (fun c => block C z c (C.nodes.getD c (.const false)))) V)
        (img C z c') (cv C r z c') := by
  intro c
  induction c with
  | zero => intro _; exact ⟨by simp [ev], fun c' h => absurd h (Nat.not_lt_zero _)⟩
  | succ c ih =>
    intro hc
    have hcm : c < C.nodes.length := by omega
    obtain ⟨hs, hv⟩ := ih (by omega)
    rw [List.range_succ, List.flatMap_append, ev_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    set W := ev r ((List.range c).flatMap (fun c => block C z c (C.nodes.getD c (.const false)))) V with hW
    have hWs : W.size = bs C z c := by rw [hs, hsize]
    have hWst : StartFacts r W := hst.ev _
    have hnd : C.nodes.getD c (.const false) = C.nodes[c] := by simp [List.getD_eq_getElem?_getD, hcm]
    have hwf := node_wf C c hcm
    have hval := cv_node C r z c hcm
    have hread : ∀ c' < c, (pre C r z c)[c']?.getD false = cv C r z c' := pre_agree C r z c hcm.le
    rw [hnd]
    -- the new block
    have key : (ev r (block C z c (C.nodes[c])) W).size = W.size + K ℓ ∧
        Has (ev r (block C z c (C.nodes[c])) W) (img C z c) (cv C r z c) := by
      generalize hN : C.nodes[c] = nd at hwf hval
      cases nd with
      | oracle args =>
        have hwf' : ∀ j, args j < c := hwf
        have hb := oracleBlock_ev C r z c args W (fun j => if h : j < ℓ then cv C r z (args ⟨j, h⟩) else false)
          hWs hWst.zero hWst.inp (fun j hj => by simpa [hj] using hv (args ⟨j, hj⟩) (hwf' _))
        refine ⟨hb.1, ?_⟩
        have he : anyUpTo r (fun j => if h : j < ℓ then cv C r z (args ⟨j, h⟩) else false) (T ℓ) = cv C r z c := by
          rw [anyUpTo_eq, hval]
          simp only [OracleNode.eval, tOr]
          congr 1
          congr 1
          funext j
          simp [j.isLt, hread _ (hwf' j)]
        rw [← he]
        exact hb.2
      | const b =>
        have hb := plainBlock_ev C r z c (.const b) W hWs (fun _ h => by cases h)
        refine ⟨hb.1, ?_⟩
        convert hb.2 using 1
        rw [hval]; rfl
      | input i =>
        have hb := plainBlock_ev C r z c (.input i) W hWs (fun _ h => by cases h)
        refine ⟨hb.1, ?_⟩
        convert hb.2 using 1
        rw [hval]; rfl
      | not c1 =>
        have hb := plainBlock_ev C r z c (.not c1) W hWs (fun _ h => by cases h)
        refine ⟨hb.1, ?_⟩
        convert hb.2 using 1
        have h1 := ((hv c1 hwf).ev r (List.replicate (K ℓ - 1) (.const false))).read
        rw [hval]
        simp only [translate, BooleanNode.eval, OracleNode.eval, h1, hread c1 hwf]
      | and c1 c2 =>
        have hb := plainBlock_ev C r z c (.and c1 c2) W hWs (fun _ h => by cases h)
        refine ⟨hb.1, ?_⟩
        convert hb.2 using 1
        have h1 := ((hv c1 hwf.1).ev r (List.replicate (K ℓ - 1) (.const false))).read
        have h2 := ((hv c2 hwf.2).ev r (List.replicate (K ℓ - 1) (.const false))).read
        rw [hval]
        simp only [translate, BooleanNode.eval, OracleNode.eval, h1, h2, hread c1 hwf.1, hread c2 hwf.2]
      | or c1 c2 =>
        have hb := plainBlock_ev C r z c (.or c1 c2) W hWs (fun _ h => by cases h)
        refine ⟨hb.1, ?_⟩
        convert hb.2 using 1
        have h1 := ((hv c1 hwf.1).ev r (List.replicate (K ℓ - 1) (.const false))).read
        have h2 := ((hv c2 hwf.2).ev r (List.replicate (K ℓ - 1) (.const false))).read
        rw [hval]
        simp only [translate, BooleanNode.eval, OracleNode.eval, h1, h2, hread c1 hwf.1, hread c2 hwf.2]
    refine ⟨by rw [key.1, hs]; ring, ?_⟩
    intro c' hc'
    by_cases he : c' = c
    · subst he; exact key.2
    · exact (hv c' (by omega)).ev r _

/-- `C(bin(z))` with the table oracle. -/
def Ceval (r : BitInput (T ℓ)) (z : ℕ) : Bool := C.eval (tOr r) (seedIn z)

theorem Ceval_eq (r : BitInput (T ℓ)) (z : ℕ) : Ceval C r z = cv C r z C.output.val := rfl

/-- The running conjunction after `z` seeds. -/
def allUpTo (r : BitInput (T ℓ)) (z : ℕ) : Bool := (List.range z).all (fun z' => !Ceval C r z')

/-- **One seed**: its blocks, `¬C(z)` and the running conjunction. -/
theorem seed_ev (r : BitInput (T ℓ)) (z : ℕ) (V : Array Bool) (hsize : V.size = base C z)
    (hst : StartFacts r V) (hprev : Has V (base C z - 1) (allUpTo C r z)) :
    (ev r (seed C z) V).size = V.size + L C ∧
      Has (ev r (seed C z) V) (base C (z + 1) - 1) (allUpTo C r (z + 1)) := by
  obtain ⟨hs, hv⟩ := blocks_ev C r z V hsize hst C.nodes.length le_rfl
  unfold seed
  rw [ev_append]
  set W := ev r ((List.range C.nodes.length).flatMap (fun c => block C z c (C.nodes.getD c (.const false)))) V
    with hW
  rw [show [(BooleanNode.not (img C z C.output.val) : BooleanNode (T ℓ)),
      .and (base C z - 1) (base C z + C.nodes.length * K ℓ)] =
      [(BooleanNode.not (img C z C.output.val) : BooleanNode (T ℓ))] ++
      [.and (base C z - 1) (base C z + C.nodes.length * K ℓ)] from rfl, ev_append, ev_single, ev_single]
  have hout := (hv C.output.val C.output.isLt)
  set W1 := W.push ((BooleanNode.not (img C z C.output.val) : BooleanNode (T ℓ)).eval r W) with hW1
  have hW1s : W1.size = W.size + 1 := by rw [hW1]; simp
  have hN : Has W1 (base C z + C.nodes.length * K ℓ) (!Ceval C r z) := by
    unfold Has
    rw [hW1, show base C z + C.nodes.length * K ℓ = W.size by rw [hs, hsize], push_last]
    simp [BooleanNode.eval, hout.read, Ceval_eq]
  have hP : Has W1 (base C z - 1) (allUpTo C r z) := (hprev.ev r _).push _
  refine ⟨by simp only [Array.size_push]; rw [hW1s, hs]; simp only [L]; ring, ?_⟩
  unfold Has
  rw [show base C (z + 1) - 1 = W1.size by
    simp only [base, L] at hs hsize ⊢; rw [hW1s, hs, hsize]; rw [Nat.succ_mul]; omega, push_last]
  simp only [BooleanNode.eval, hN.read, hP.read]
  simp [allUpTo, List.range_succ, List.all_append]

/-- The input nodes `0..k−1`. -/
def inputs (k : ℕ) : List (BooleanNode (T ℓ)) :=
  (List.range k).map (fun a => if h : a < T ℓ then .input ⟨a, h⟩ else .const false)

theorem ofFn_inputs : List.ofFn (fun a : Fin (T ℓ) => (.input a : BooleanNode (T ℓ))) = inputs (T ℓ) := by
  apply List.ext_getElem
  · simp [inputs]
  · intro i h1 h2
    simp [inputs, show i < T ℓ by simpa using h1]

theorem inputs_ev (r : BitInput (T ℓ)) (V : Array Bool) :
    ∀ k, (hk : k ≤ T ℓ) → (ev r (inputs k) V).size = V.size + k ∧
      ∀ a (ha : a < k), Has (ev r (inputs k) V) (V.size + a) (r ⟨a, by omega⟩) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨by simp [inputs, ev], fun a h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨hs, hv⟩ := ih (by omega)
    rw [inputs, List.range_succ, List.map_append, ← inputs, ev_append, List.map_cons, List.map_nil, ev_single]
    refine ⟨by simp [hs]; omega, ?_⟩
    intro a ha
    by_cases he : a = k
    · subst he
      unfold Has
      rw [show V.size + a = (ev r (inputs a) V).size by rw [hs], push_last]
      simp [BooleanNode.eval, show a < T ℓ by omega]
    · exact (hv a (by omega)).push _

theorem start_ev (r : BitInput (T ℓ)) :
    (ev r (start ℓ) #[]).size = S ℓ ∧ StartFacts r (ev r (start ℓ) #[]) ∧ Has (ev r (start ℓ) #[]) (S ℓ - 1) true := by
  unfold start
  rw [ofFn_inputs, ev_append, ev_append, ev_single]
  set V0 : Array Bool := (#[] : Array Bool).push ((BooleanNode.const false : BooleanNode (T ℓ)).eval r #[])
  have hV0 : V0.size = 1 := rfl
  obtain ⟨hs, hv⟩ := inputs_ev r V0 (T ℓ) le_rfl
  rw [ev_single]
  set V1 := ev r (inputs (T ℓ)) V0 with hV1
  refine ⟨by simp [hs, hV0]; omega, ⟨?_, ?_⟩, ?_⟩
  · exact (show Has V0 0 false from rfl).ev r _ |>.push _
  · intro a ha
    have := (hv a ha).push ((BooleanNode.const true : BooleanNode (T ℓ)).eval r V1)
    rw [hV0] at this
    exact this
  · unfold Has
    rw [show S ℓ - 1 = V1.size by simp only [S]; rw [hs, hV0]; omega, push_last]
    rfl

/-- **The fold over all seeds.** -/
theorem seeds_ev (r : BitInput (T ℓ)) :
    ∀ z ≤ T ℓ, (ev r ((List.range z).flatMap (seed C)) (ev r (start ℓ) #[])).size = base C z ∧
      Has (ev r ((List.range z).flatMap (seed C)) (ev r (start ℓ) #[])) (base C z - 1) (allUpTo C r z) := by
  obtain ⟨hs0, hst0, ht0⟩ := start_ev r
  intro z
  induction z with
  | zero =>
    intro _
    refine ⟨by simp only [base]; simpa [ev] using hs0, ?_⟩
    simpa [allUpTo, ev] using ht0
  | succ z ih =>
    intro hz
    obtain ⟨hs, hv⟩ := ih (by omega)
    rw [List.range_succ, List.flatMap_append, ev_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have h := seed_ev C r z _ hs (hst0.ev _) hv
    refine ⟨by rw [h.1, hs]; simp only [base, L]; rw [Nat.succ_mul]; ring, h.2⟩

/-! ## Well-formedness -/

/-- Every node of `ds`, placed from index `n` on, reads only earlier nodes. -/
def WF (n : ℕ) (ds : List (BooleanNode (T ℓ))) : Prop := ∀ p (hp : p < ds.length), (ds[p]'hp).WellFormedAt (n + p)

theorem WF_append (n : ℕ) (ds es : List (BooleanNode (T ℓ))) (h1 : WF n ds) (h2 : WF (n + ds.length) es) :
    WF n (ds ++ es) := by
  intro p hp
  by_cases hd : p < ds.length
  · rw [List.getElem_append_left hd]; exact h1 p hd
  · rw [List.getElem_append_right (by omega)]
    have := h2 (p - ds.length) (by simp at hp; omega)
    rwa [show n + ds.length + (p - ds.length) = n + p by omega] at this

theorem WF_single (n : ℕ) (nd : BooleanNode (T ℓ)) (h : nd.WellFormedAt n) : WF n [nd] := by
  intro p hp
  have : p = 0 := by simp at hp; omega
  subst this
  simpa using h

theorem WF_flatMap_range (n : ℕ) (f : ℕ → List (BooleanNode (T ℓ))) (len : ℕ)
    (hlen : ∀ i, (f i).length = len) (k : ℕ) (hf : ∀ i < k, WF (n + i * len) (f i)) :
    WF n ((List.range k).flatMap f) := by
  induction k with
  | zero => intro p hp; simp at hp
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply WF_append _ _ _ (ih (fun i hi => hf i (by omega)))
    have hl : ((List.range k).flatMap f).length = k * len := by
      clear ih hf
      induction k with
      | zero => simp
      | succ k ihk => rw [List.range_succ, List.flatMap_append]; simp [ihk, hlen, Nat.succ_mul]
    rw [hl]
    exact hf k (by omega)

theorem WF_pair (n : ℕ) (x y : BooleanNode (T ℓ)) (hx : x.WellFormedAt n) (hy : y.WellFormedAt (n + 1)) :
    WF n [x, y] := by
  intro p hp
  have : p = 0 ∨ p = 1 := by simp at hp; omega
  rcases this with rfl | rfl
  · simpa using hx
  · simpa using hy

theorem flatMap_range_length (f : ℕ → List (BooleanNode (T ℓ))) (len : ℕ) (hlen : ∀ i, (f i).length = len) :
    ∀ k, ((List.range k).flatMap f).length = k * len := by
  intro k
  induction k with
  | zero => simp
  | succ k ihk => rw [List.range_succ, List.flatMap_append]; simp [ihk, hlen, Nat.succ_mul]

theorem group_length (z c : ℕ) (args : Fin ℓ → ℕ) (a : ℕ) : (group C z c args a).length = 2 * ℓ + 1 := by
  unfold group
  rw [List.length_append, flatMap_range_length _ 2 (fun _ => rfl)]
  simp; ring

theorem block_length (z c : ℕ) (nd : OracleNode ℓ ℓ) : (block C z c nd).length = K ℓ := by
  have hK : 1 ≤ K ℓ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  cases nd with
  | oracle args =>
    simp only [block]
    rw [flatMap_range_length _ _ (group_length C z c args)]
  | _ => simp [block]; omega

theorem seed_length (z : ℕ) : (seed C z).length = L C := by
  unfold seed
  rw [List.length_append, flatMap_range_length _ _ (fun c => block_length C z c _)]
  simp

theorem lit_wf (b : Bool) (w n : ℕ) (h : w < n) : (lit b w : BooleanNode (T ℓ)).WellFormedAt n := by
  unfold lit; cases b <;> simp [BooleanNode.WellFormedAt, h]

theorem group_wf (z c : ℕ) (args : Fin ℓ → ℕ) (hargs : ∀ j, args j < c) (a : ℕ) (ha : a < T ℓ) :
    WF (gs C z c a) (group C z c args a) := by
  have hS : S ℓ ≤ base C z := by simp only [base]; omega
  have hgs : base C z ≤ gs C z c a := by simp only [gs, bs]; omega
  have hTS : 1 + a < S ℓ := by simp only [S]; omega
  have hK : 1 ≤ K ℓ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold group
  apply WF_append
  · apply WF_flatMap_range _ _ 2 (fun _ => rfl)
    intro j hj
    have hj' : j < ℓ := List.mem_range.mp (List.mem_range.mpr hj)
    apply WF_pair
    · apply lit_wf
      rw [dif_pos hj']
      have h1 := hargs ⟨j, hj'⟩
      have h2 : (args ⟨j, hj'⟩ + 1) * K ℓ ≤ c * K ℓ := Nat.mul_le_mul_right _ h1
      rw [Nat.succ_mul] at h2
      have h3 : bs C z c ≤ gs C z c a := by simp only [gs]; omega
      simp only [img, bs] at h3 ⊢
      omega
    · simp only [BooleanNode.WellFormedAt, gIdx]
      constructor
      · split_ifs <;> omega
      · omega
  · apply WF_single
    rw [flatMap_range_length _ 2 (fun _ => rfl)]
    simp only [BooleanNode.WellFormedAt, oPrev, gIdx]
    constructor
    · split_ifs <;> omega
    · split_ifs <;> omega

theorem block_wf (z c : ℕ) (hc : c < C.nodes.length) : WF (bs C z c) (block C z c (C.nodes[c])) := by
  have hwf := node_wf C c hc
  have hK : 1 ≤ K ℓ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have himg : ∀ c' < c, img C z c' < bs C z c + (K ℓ - 1) := by
    intro c' hc'
    have h2 : (c' + 1) * K ℓ ≤ c * K ℓ := Nat.mul_le_mul_right _ hc'
    rw [Nat.succ_mul] at h2
    simp only [img, bs]
    omega
  generalize C.nodes[c] = nd at hwf
  cases nd with
  | oracle args =>
    simp only [block]
    apply WF_flatMap_range _ _ _ (group_length C z c args)
    intro a ha
    exact group_wf C z c args hwf a (List.mem_range.mp (List.mem_range.mpr ha))
  | const b =>
    simp only [block]
    apply WF_append
    · intro p hp; simp [BooleanNode.WellFormedAt]
    · apply WF_single; simp [translate, BooleanNode.WellFormedAt]
  | input i =>
    simp only [block]
    apply WF_append
    · intro p hp; simp [BooleanNode.WellFormedAt]
    · apply WF_single; simp [translate, BooleanNode.WellFormedAt]
  | not c1 =>
    simp only [block]
    apply WF_append
    · intro p hp; simp [BooleanNode.WellFormedAt]
    · apply WF_single; simp only [translate, BooleanNode.WellFormedAt, List.length_replicate]
      exact himg c1 hwf
  | and c1 c2 =>
    simp only [block]
    apply WF_append
    · intro p hp; simp [BooleanNode.WellFormedAt]
    · apply WF_single; simp only [translate, BooleanNode.WellFormedAt, List.length_replicate]
      exact ⟨himg c1 hwf.1, himg c2 hwf.2⟩
  | or c1 c2 =>
    simp only [block]
    apply WF_append
    · intro p hp; simp [BooleanNode.WellFormedAt]
    · apply WF_single; simp only [translate, BooleanNode.WellFormedAt, List.length_replicate]
      exact ⟨himg c1 hwf.1, himg c2 hwf.2⟩

theorem seed_wf (z : ℕ) : WF (base C z) (seed C z) := by
  unfold seed
  apply WF_append
  · apply WF_flatMap_range _ _ _ (fun c => block_length C z c _)
    intro c hc
    have hc' : c < C.nodes.length := List.mem_range.mp (List.mem_range.mpr hc)
    have hnd : C.nodes.getD c (.const false) = C.nodes[c] := by simp [List.getD_eq_getElem?_getD, hc']
    rw [hnd]
    exact block_wf C z c hc'
  · rw [flatMap_range_length _ _ (fun c => block_length C z c _)]
    apply WF_pair
    · simp only [BooleanNode.WellFormedAt, img]
      have ho := C.output.isLt
      have h2 : (C.output.val + 1) * K ℓ ≤ C.nodes.length * K ℓ := Nat.mul_le_mul_right _ ho
      rw [Nat.succ_mul] at h2
      have hK : 1 ≤ K ℓ := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    · simp only [BooleanNode.WellFormedAt, base, S]
      omega

theorem start_wf : WF 0 (start ℓ) := by
  intro p hp
  unfold start at hp ⊢
  simp only [List.length_append, List.length_singleton, List.length_ofFn] at hp
  by_cases h0 : p = 0
  · subst h0; simp [BooleanNode.WellFormedAt]
  by_cases h1 : p < 1 + T ℓ
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
    simp [BooleanNode.WellFormedAt]
  · rw [List.getElem_append_right (by simp; omega)]
    simp [BooleanNode.WellFormedAt]

theorem start_length : (start ℓ).length = S ℓ := by simp [start]

theorem nodes_length : (nodes C).length = base C (T ℓ) := by
  unfold nodes
  rw [List.length_append, start_length, flatMap_range_length _ _ (seed_length C)]

theorem nodes_wf : WF 0 (nodes C) := by
  unfold nodes
  apply WF_append _ _ _ start_wf
  rw [start_length, Nat.zero_add]
  apply WF_flatMap_range _ _ _ (seed_length C)
  intro z _
  exact seed_wf C z

/-- **The stage-2 circuit `c_T`** on the `2^ℓ` table bits (`sec:all-lengths` stage 2). -/
def tCircuit : BooleanCircuit (T ℓ) where
  nodes := nodes C
  output := ⟨(nodes C).length - 1, by rw [nodes_length]; simp only [base, S]; omega⟩
  wellFormed := fun i => by simpa using nodes_wf C i.val i.isLt

theorem tCircuit_values (r : BitInput (T ℓ)) : (tCircuit C).values r = ev r (nodes C) #[] := rfl

/-- **The value of `c_T`**: `⋀_{z < 2^ℓ} ¬C^{O_t}(bin(z))`. -/
theorem tCircuit_eval_allUpTo (r : BitInput (T ℓ)) : (tCircuit C).eval r = allUpTo C r (T ℓ) := by
  unfold BooleanCircuit.eval
  rw [tCircuit_values]
  unfold nodes
  rw [ev_append]
  have h := (seeds_ev C r (T ℓ) le_rfl).2
  have hidx : (tCircuit C).output.val = base C (T ℓ) - 1 := by
    change (nodes C).length - 1 = _
    rw [nodes_length]
  rw [hidx, h.read]

/-- **The meaning of `c_T`** (`sec:all-lengths` stage 2): it accepts the table `t` exactly when `C^{O_t}` is unsatisfiable,
`O_t(a) = t(binaryAddress a)`. -/
theorem tCircuit_eval (r : BitInput (T ℓ)) :
    (tCircuit C).eval r = true ↔ ∀ w : BitInput ℓ, C.eval (tOr r) w = false := by
  rw [tCircuit_eval_allUpTo, allUpTo, List.all_eq_true]
  constructor
  · intro h w
    have hz := h (binaryAddress w).val (List.mem_range.mpr (binaryAddress w).isLt)
    have hs : seedIn (binaryAddress w).val = w := by
      funext i; exact binaryAddress_val_testBit w i
    simpa [Ceval, hs] using hz
  · intro h z _
    simp [Ceval, h]

end NearCubicGates.Close.ENP.TCirc
