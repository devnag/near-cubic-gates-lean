import Proof.Wire_3_5.PrimAsmPopRecW

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopLink
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW
open NearCubicWires.WireExponent3_5.PrimAsm.PopRec NearCubicWires.WireExponent3_5.PrimAsm.LevelWordW
open NearCubicWires.WireExponent3_5.PrimAsm.PopBlockW NearCubicWires.WireExponent3_5.PrimAsm.PopRecW
open NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- The list bound of the base list (the same at every visit: it reads only `J` and the windows). -/
def lbP (P : FlatListParams) : ℕ := listBound ⟨P.base.M, P.base.J, P.base.W, fun _ _ => false⟩

theorem listBound_visit (P : FlatListParams) (e : P.FlatSeed) (k : Fin P.walkLen) :
    listBound (visitData P e k) = lbP P := rfl

/-- The stage-5 register capacity of the base list at point length `L` (the same at every visit). -/
def capP (P : FlatListParams) (L : ℕ) : ℕ :=
  ListEval.capOf P.base.M P.base.J P.base.W (fun _ => List.replicate L false) L

theorem levelWord_length_congr (M J : ℕ) (W : ℕ → ℕ) (r1 r2 : ℕ → List Bool)
    (h : ∀ j ≤ J, (r1 j).length = (r2 j).length) :
    (ListEval.levelWord M J W r1).length = (ListEval.levelWord M J W r2).length := by
  unfold ListEval.levelWord
  simp only [List.length_append, List.length_flatMap]
  congr 2
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hjJ : j ≤ J := by
    unfold ListEval.levels at hj
    simp only [List.mem_reverse, List.mem_range] at hj
    omega
  unfold ListEval.record
  simp only [List.length_cons, List.length_append, h j hjJ]

theorem capC_visit (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (k : Fin P.walkLen) :
    capC (visitData P e k) L = capP P L := by
  unfold capC capP ListEval.capOf
  rw [levelWord_length_congr _ _ _ _ (fun _ => List.replicate L false) (fun j _ => by simp [ListEval.rowsOf])]
  rfl

/-- The visits' rows, by visit index. -/
def rowKP (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (k : ℕ) : ℕ → List Bool :=
  if h : k < P.walkLen then ListEval.rowsOf (visitData P e ⟨k, h⟩) L else fun _ => []

theorem rowKP_length (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) :
    ∀ k < P.walkLen, ∀ j ≤ P.base.J, (rowKP P e L k j).length = L := by
  intro k hk j _
  unfold rowKP; rw [dif_pos hk]; simp [ListEval.rowsOf]

/-- The coefficient words `+1`, `−1` at level 2. -/
def cwOne : List Bool := (Rec.coefWord 1).flatMap m2
def cwNeg : List Bool := (Rec.coefWord (-1)).flatMap m2

theorem finRange_flatMap {n : ℕ} (g : Fin n → List Bool) (g' : ℕ → List Bool) (h : ∀ i : Fin n, g i = g' i.val) :
    (List.finRange n).flatMap g = (List.range n).flatMap g' := by
  have hm : (List.finRange n).map Fin.val = List.range n :=
    List.ext_getElem (by simp) (fun i _ _ => by simp)
  rw [← hm, List.flatMap_map]
  exact List.flatMap_congr fun i _ => h i

theorem reps_flatMap (n : ℕ) (w : List Bool) : (reps n w).flatMap m2 = reps n (w.flatMap m2) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [reps_succ, List.flatMap_append, ih, reps_succ]

theorem oneE_eq (P : FlatListParams) (s : Fin (P.M + 1)) :
    oneE s.val P.walkLen = (oneWC P s).flatMap m2 ++ [true, false] := by
  unfold oneE oneWC popOne
  by_cases hs : s.val = 0
  · rw [if_pos hs, if_pos hs]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Rec.termWord, List.cons_append]
    rw [flatMap_replicate_gen]
    unfold oneHead oneVisit
    simp only [List.flatMap_cons, List.flatMap_append, reps_flatMap, List.flatMap_nil, List.append_assoc,
      List.cons_append, List.nil_append]
  · rw [if_neg hs, if_neg hs]; rfl

section
variable (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (r4 G off : ℕ)

theorem visitE_eq (s' : ℕ) (k : Fin P.walkLen) (hlen : (sliceLabs r4 G off L).length = 4 * L) :
    visitE P e L sgn (sliceLabs r4 G off L) s' k =
      blockE (4 * L) (3 * lbP P) (labSum (sliceLabs r4 G off L)) (sliceLabs r4 G off L)
          (levelE P.M (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.base.B)) P.base.J (rowKP P e L k.val)) s'
          sgn (capP P L) true ++
        blockE (4 * L) (3 * lbP P) (labSum (sliceLabs r4 G off L)) (sliceLabs r4 G off L)
          (levelE P.M (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.base.B)) P.base.J (rowKP P e L k.val)) s'
          sgn (capP P L) false := by
  have hr : rowKP P e L k.val = ListEval.rowsOf (visitData P e k) L := by unfold rowKP; rw [dif_pos k.isLt]
  have hl : (ListEval.levelWord (visitData P e k).M (visitData P e k).J (visitData P e k).W
      (ListEval.rowsOf (visitData P e k) L)).flatMap m2 =
      levelE P.M (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.base.B)) P.base.J (rowKP P e L k.val) := by
    rw [hr]
    exact levelE_eq P.base (ListEval.rowsOf (visitData P e k) L)
  unfold visitE
  rw [hl, listBound_visit, capC_visit, cap1C_eq L _ hlen]

theorem visits_eq (s' : ℕ) (hlen : (sliceLabs r4 G off L).length = 4 * L) :
    ((List.finRange P.walkLen).flatMap fun k => visitE P e L sgn (sliceLabs r4 G off L) s' k) =
      visitsE P.walkLen (4 * L) (3 * lbP P) r4 G off L (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.base.B))
        P.base.J P.M s' (capP P L) sgn (rowKP P e L) :=
  finRange_flatMap _ _ fun k => visitE_eq P e L sgn r4 G off s' k hlen

theorem statesE_eq (s : Fin (P.M + 1)) (hlen : (sliceLabs r4 G off L).length = 4 * L) :
    statesE P e L sgn (sliceLabs r4 G off L) s =
      statesAbs s.val P.walkLen (4 * L) (3 * lbP P) r4 G off L
        (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.base.B)) P.base.J P.M (capP P L) sgn (rowKP P e L)
        cwOne cwNeg := by
  unfold statesE statesC statesAbs
  by_cases hs : s.val = 0
  · rw [if_pos hs, if_pos hs, List.flatMap_map]
    refine finRange_flatMap _ _ fun i => ?_
    unfold stateE stateEw
    rw [visits_eq P e L sgn r4 G off _ hlen]
    rfl
  · rw [if_neg hs, if_neg hs]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    unfold stateE stateEw
    rw [visits_eq P e L sgn r4 G off _ hlen]
    rfl

/-- **The written POP record is the one C2's POP row reads** (at any capacities `R`, `Lgc`, `cp` and threshold `θ`). -/
theorem popRec_link (hlen : (sliceLabs r4 G off L).length = 4 * L)
    (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length) (s : Fin (P.M + 1)) (θ R Lgc cp : ℕ) :
    frame (popRowRec P.walkLen θ R Lgc cp (oneWC P s) (popStates P e L sgn (sliceLabs r4 G off L) hlabs s)) =
      popRecAbs P.walkLen θ R Lgc cp s.val (4 * L) (3 * lbP P) r4 G off L
        (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.base.B)) P.base.J P.M (capP P L) sgn (rowKP P e L)
        cwOne cwNeg := by
  rw [popEmit_eq, statesE_eq P e L sgn r4 G off s hlen, ← oneE_eq]
  unfold popRecAbs
  simp only [List.append_assoc]

end

end NearCubicWires.WireExponent3_5.PrimAsm.PopLink
