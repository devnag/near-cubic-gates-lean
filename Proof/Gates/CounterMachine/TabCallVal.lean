import Proof.Gates.CounterMachine.TabCallFState

/-! # RK, part 11: the value level — prefixes, tokens, the request word

* `pfxOf x`: the request's prefix (PrefixSpec: `resPrefix part` or `momPrefix r`); **`prefixes_split`**: the prefix
  machine's output is `(wsOf r).flatMap frame` and the word at `pidx` is `pfxOf x`.
* `formulaToks x`: the tokens RG prints (`ampToks e (tToks d)`, `mdToks d r j`, `mpToks d r` for `d = fdataOf x`);
  **`toks_tabCallTab`**: they are `toks (tabCallTab x).F`; **`tabWord_tabCallTab`**: `tabWord (tabCallTab x) = pfxOf x ++ natWord |toks| ++
  toks-bits` (ReqWord). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {B1 B2 cT : ℕ}

/-- The request's prefix. -/
def pfxOf (x : TabCallReq B1 B2 cT) : List Bool :=
  match x.id with
  | .residue part _ _ _ => resPrefix x.r.c x.r.p x.r.wt part
  | .digitMoment r _ => momPrefix x.r.c x.r.p x.r.wt r
  | .phiMoment r => momPrefix x.r.c x.r.p x.r.wt r

/-- The prefix machine's words. -/
def wsOf (r : CellReq B1 B2 cT) : List (List Bool) :=
  (parts r.c).map (resPrefix r.c r.p r.wt) ++ (List.range (roleCount r.c.kind)).map (momPrefix r.c r.p r.wt)

theorem prefixesWord_eq (r : CellReq B1 B2 cT) : prefixesWord r = (wsOf r).flatMap RepairOrdinary.frame := by
  simp [prefixesWord, wsOf, List.flatMap_append, List.flatMap_map]

theorem mem_moment {c : Call} {p : Params} {r j : ℕ} (h : ReqId.digitMoment r j ∈ reqIds c p) :
    r < roleCount c.kind ∧ j < p.J := by
  unfold reqIds at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨_, _, _, _, _, _, _, _, h⟩ | ⟨r', hr', (⟨j', hj', h⟩ | h)⟩
  · cases h
  · cases h; exact ⟨hr', hj'⟩
  · cases h

theorem mem_phi {c : Call} {p : Params} {r : ℕ} (h : ReqId.phiMoment r ∈ reqIds c p) : r < roleCount c.kind := by
  unfold reqIds at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨_, _, _, _, _, _, _, _, h⟩ | ⟨r', hr', (⟨j', hj', h⟩ | h)⟩
  · cases h
  · cases h
  · cases h; exact hr'

theorem parts_len (c : Call) : (parts c).length = (if 2 ≤ kindTag c.kind then 1 else 0) + 1 := by
  unfold parts; cases h : c.kind <;> simp [h, kindTag]

/-- **The selected prefix.** -/
theorem prefix_sel (x : TabCallReq B1 B2 cT) :
    ∃ h : pidx (dTag x.id) (dF1 x.id) (kindTag x.r.c.kind) < (wsOf x.r).length,
      (wsOf x.r)[pidx (dTag x.id) (dF1 x.id) (kindTag x.r.c.kind)] = pfxOf x := by
  have hmem := x.mem
  have hpl := parts_len x.r.c
  cases hid : x.id with
  | residue part q κ σ =>
    rw [hid] at hmem
    have hp : part ∈ parts x.r.c := by
      unfold reqIds at hmem
      simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton] at hmem
      rcases hmem with ⟨pt, hpt, _, _, _, _, _, _, h⟩ | ⟨_, _, (⟨_, _, h⟩ | h)⟩
      · cases h; exact hpt
      · cases h
      · cases h
    have hidx : pidx (dTag (.residue part q κ σ)) (dF1 (.residue part q κ σ)) (kindTag x.r.c.kind) =
        (parts x.r.c).idxOf part := by
      unfold parts at hp ⊢
      split_ifs at hp ⊢ with hk <;> simp at hp <;> rcases hp with rfl | rfl <;> simp [pidx, dTag, dF1, partCode]
    have hlt : (parts x.r.c).idxOf part < (parts x.r.c).length := List.idxOf_lt_length_of_mem hp
    refine ⟨by rw [hidx, wsOf, List.length_append, List.length_map]; omega, ?_⟩
    simp only [hidx, wsOf]
    rw [List.getElem_append_left (by simpa using hlt)]
    simp [pfxOf, hid, List.getElem_idxOf]
  | digitMoment r j =>
    rw [hid] at hmem
    have hr := (mem_moment hmem).1
    have hidx : pidx (dTag (.digitMoment r j)) (dF1 (.digitMoment r j)) (kindTag x.r.c.kind) =
        (parts x.r.c).length + r := by simp [pidx, dTag, dF1, hpl]; omega
    refine ⟨by rw [hidx, wsOf, List.length_append, List.length_map, List.length_map, List.length_range]; omega, ?_⟩
    simp only [hidx, wsOf]
    rw [List.getElem_append_right (by simp)]
    simp [pfxOf, hid]
  | phiMoment r =>
    rw [hid] at hmem
    have hr := mem_phi hmem
    have hidx : pidx (dTag (.phiMoment r)) (dF1 (.phiMoment r)) (kindTag x.r.c.kind) =
        (parts x.r.c).length + r := by simp [pidx, dTag, dF1, hpl]; omega
    refine ⟨by rw [hidx, wsOf, List.length_append, List.length_map, List.length_map, List.length_range]; omega, ?_⟩
    simp only [hidx, wsOf]
    rw [List.getElem_append_right (by simp)]
    simp [pfxOf, hid]

theorem coefOK_of (r : CellReq B1 B2 cT) : CoefOK r.c r.p r.wt := by
  obtain ⟨w, hw⟩ := r.hw
  have wf1 : r.c.first.gates.length = r.c.first.coeffs.length := r.adm.2.1.1
  have wf2 : r.c.second.gates.length = r.c.second.coeffs.length := r.adm.2.2.1.1
  have hc : ∀ q, (circ r.c q).coeffs.length = (circ r.c q).gates.length := fun q => by
    unfold circ; split_ifs <;> simp [wf1, wf2]
  exact ⟨fun q _ => hc q, fun s hs q hq => by rw [coef_length_of_decode _ _ w _ hw s q hs hq, hc]⟩

/-- The tokens RG prints for a request. -/
def formulaToks (x : TabCallReq B1 B2 cT) : List Tok :=
  match x.id with
  | .residue .. => ampToks x.r.p.e (tToks (fdataOf x))
  | .digitMoment r j => mdToks (fdataOf x) r j
  | .phiMoment r => mpToks (fdataOf x) r

theorem vecs_length (q d : ℕ) : ∀ v ∈ vecs q d, v.length = d := by
  induction d with
  | zero => intro v hv; simp [vecs] at hv; subst hv; rfl
  | succ d ih =>
    intro v hv
    simp only [vecs, List.mem_flatMap, List.mem_map, List.mem_range] at hv
    obtain ⟨a, _, u, hu, rfl⟩ := hv
    simp [ih u hu]

theorem mem_residue_len {c : Call} {p : Params} {part : Option Bool} {q : ℕ} {κ σ : List ℕ}
    (h : ReqId.residue part q κ σ ∈ reqIds c p) : κ.length = roleCount c.kind * p.J ∧ σ.length = roleCount c.kind := by
  unfold reqIds at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨_, _, q', _, κ', hκ', σ', hσ', h⟩ | ⟨_, _, (⟨_, _, h⟩ | h)⟩
  · cases h; exact ⟨vecs_length _ _ _ hκ', vecs_length _ _ _ hσ'⟩
  · cases h
  · cases h

theorem toks_tabCallTab (x : TabCallReq B1 B2 cT) : toks (tabCallTab x).F = formulaToks x := by
  have hspec := cellReq_spec x.r
  have hL := factors_length hspec
  have hok := coefOK_of x.r
  have hJ1 : 1 ≤ x.r.p.J := hspec.J_pos
  unfold tabCallTab formulaToks
  split
  · next part q κ σ h =>
    have hm := x.mem; rw [h] at hm
    have hl := mem_residue_len hm
    show toks (resFormula x.r.c x.r.p x.r.wt q κ σ) = _
    rw [tToks_link x.r.c x.r.p x.r.wt hL q κ σ hl.1 hok]
    simp [h, fdataOf, qOf, dTag, dF2, dRho]
  · next r j h =>
    have hm := x.mem; rw [h] at hm
    have hrj := mem_moment hm
    show toks (momF (V := 2 * (circ x.r.c r).gates.length) x.r.c x.r.p x.r.wt r (some j)) = _
    rw [toks_momF x.r.c x.r.p x.r.wt r hrj.1 (some j) (fun i hi => by cases hi; exact hrj.2) hJ1 hok,
      mdToks_link x.r.c x.r.p x.r.wt hL (qOf x.id) (dRho x.id) r j (by have := roleCount_le_two x.r.c; omega) hrj.2]
    simp [h, fdataOf]
  · next r h =>
    have hm := x.mem; rw [h] at hm
    have hr := mem_phi hm
    show toks (momF (V := 2 * (circ x.r.c r).gates.length) x.r.c x.r.p x.r.wt r none) = _
    rw [toks_momF x.r.c x.r.p x.r.wt r hr none (fun i hi => by cases hi) hJ1 hok,
      mpToks_link x.r.c x.r.p x.r.wt hL hJ1 (qOf x.id) (dRho x.id) r (by have := roleCount_le_two x.r.c; omega)]
    simp [h, fdataOf]

/-- **The request word.** -/
theorem tabWord_tabCallTab (x : TabCallReq B1 B2 cT) :
    tabWord (tabCallTab x) = pfxOf x ++ natWord (formulaToks x).length ++ (formulaToks x).flatMap tokWord := by
  rw [← toks_tabCallTab]
  unfold tabCallTab pfxOf
  split
  · next part q κ σ h => simp only [h]; exact resReq_tabWord _ _ _ _ _ _ _ _ _ _
  · next r j h => simp only [h]; exact momReq_tabWord _ _ _ _ _ _ _ _
  · next r h => simp only [h]; exact momReq_tabWord _ _ _ _ _ _ _ _

end NearCubicGates.Close.CounterMachine
