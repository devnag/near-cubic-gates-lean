import SourceAdapters.ShortPCP.Machines.FLangPx

/-!
# Single-run time, machine layer 24: the masks, and the request's hypotheses for the parse

`lem:patch-r` (proof of `thm:short-pcp-ours`): "Let V accept x with proof π and random string R ∈ {0,1}^{r0} exactly when V0 accepts
x with π and R ⊕ σ for every σ ∈ S". The multiset `S` is the last field of the data word (`listWord frame masks`);
the parse record holds its size (slot 12) and the position of its first frame (slot 13). `maskP j` reads mask
number `j` (`26 := bitsValue σ_j`, `27 := |σ_j|`; `maskP_spec`).

`valid_irr`, `valid_px` collect what `Request.Valid` and a bijective `ψ` give to `cdP_spec` and `pxP_spec`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary NearCubicWires.WireExponent3_5
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.Joins (CodeGate listWord)
open NearCubicGates.Adapters.Joins.SingleRun (Request)
open NearCubicGates.Adapters.ACSP.Affine (Instance)
open NearCubicGates.Adapters.ShortPCP.Time

variable (G : Glob)

/-- Read mask number `j` (an expression, evaluated once): `26 := bitsValue σ_j`, `27 := |σ_j|` (cursor from record
slot 13; loop variable `32`). -/
def maskP (j : E) : S := .seq (.set 14 (recE 13)) (.seq (.loop 32 j pFrameD) pFrameD)

def maskW : List Var := [14, 26, 27, 28, 32]

/-- **The mask reader.** -/
theorem maskP_spec (s : FS) (q : Request) (c : PCtx G q (s.env 10)) (h15 : s.env 15 = packW (G.K / 16) (parseRec q))
    (j : E) (k : ℕ) (hj : evalE G (s.setv 14 (posM q)) j = k) (hk : k < q.masks.length) :
    (evalS G (maskP j) s).env 26 = bitsValue q.masks[k] ∧ (evalS G (maskP j) s).env 27 = q.masks[k].length ∧
      Wr maskW s (evalS G (maskP j) s) := by
  have hd := c.bd
  obtain ⟨a11, -, l11⟩ := c.piece 10 (listWord frame q.masks) (by norm_num) rfl
  rw [listWord_eq] at a11 l11
  obtain ⟨-, a11b⟩ := At.append a11
  simp only [List.length_append] at l11
  have hpM : posM q = posOf q 10 + (natWord q.masks.length).length := rfl
  have e1 : evalS G (.set 14 (recE 13)) s = s.setv 14 (posM q) := by
    simp only [evalS_set]; rw [recE_parse G s q c h15 13 (by norm_num)]; rfl
  have hnm := count_le frame q.masks (fun x _ => frame_pos x) (posOf q 10) q.data.length
    (by rw [listWord_eq, List.length_append]; exact l11)
  obtain ⟨l14, lW⟩ := curLoop_spec G 32 j pFrameD pFrameW frame q.masks (s.setv 14 (posM q)) (posM q) q.data.length k
    (by rw [hj]; have := hd.2; omega) hk.le (by simpa [hpM] using a11b) (by simp) (by rw [hpM]; omega)
    (by decide) (by decide) (by decide)
    (fun x _ t p' ha ht he => let r := pFrameD_spec G t x p' _ ha ht he hd; ⟨r.2.2.1, r.2.2.2⟩)
  generalize hs2 : evalS G (.loop 32 j pFrameD) (s.setv 14 (posM q)) = s2 at l14 lW
  have hA := At.flatten frame q.masks a11b k hk
  have hle := flatten_take_le frame q.masks (k + 1)
  have hts := flatten_take_succ_length frame q.masks k hk
  obtain ⟨f26, f27, -, fW⟩ := pFrameD_spec G s2 q.masks[k] _ q.data.length
    (by rw [lW.env 10 (by decide)]; simp only [FS.setv_env, Function.update_of_ne (show (10 : Var) ≠ 14 by decide)]
        rw [hpM]; exact hA) l14 (by rw [hpM] at *; omega) hd
  have e : evalS G (maskP j) s = evalS G pFrameD s2 := by
    simp only [maskP, evalS_seq]; rw [e1, hs2]
  rw [e]
  exact ⟨f26, f27, ((Wr.setv _ (by decide) _).trans (lW.mono (by decide))).trans (fW.mono (by decide))⟩

/-! ## What `Request.Valid` gives -/

theorem valid_irr (q : Request) (hv : q.Valid) : Irreducible (GF.toPoly q.code.irr) := hv.2.1.1.1

/-- The hypotheses of `pxP_spec` from `Request.Valid` and a bijective `ψ` (`TimeVerdict`). -/
theorem valid_px {F : Type} [Field F] (q : Request) (hv : q.Valid) (ψ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (hψ : Function.Bijective ψ) :
    CharP F 2 ∧ Indep ((iBw q).map (ev ψ)) ∧ q.xbar.length = 2 ^ q.mI := by
  exact ⟨charP_two q ψ, indep_iB q ψ hv hψ, by rw [mI_eq q hv]; exact hv.2.2.1⟩

end NearCubicGates.Adapters.ShortPCP.Machines.FL
