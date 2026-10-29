import SourceAdapters.Routing.CoordinateMachineOutput
import SourceAdapters.ShortPCP.Machines.FLangPack

/-!
# Packed gate-reference stack

The construction in `lem:generator`: the postfix circuit printer holds absolute gate references in
a packed stack. Variable 28 is the packed stack, 29 its depth, 30 its entry width,
and 24 the next gate reference. Every operation is an ordinary FL operation.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.TermsMachine

open NearCubicGates.Adapters.ShortPCP.Machines.FL
open CoordinateMachine

def stackAt (k : ℕ) : E :=
  .md (.shr (.v 28) (.mul (.k k) (.v 30))) (.shl (.k 1) (.v 30))

def pushNext : S :=
  .seq (.set 28 (.add (.v 24) (.shl (.v 28) (.v 30))))
    (.set 29 (.add (.v 29) (.k 1)))

def dropStack (k : ℕ) : S :=
  .seq (.set 28 (.shr (.v 28) (.mul (.k k) (.v 30))))
    (.set 29 (.sub (.v 29) (.k k)))

theorem stackAt_spec (G : Glob) (s : FS) (w k : ℕ) (st : List ℕ)
    (h28 : s.env 28 = packW w st) (h30 : s.env 30 = w)
    (hs : ∀ a ∈ st, a < 2 ^ w) (hk : k ≤ G.cap) (hkw : k * w ≤ G.cap)
    (hw : 2 ^ w ≤ G.cap) :
    evalE G s (stackAt k) = st.getD k 0 := by
  have h1 : 1 ≤ G.cap := le_trans (Nat.one_le_two_pow) hw
  simp only [stackAt, evalE, h28, h30, min_eq_left hk, min_eq_left hkw,
    min_eq_left h1, one_mul, min_eq_left hw]
  exact packW_get w st hs k

theorem pushNext_state (G : Glob) (s : FS) (w n : ℕ) (st : List ℕ)
    (h28 : s.env 28 = packW w st) (h29 : s.env 29 = st.length)
    (h30 : s.env 30 = w) (h24 : s.env 24 = n)
    (hp : packW w (n :: st) ≤ G.cap) (hd : st.length + 1 ≤ G.cap) :
    evalS G pushNext s = (s.setv 28 (packW w (n :: st))).setv 29 (st.length + 1) := by
  have hsh : packW w st * 2 ^ w ≤ G.cap := by
    simp only [packW] at hp
    nlinarith
  have hn : n + packW w st * 2 ^ w ≤ G.cap := by
    simpa only [packW, Nat.mul_comm] using hp
  have he : evalE G s (.add (.v 24) (.shl (.v 28) (.v 30))) = packW w (n :: st) := by
    simp only [evalE, h24, h28, h30]
    rw [min_eq_left hsh, min_eq_left hn]
    simp only [packW, Nat.mul_comm]
  change evalS G (.set 29 (.add (.v 29) (.k 1)))
    (s.setv 28 (evalE G s (.add (.v 24) (.shl (.v 28) (.v 30))))) = _
  rw [he]
  simp only [evalS_set, evalE, FS.setv_env,
    Function.update_of_ne (by decide : (29 : Var) ≠ 28), h29,
    min_eq_left (show 1 ≤ G.cap by omega), min_eq_left hd]

theorem pushNext_spec (G : Glob) (s : FS) (w n : ℕ) (st : List ℕ)
    (h28 : s.env 28 = packW w st) (h29 : s.env 29 = st.length)
    (h30 : s.env 30 = w) (h24 : s.env 24 = n)
    (hp : packW w (n :: st) ≤ G.cap) (hd : st.length + 1 ≤ G.cap) :
    (evalS G pushNext s).env 28 = packW w (n :: st) ∧
      (evalS G pushNext s).env 29 = st.length + 1 ∧
      Appends [28, 29] s (evalS G pushNext s) [] := by
  rw [pushNext_state G s w n st h28 h29 h30 h24 hp hd]
  refine ⟨by simp, by simp, ?_⟩
  simpa using (Appends.setv [28, 29] s 28 (by simp) (packW w (n :: st))).trans
    (Appends.setv [28, 29] _ 29 (by simp) (st.length + 1))

theorem dropStack_state (G : Glob) (s : FS) (w k : ℕ) (st : List ℕ)
    (h28 : s.env 28 = packW w st) (h29 : s.env 29 = st.length)
    (h30 : s.env 30 = w) (hs : ∀ a ∈ st, a < 2 ^ w)
    (hk : k ≤ G.cap) (hkw : k * w ≤ G.cap) :
    evalS G (dropStack k) s =
      (s.setv 28 (packW w (st.drop k))).setv 29 (st.length - k) := by
  have he : evalE G s (.shr (.v 28) (.mul (.k k) (.v 30))) = packW w (st.drop k) := by
    simp only [evalE, h28, h30, min_eq_left hk, min_eq_left hkw]
    simpa only [Nat.mul_comm] using (packW_drop w st hs k).symm
  change evalS G (.set 29 (.sub (.v 29) (.k k)))
    (s.setv 28 (evalE G s (.shr (.v 28) (.mul (.k k) (.v 30))))) = _
  rw [he]
  simp only [evalS_set, evalE, FS.setv_env,
    Function.update_of_ne (by decide : (29 : Var) ≠ 28), h29, min_eq_left hk]

theorem dropStack_spec (G : Glob) (s : FS) (w k : ℕ) (st : List ℕ)
    (h28 : s.env 28 = packW w st) (h29 : s.env 29 = st.length)
    (h30 : s.env 30 = w) (hs : ∀ a ∈ st, a < 2 ^ w)
    (hk : k ≤ G.cap) (hkw : k * w ≤ G.cap) :
    (evalS G (dropStack k) s).env 28 = packW w (st.drop k) ∧
      (evalS G (dropStack k) s).env 29 = st.length - k ∧
      Appends [28, 29] s (evalS G (dropStack k) s) [] := by
  rw [dropStack_state G s w k st h28 h29 h30 hs hk hkw]
  refine ⟨by simp, by simp, ?_⟩
  simpa using (Appends.setv [28, 29] s 28 (by simp) (packW w (st.drop k))).trans
    (Appends.setv [28, 29] _ 29 (by simp) (st.length - k))

theorem pushNext_wf (d : ℕ) : wfS pushNext d = true := by
  simp [pushNext, wfS, dE]

theorem dropStack_wf (k d : ℕ) : wfS (dropStack k) d = true := by
  simp [dropStack, wfS, dE]

end NearCubicGates.Adapters.Routing.TermsMachine
