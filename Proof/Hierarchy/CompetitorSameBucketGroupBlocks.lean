import Proof.Hierarchy.CompetitorSameBucketGroupFoldSemantics
import Proof.Hierarchy.CompetitorSameBucketDenseSemantics

/-! The transducer's literal scan equals the positive/negative totals of
consecutive nonempty same-ID blocks. Final totals discharge every add fit. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open SignedSortKey RadixSemantics CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem FitsAll_append (w p m : ℕ) (xs ys : List Entry) (s : Store) :
    FitsAll w p m s (xs++ys) ↔ FitsAll w p m s xs ∧ FitsAll w p m (foldStore p m s xs) ys := by
  induction xs generalizing s with
  | nil => simp [FitsAll,foldStore]
  | cons e xs ih => simp only [List.cons_append,FitsAll,foldStore,ih,and_assoc]

def blockWord (w : ℕ) (g : List Entry) := binary w (positive g)++binary w (negative g)
def pendingWord (w : ℕ) (s : Store) := if s.present then pair w s else []

theorem blocks_scan (w p m : ℕ) (gs : List (List Entry)) (s : Store)
    (hne : ∀ g∈gs,g≠[])
    (hsame : ∀ g∈gs,∀ a∈g,∀ b∈g,a.ids m=b.ids m)
    (hapart : gs.Pairwise (fun g h => ∀ a∈g,∀ b∈h,a.ids m≠b.ids m))
    (hbits : ∀ e∈gs.flatten,e.coefficient.natAbs<2^p)
    (hbound : ∀ g∈gs,positive g<2^w ∧ negative g<2^w)
    (hzero : s.present=false → s.positive=0 ∧ s.negative=0)
    (hcurrent : s.present=true → ∀ e∈gs.flatten,s.current≠e.ids m) :
    FitsAll w p m s gs.flatten ∧
      scanWord w p m s gs.flatten=pendingWord w s++gs.flatMap (blockWord w) := by
  induction gs generalizing s with
  | nil => simp [FitsAll,scanWord,pendingWord]
  | cons g gs ih =>
    obtain ⟨e,es,rfl⟩ := List.exists_cons_of_ne_nil (hne g (by simp))
    have hgroup : e::es ∈ (e::es)::gs := by simp
    have heflat : e∈((e::es)::gs).flatten := by simp
    obtain ⟨hsep,hrest⟩ := List.pairwise_cons.mp hapart
    obtain ⟨hgp,hgn⟩ := hbound (e::es) hgroup
    have hb := hbits e heflat
    have hchange : changed s m e=s.present := by
      cases hp : s.present
      · simp [changed,hp]
      · simp [changed,hp,hcurrent hp e heflat]
    have hbasep : (if changed s m e then 0 else s.positive)=0 := by
      rw [hchange]
      cases hp : s.present
      · exact (hzero hp).1
      · rfl
    have hbasen : (if changed s m e then 0 else s.negative)=0 := by
      rw [hchange]
      cases hp : s.present
      · exact (hzero hp).2
      · rfl
    have hfit := fits_of_counts w p m s e hb
      (by rw [hbasep,positive_cons] at *;omega) (by rw [hbasen,negative_cons] at *;omega)
    obtain ⟨hpos,hneg⟩ := stepStore_counts s p m e hb
    rw [hbasep,Nat.zero_add] at hpos
    rw [hbasen,Nat.zero_add] at hneg
    obtain ⟨_,_,hcur,hpresent⟩ := stepStore_fields s p m e
    obtain ⟨hfits,hword,hp,hn,hkey,_,hkeep⟩ := homogeneous_prefix w p m (e.ids m) es (stepStore s p m e)
      (fun a ha => hsame (e::es) hgroup a (by simp [ha]) e (by simp)) (fun _ => hcur)
      (fun a ha => hbits a (by simp [ha]))
      (by rw [hpos];simpa only [positive_cons] using hgp)
      (by rw [hneg];simpa only [negative_cons] using hgn)
    let after := foldStore p m (stepStore s p m e) es
    have haPresent : after.present=true := hkeep hpresent
    have haKey : after.current=e.ids m := hkey haPresent
    have haPos : after.positive=positive (e::es) := by simpa only [hpos,positive_cons] using hp
    have haNeg : after.negative=negative (e::es) := by simpa only [hneg,negative_cons] using hn
    obtain ⟨hrfits,hrword⟩ := ih after
      (fun h hh => hne h (by simp [hh]))
      (fun h hh => hsame h (by simp [hh])) hrest
      (fun a ha => hbits a (by simp [ha]))
      (fun h hh => hbound h (by simp [hh]))
      (by intro hf;rw [haPresent] at hf;cases hf)
      (by
        intro _ a ha
        obtain ⟨h,hh,hah⟩ := List.mem_flatten.mp ha
        rw [haKey]
        exact hsep h hh e (by simp) a hah)
    constructor
    · change Fits w p m s e ∧ FitsAll w p m (stepStore s p m e) (es++gs.flatten)
      exact ⟨hfit,(FitsAll_append w p m es gs.flatten (stepStore s p m e)).mpr ⟨hfits,hrfits⟩⟩
    · change emittedPrefix w m s e++scanWord w p m (stepStore s p m e) (es++gs.flatten)=_
      rw [hword,hrword]
      have hpending : pendingWord w after=blockWord w (e::es) := by
        simp only [pendingWord,haPresent,↓reduceIte,pair,haPos,haNeg,blockWord]
      rw [hpending]
      simp only [emittedPrefix,hchange,pendingWord,List.flatMap_cons]

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
