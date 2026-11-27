import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.LinearPMap

/-! Certificates obtained by saturating a family of observable linear forms under pullback. -/
namespace HiddenWord.ObservableClosure

variable {K V A I : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Read the first symbol as the outermost pullback. -/
def follow (step : A → V →ₗ[K] V) : List A → V → V
  | [], v => v
  | a :: w, v => step a (follow step w v)

def reachable (step : A → V →ₗ[K] V) (seed : I → V) : Submodule K V :=
  Submodule.span K (Set.range fun p : List A × I => follow step p.1 (seed p.2))

theorem seed_mem (step : A → V →ₗ[K] V) (seed : I → V) (i : I) :
    seed i ∈ reachable step seed :=
  Submodule.subset_span ⟨([], i), rfl⟩

theorem step_mem (step : A → V →ₗ[K] V) (seed : I → V) (a : A) {v : V}
    (hv : v ∈ reachable step seed) : step a v ∈ reachable step seed := by
  change v ∈ (reachable step seed).comap (step a)
  apply (Submodule.span_le.mpr ?_) hv
  rintro _ ⟨⟨w,i⟩, rfl⟩
  exact Submodule.subset_span ⟨(a :: w, i), rfl⟩

/-- Every invariant subspace containing the initial observations contains their full closure. -/
theorem least (step : A → V →ₗ[K] V) (seed : I → V) (U : Submodule K V)
    (hseed : ∀ i, seed i ∈ U) (hstep : ∀ a (v : V), v ∈ U → step a v ∈ U) :
    reachable step seed ≤ U := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨w,i⟩, rfl⟩
  induction w with
  | nil => exact hseed i
  | cons a w ih => exact hstep a _ ih

theorem checks_on_generators (step : A → V →ₗ[K] V) (basis : Set V)
    (h : ∀ a, ∀ v ∈ basis, step a v ∈ Submodule.span K basis) :
    ∀ a (v : V), v ∈ Submodule.span K basis → step a v ∈ Submodule.span K basis := by
  intro a v hv
  change v ∈ (Submodule.span K basis).comap (step a)
  exact (Submodule.span_le.mpr (h a) : Submodule.span K basis ≤
    (Submodule.span K basis).comap (step a)) hv

/-- Equality of two evaluations on a generated invariant subspace suffices for every word. -/
theorem certificate (step : A → V →ₗ[K] V) (seed : I → V) (basis : Set V)
    (p q : V →ₗ[K] K) (hi : ∀ i, seed i ∈ Submodule.span K basis)
    (hs : ∀ a, ∀ v ∈ basis, step a v ∈ Submodule.span K basis)
    (he : ∀ v ∈ basis, p v = q v) (w : List A) (i : I) :
    p (follow step w (seed i)) = q (follow step w (seed i)) := by
  have hb : Submodule.span K basis ≤ LinearMap.ker (p - q) := by
    apply Submodule.span_le.mpr
    intro v hv
    exact sub_eq_zero.mpr (he v hv)
  have hw : follow step w (seed i) ∈ reachable step seed :=
    Submodule.subset_span ⟨(w,i), rfl⟩
  exact sub_eq_zero.mp (hb (least step seed _ hi (checks_on_generators step basis hs) hw))

/-- Arbitrary exact decoders cannot distinguish two observations equal on every reachable query. -/
theorem all_words_iff (step : A → V →ₗ[K] V) (seed : I → V) (p q : V →ₗ[K] K) :
    (∀ w i, p (follow step w (seed i)) = q (follow step w (seed i))) ↔
    reachable step seed ≤ LinearMap.ker (p - q) := by
  constructor
  · intro h
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨w,i⟩, rfl⟩
    exact sub_eq_zero.mpr (h w i)
  · intro h w i
    have hw : follow step w (seed i) ∈ reachable step seed :=
      Submodule.subset_span ⟨(w,i), rfl⟩
    exact sub_eq_zero.mp (h hw)

end HiddenWord.ObservableClosure
