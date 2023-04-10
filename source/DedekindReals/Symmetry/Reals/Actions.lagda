Andrew Sneap and Ohad Kammar

Various actions on the reals

\begin{code}
{-# OPTIONS --without-K --exact-split --no-sized-types --no-guardedness --auto-inline --lossy-unification --allow-unsolved-metas #-} --safe

-- TODO: remove unnecessary dependencies

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.CanonicalMap
open import Notation.Order
open import UF.PropTrunc
open import MLTT.Sigma
open import Notation.General

open import UF.Subsingletons
open import UF.FunExt
open import UF.Equiv
open import UF.Powerset
open import UF.UniverseEmbedding

-- ought to not be needed eventually
open import UF.Univalence

open import Rationals.Type
open import Rationals.Order
open import Integers.Type
open import Integers.Order

open import Groups.Type
open import Groups.GroupActions
open import Groups.Subgroups

open import MLTT.Id

open import DedekindReals.Symmetry.UF
open import DedekindReals.Symmetry.IndexedAction
open import DedekindReals.Symmetry.ActionsConstructions
open import DedekindReals.Symmetry.Equivariance
open import DedekindReals.Symmetry.S2

module DedekindReals.Symmetry.Reals.Actions
 (pe : Prop-Ext)
 (pt : propositional-truncations-exist)
 (fe : Fun-Ext)
 {𝓤 : Universe} where

   open DedekindReals.Symmetry.UF.SurelyThisExistsSomewhere pe fe
   open import DedekindReals.Symmetry.MetaRelations pe pt fe ℚ (ℚ-is-set fe)
   open import DedekindReals.Symmetry.Relations-S2 pe pt fe ℚ (ℚ-is-set fe)
   open import DedekindReals.Type pe pt fe
   open PropositionalTruncation pt

   open import DedekindReals.Symmetry.Cuts pe pt fe ℚ (ℚ-is-set fe)
   open import DedekindReals.Symmetry.Reals.Type pe pt fe {𝓤}
   open import DedekindReals.Symmetry.Transport pe fe


   open import Rationals.Addition renaming (_+_ to _ℚ+_)
   open import Rationals.Negation
   open import Rationals.Multiplication renaming (_*_ to _ℚ*_)

   -- First, let's define some symmetries on the reals
   additive-ℚ : Group 𝓤₀
   additive-ℚ
     = ℚ
     , _ℚ+_
     , ℚ-is-set fe
     , ℚ+-assoc fe
     , 0ℚ
     , ℚ-zero-left-neutral fe
     , ℚ-zero-right-neutral fe
     , λ p → (- p)
           , (ℚ-inverse-sum-to-zero' fe p)
           , (ℚ-inverse-sum-to-zero  fe p)

   ℚ∘ : 𝓤₀ ̇
   ℚ∘ = Σ p ꞉ ℚ , p ≠ 0ℚ

   ℚ∘-is-set : is-set ℚ∘
   ℚ∘-is-set = sigma-is-set (ℚ-is-set fe)
     -- TODO: prove this in a way that would make Martin happy
     (λ {p {f} {.f} refl arefl → {!refl!}})

   ≠0ℚ-is-prop : (p : ℚ) → is-prop (p ≠ 0ℚ)
   ≠0ℚ-is-prop p p≠₁0 p≠₂0 = nfe-by-fe fe (λ x → 𝟘-elim (p≠₁0 x))

   -- Must be somewhere!
   ℚ-dec-eq : (p q : ℚ) → (p ＝ q) ∔ (p ≠ q)
   ℚ-dec-eq p q with ℚ-trichotomous fe p q
   ... | inl p<q = inr (λ {refl → ℚ<-not-itself p p<q})
   ... | inr (inl p＝q) = inl p＝q
   ... | inr (inr p>q) = inr (λ {refl → ℚ<-not-itself p p>q})

   ℚ*-no-zero-divisors : (p q : ℚ) → (p ℚ* q ＝ 0ℚ) →
     (p ＝ 0ℚ) ∔ (q ＝ 0ℚ)
   ℚ*-no-zero-divisors p q p*q=0 with ℚ-dec-eq q 0ℚ
   ... | inl q=0 = inr q=0
   ... | inr q≠0 = inl
     (p
        ＝⟨ ℚ-mult-right-id fe p  ⁻¹  ⟩
      p ℚ* 1ℚ
        ＝⟨ ap (p ℚ*_) (qq'1 ⁻¹) ⟩
      p ℚ* (q ℚ* q')
        ＝⟨ ℚ*-assoc fe p q q' ⁻¹ ⟩
      (p ℚ* q ) ℚ* q'
        ＝⟨ ap (_ℚ* q') p*q=0 ⟩
      0ℚ ℚ* q'
        ＝⟨ ℚ-zero-left-is-zero fe q' ⟩
      0ℚ ∎)
     where
       q-inv : Σ q' ꞉ ℚ , q ℚ* q' ＝ 1ℚ
       q-inv = ℚ*-inverse fe q q≠0
       q' : ℚ
       q' = pr₁ q-inv
       qq'1 : q ℚ* q' ＝ 1ℚ
       qq'1 = pr₂ q-inv

   ℚ-one-not-zero : 1ℚ ≠ 0ℚ
   ℚ-one-not-zero 1=0 = ℚ-zero-not-one fe (1=0 ⁻¹)

   multiplicative-ℚ : Group 𝓤₀
   multiplicative-ℚ
     = ℚ∘
     , (λ (p , p≠0) (q , q≠0) → (p ℚ* q)
       , cases
           p≠0
           q≠0
           ∘ (ℚ*-no-zero-divisors p q) )
     , ℚ∘-is-set
     , (λ (x , _) (y , _) (z , _) →
          to-subtype-＝
            ≠0ℚ-is-prop
            (ℚ*-assoc fe x y z))
     , (1ℚ , ℚ-one-not-zero)
     , (λ (x , _) → to-subtype-＝
         ≠0ℚ-is-prop
         (ℚ-mult-left-id fe x))
     , (λ (x , _) → to-subtype-＝
         ≠0ℚ-is-prop
         (ℚ-mult-right-id fe x))
     , λ (x , x≠0) →
         let x' = multiplicative-inverse fe x x≠0
         in (x'
         , λ x'=0 → ℚ-one-not-zero
           (1ℚ
              ＝⟨ ℚ*-inverse-product-is-one fe x x≠0 ⁻¹ ⟩
            x ℚ* x'
              ＝⟨ ap (x ℚ*_) x'=0 ⟩
            (x ℚ* 0ℚ)
              ＝⟨ ℚ-zero-right-is-zero fe x ⟩
            0ℚ ∎))
       , to-subtype-＝
           ≠0ℚ-is-prop
           (x' ℚ* x
             ＝⟨ ℚ*-comm x' x ⟩
           x ℚ* x'
             ＝⟨ ℚ*-inverse-product-is-one fe x x≠0 ⟩
            1ℚ ∎)
       , to-subtype-＝
           ≠0ℚ-is-prop
           (ℚ*-inverse-product-is-one fe x x≠0)

   ℚ∘-pos : 𝓟 ℚ∘
   ℚ∘-pos (p , _) = 0ℚ < p , ℚ<-is-prop 0ℚ p

   instance
     canonical-map-ℚ∘-to-ℚ : Canonical-Map ℚ∘ ℚ
     ι {{canonical-map-ℚ∘-to-ℚ}} = pr₁


   open import DedekindReals.Symmetry.Subgroups pe pt fe

   -- This ought to be in Rationals.Order
   ℚ-pos-non-zero : (p : ℚ) → (p>0 : 0ℚ < p) → ¬ (p ＝ 0ℚ)
   ℚ-pos-non-zero p p>0 p=0 = ℚ<-not-itself 0ℚ (transport (0ℚ <_) p=0 p>0)

   multiplicative-ℚ+-subgroup
     : Subgroups' multiplicative-ℚ
   multiplicative-ℚ+-subgroup = ℚ∘-pos ,
     ( lift _ (0 , refl)
     , (λ p q p>0 q>0 →
         (ℚ<-pos-multiplication-preserves-order
           (ι (lower p)) (ι (lower q)) p>0 q>0))
     , (λ { (p , p≠0) p>0 →
            (multiplicative-inverse-preserves-pos fe
              p (p>0) p≠0)
          }) ∘ lower)

   multiplicative-ℚ+ : Group 𝓤₀
   multiplicative-ℚ+ = induced-group' multiplicative-ℚ multiplicative-ℚ+-subgroup

   open import DedekindReals.Addition pe pt fe
     renaming (_+_ to _ℝ+_; -_ to ℝ-_)
   additive-ℝ' : Group 𝓤₁
   -- TODO: transport structure
   additive-ℝ'
     = ℝ'
     , (λ r s → ⌜ ℝ≃ℝ' ⌝ (⌜ ℝ≃ℝ' ⌝⁻¹ r ℝ+ ⌜ ℝ≃ℝ' ⌝⁻¹ s))
     , ℝ'-is-set
     , {!!}
     , ι 0ℝ
     , {!!}
     , {!!}
     , λ x →
       (ι (ℝ- ι x))
     , {!!}
     , {!!}

   ℚ+' : Group 𝓤₁
   ℚ+' = Lift-group additive-ℚ

   ℚ+'∣ℝ' : Action ℚ+'
   ℚ+'∣ℝ'
     = ℝ'
     , (λ lp r → ι (lower lp) ·⟨ additive-ℝ' ⟩ r)
     , ℝ'-is-set
     , {!!}
     , {!!}

   ℚ₊ : 𝓤₀ ̇
   ℚ₊ = ⟨ multiplicative-ℚ+ ⟩

   instance
     canonical-map-ℚ₊-to-ℚ : Canonical-Map ℚ₊ ℚ
     ι {{canonical-map-ℚ₊-to-ℚ}} = pr₁ ∘ pr₁

   -- can do away with some of the projection reshuffling if
   -- we define the monoid action instead

   ℚ*' : Group 𝓤₁
   ℚ*' = Lift-group multiplicative-ℚ

   -- It's easier to go this way :(
   ℚ₊*'◃ℚ*' : Subgroups' ℚ*'
   ℚ₊*'◃ℚ*' = lift-Ω ∘ ℚ∘-pos ∘ lower
     , lift _ (unit-closed' multiplicative-ℚ multiplicative-ℚ+-subgroup)
     , (λ 𝓐 x y z → lift _
         (mult-closed' multiplicative-ℚ multiplicative-ℚ+-subgroup
           (lower 𝓐) (lower x) (lower y) (lower z)))
     , λ 𝓐 x → lift _
         (inv-closed' multiplicative-ℚ multiplicative-ℚ+-subgroup
           (lower 𝓐) (lower x))

   ℚ₊*' : Group 𝓤₁
   ℚ₊*' = induced-group' ℚ*' ℚ₊*'◃ℚ*'

   scale-pred : ⟨ multiplicative-ℚ ⟩ → 𝓟 ℚ → 𝓟 ℚ
   scale-pred p P q
       -- This way around works better with left actions
     = P (q ℚ* pr₁ p)

   -- Now starts the real work, hopefully
   ℚ*'∣𝓟ℚ : Action ℚ*'
   ℚ*'∣𝓟ℚ
     = 𝓟 ℚ
     , (λ lp P → scale-pred (lower lp) P)
     , 𝓟-is-set' fe pe
     , (λ lp lq L →
         nfe-by-fe fe λ x →
         ap L (ℚ*-assoc fe x (ι (lower lp)) (ι (lower lq)) ⁻¹))
     , λ L → nfe-by-fe fe
       λ x → ap L (ℚ-mult-right-id fe x)

   ℚ₊*'∣𝓟ℚ : Action ℚ₊*'
   ℚ₊*'∣𝓟ℚ = induced-action ℚ*' ℚ₊*'◃ℚ*' ℚ*'∣𝓟ℚ

   ℚ₊*'∣𝓟ℚ-inhabited-invariant :
     prop-is-invariant (Lift-group {𝓥 = 𝓤₀ ⁺⁺} ℚ₊*')
                       (Lift-action ℚ₊*' ℚ₊*'∣𝓟ℚ)
                       (inhabited-pred ∘ lower)
   ℚ₊*'∣𝓟ℚ-inhabited-invariant g L with g' ← pr₁ (lower (pr₁ (lower g)))
     = ∥∥-induction
     {!!}
     λ (p , Lp) → ∣ g' ℚ* p  , {!!}   ∣

   ℚ*'∣pre-cut-action : action-structure ℚ*' pre-cut
   ℚ*'∣pre-cut-action lpnz r
     with (p , p≠0) ← lower lpnz | ℚ-trichotomous fe p 0ℚ
   ... | inl p>0 = {!!}
   ... | inr p<0 = {!!}

   ℚ*'∣pre-cut : Action ℚ*'
   ℚ*'∣pre-cut
     = pre-cut
     , (λ lq x → {!!})
     , {!!}
     , {!!}
     , {!!}
