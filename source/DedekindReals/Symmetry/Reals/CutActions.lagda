Andrew Sneap and Ohad Kammar

Actions on cuts. I needed to break Actions into another module since
it was getting too slow.

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
open import UF.Subsingletons-FunExt
open import UF.FunExt
open import UF.Equiv
open import UF.Powerset
open import UF.UniverseEmbedding

-- ought to not be needed eventually
open import UF.Univalence

open import Rationals.Type
open import Rationals.Order
open import Rationals.FractionsOrder

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
open import DedekindReals.Symmetry.GroupProperties

open import DedekindReals.Symmetry.Transitive

module DedekindReals.Symmetry.Reals.CutActions
 (pe : Prop-Ext)
 (pt : propositional-truncations-exist)
 (fe : Fun-Ext)
 {𝓤 : Universe} where

   open DedekindReals.Symmetry.UF.SurelyThisExistsSomewhere pe fe
   open import DedekindReals.Symmetry.MetaRelations pe pt fe
   open SetConstructions ℚ (ℚ-is-set fe)
   open import DedekindReals.Symmetry.Relations-S2 pe pt fe
   open SetConstructions-S2 ℚ (ℚ-is-set fe)
   open import DedekindReals.Type pe pt fe
   open PropositionalTruncation pt

   open import DedekindReals.Symmetry.Cuts pe pt fe ℚ (ℚ-is-set fe)
   open import DedekindReals.Symmetry.Reals.Type pe pt fe {𝓤}
   open import DedekindReals.Symmetry.Transport pe fe


   open import Rationals.Addition renaming (_+_ to _ℚ+_)
   open import Rationals.Negation
   open import Rationals.Multiplication renaming (_*_ to _ℚ*_)

   open import DedekindReals.Symmetry.Reals.Actions pe pt fe {𝓤}

   data S₂×ℚ₊⟦_⟧ : ℚ∘ → 𝓤₀ ̇ where
     _◂_ : (σ : ⟨ S₂ ⟩) → (p : ℚ₊) → S₂×ℚ₊⟦ σ ◂⟨ S₂ ∣ S₂∣ℚ∘ ⟩ pr₁ p ⟧

   ℚ<-left-neg-multiplication-reverses-order : (p q : ℚ) →
     0ℚ > p → 0ℚ < q → 0ℚ > p ℚ* q
   ℚ<-left-neg-multiplication-reverses-order p q p<0 q>0 =
      p ℚ* q
        ≺⟨ _<_ ∣ ℚ<-neg-multiplication-antitone-left
                 p 0ℚ q p<0 q>0 ⟩
      0ℚ ℚ* 0ℚ
      ＝[ ℚ-zero-left-is-zero fe 0ℚ ]
      0ℚ ∎
   ℚ<-right-neg-multiplication-reverses-order : (p q : ℚ) →
     0ℚ < p → 0ℚ > q → 0ℚ > p ℚ* q
   ℚ<-right-neg-multiplication-reverses-order p q p>0 q<0 =
      p ℚ* q
        ＝[ ℚ*-comm p q ]
      q ℚ* p
        ≺⟨ _<_ ∣ ℚ<-left-neg-multiplication-reverses-order
                 q p q<0 p>0 ⟩
      0ℚ ∎

   ℚ*-neg-neg-pos : (p q : ℚ) →
     p < 0ℚ → q < 0ℚ → p ℚ* q > 0ℚ
   ℚ*-neg-neg-pos p q p<0 q<0 =
      0ℚ
      ＝[ ℚ-zero-left-is-zero fe 0ℚ ]
      0ℚ ℚ* 0ℚ
      ≺⟨ _<_ ∣ ℚ<-neg-multiplication-antitone-left
                 p q 0ℚ p<0 q<0 ⟩
      p ℚ* q ∎

   ℚ∘-sign : (p : ℚ∘) → (pr₁ p < 0ℚ) ∔ (pr₁ p > 0ℚ)
   ℚ∘-sign (p , p≠0) with ℚ-trichotomous fe p 0ℚ
   ... | inl p<0 = inl p<0
   ... | inr (inl p=0) = 𝟘-elim (p≠0 p=0)
   ... | inr (inr p>0) = inr p>0

   ℚ-pos-mult : (p q : ℚ) → (p ℚ* q > 0ℚ) →
     (p > 0ℚ) × (q > 0ℚ) ∔ (p < 0ℚ) × (q < 0ℚ)
   ℚ-pos-mult p q pq>0 with ℚ*-non-zero-non-zero-factors p q
                               (ℚ-pos-non-zero (p ℚ* q) pq>0)
   ... | p≠0 , q≠0 with ℚ∘-sign (p , p≠0) | ℚ∘-sign (q , q≠0)
   ... | inl p<0 | inl q<0 = inr (p<0 , q<0)
   ... | inl p<0 | inr q>0 = 𝟘-elim
     (ℚ-not-<-and-> (p ℚ* q) 0ℚ
       (ℚ<-left-neg-multiplication-reverses-order p q p<0 q>0
       , pq>0))
   ... | inr p>0 | inl q<0 = 𝟘-elim
     (ℚ-not-<-and-> (p ℚ* q) 0ℚ
       (ℚ<-right-neg-multiplication-reverses-order p q p>0 q<0
       , pq>0))
   ... | inr p>0 | inr q>0 = inl (p>0 , q>0)

   ℚ∘→S₂ : (p : ℚ∘) → ⟨ S₂ ⟩
   ℚ∘→S₂ p with ℚ∘-sign p
   ... | inl p<0 = flip
   ... | inr p>0 = id∈S₂

   1ℚ∘ : ℚ∘
   1ℚ∘ = 1ℚ , ℚ-one-not-zero

   -1ℚ∘ : ℚ∘
   -1ℚ∘ = -1ℚ , -1ℚ≠0

   ±⟦_⟧ : ⟨ S₂ ⟩ → ℚ∘
   ±⟦ id∈S₂ ⟧ =  1ℚ∘
   ±⟦ flip  ⟧ = -1ℚ , -1ℚ≠0

   ±⟦_⟧-is-hom : is-hom S₂ ℚ∘* ±⟦_⟧
   ±⟦_⟧-is-hom {id∈S₂} {σ} =
     ±⟦ σ ⟧
       ＝⟨ unit-left ℚ∘* ±⟦ σ ⟧ ⁻¹ ⟩
     1ℚ∘ ·⟨ ℚ∘* ⟩ ±⟦ σ ⟧ ∎
   ±⟦_⟧-is-hom {flip} {id∈S₂} = {!!}
   ±⟦_⟧-is-hom {flip} {flip} =
     1ℚ∘
       ＝⟨ unit-left ℚ∘* 1ℚ∘ ⁻¹ ⟩
     1ℚ∘ ·⟨ ℚ∘* ⟩ 1ℚ∘
       ＝⟨ to-subtype-＝
         {!!}
         ({!ℚ-neg-neg- -1ℚ -1ℚ -1ℚ<0 -1ℚ<0!} ⁻¹) ⟩
     -1ℚ∘ ·⟨ ℚ∘* ⟩ -1ℚ∘ ∎


   ℚ∘→ℚ₊>0 : (p : ℚ∘) → pr₁ ((ℚ∘→S₂ p) ◂⟨ S₂ ∣ S₂∣ℚ∘ ⟩ p) > 0ℚ
   ℚ∘→ℚ₊>0 pnz@(p , p≠0) with ℚ∘-sign pnz
   ... | inl p<0 = ℚ<-neg-neg-pos p p<0
   ... | inr p>0 = p>0

   ℚ∘→ℚ₊ : (p : ℚ∘) → ℚ₊
   ℚ∘→ℚ₊ p = (ℚ∘→S₂ p) ◂⟨ S₂ ∣ S₂∣ℚ∘ ⟩ p , ℚ∘→ℚ₊>0 p

   ℚ∘↞S₂×ℚ₊ : (p : ℚ∘) → S₂×ℚ₊⟦ p ⟧
   ℚ∘↞S₂×ℚ₊ pnz@(p , p≠0) = transport S₂×ℚ₊⟦_⟧
     (let σ = ℚ∘→S₂ pnz
      in σ ◂⟨ S₂ ∣ S₂∣ℚ∘ ⟩ (σ ◂⟨ S₂ ∣ S₂∣ℚ∘ ⟩ pnz)
            ＝⟨ action-assoc S₂ S₂∣ℚ∘ σ σ pnz ⁻¹ ⟩
          (σ ·⟨ S₂ ⟩ σ) ◂⟨ S₂ ∣ S₂∣ℚ∘ ⟩ pnz
            ＝⟨ S₂-action-order-2 S₂∣ℚ∘ σ pnz ⟩
         pnz ∎)
     ((ℚ∘→S₂ pnz) ◂ (ℚ∘→ℚ₊ pnz))

   -- the point:
   ℚ∘→S₂×ℚ₊ : ℚ∘ → (⟨ S₂ ⟩ × ℚ₊ )
   ℚ∘→S₂×ℚ₊ (p , p≠0) with ℚ∘↞S₂×ℚ₊ (p , p≠0)
   ℚ∘→S₂×ℚ₊ (.(σ ◂⟨ S₂ ∣ S₂∣ℚ∘ ⟩ pr₁ p )) | σ ◂ p = (σ , p)

   flip＝ℚ∘→S₂ : (p : ℚ∘) → (ι p < 0ℚ) → flip ＝ ℚ∘→S₂ p
   flip＝ℚ∘→S₂ p p<0 with ℚ∘-sign p
   ... | inl p<0 = refl
   ... | inr p>0 = 𝟘-elim (ℚ-not-<-and-> (ι p) 0ℚ (p<0 , p>0) )

   id＝ℚ∘→S₂ : (p : ℚ∘) → (ι p > 0ℚ) → id∈S₂ ＝ ℚ∘→S₂ p
   id＝ℚ∘→S₂ p p>0 with ℚ∘-sign p
   ... | inl p<0 = 𝟘-elim (ℚ-not-<-and-> (ι p) 0ℚ (p<0 , p>0) )
   ... | inr p>0 = refl

   ℚ∘→S₂-is-hom : is-hom ℚ∘* S₂ ℚ∘→S₂
   ℚ∘→S₂-is-hom {pnz@(p , p≠0)} {qnz@(q , q≠0)}
       with ℚ∘-sign pnz | ℚ∘-sign qnz
   ... | inl p<0 | inl q<0
         --with refl ←
           =
     ℚ∘→S₂ (pnz ·⟨ ℚ∘* ⟩ qnz )
       ＝⟨ id＝ℚ∘→S₂
           (pnz ·⟨ ℚ∘* ⟩ qnz) (ℚ*-neg-neg-pos p q p<0 q<0) ⁻¹ ⟩
     id∈S₂ ∎
   ... | inl p<0 | inr q>0 =
     ℚ∘→S₂ (pnz ·⟨ ℚ∘* ⟩ qnz )
       ＝⟨ flip＝ℚ∘→S₂
           (pnz ·⟨ ℚ∘* ⟩ qnz)
           (ℚ<-left-neg-multiplication-reverses-order
             p q p<0 q>0) ⁻¹ ⟩
     flip ∎
   ... | inr p>0 | inl q<0 =
     ℚ∘→S₂ (pnz ·⟨ ℚ∘* ⟩ qnz )
       ＝⟨ flip＝ℚ∘→S₂
           (pnz ·⟨ ℚ∘* ⟩ qnz)
           (ℚ<-right-neg-multiplication-reverses-order
             p q p>0 q<0) ⁻¹ ⟩
     flip ∎

   ... | inr p>0 | inr q>0 =
       ℚ∘→S₂ (pnz ·⟨ ℚ∘* ⟩ qnz )
       ＝⟨ id＝ℚ∘→S₂
           (pnz ·⟨ ℚ∘* ⟩ qnz)
           (ℚ<-pos-multiplication-preserves-order
             p q p>0 q>0) ⁻¹ ⟩
     id∈S₂ ∎

   ℚ∘→ℚ₊-is-hom : is-hom ℚ∘* ℚ₊* ℚ∘→ℚ₊
   ℚ∘→ℚ₊-is-hom {pnz@(p , p≠0)} {qnz@(q , q≠0)} =
     to-subtype-＝
       (holds-is-prop ∘ ℚ∘-pos)
       (to-subtype-＝ ≠0ℚ-is-prop
       (pr₁ (ℚ∘→S₂ (pnz ·⟨ ℚ∘* ⟩ qnz)
         ◂⟨ S₂ ∣ S₂∣ℚ∘ ⟩ (pnz ·⟨ ℚ∘* ⟩ qnz))
       ＝⟨ ap2 (λ x y → (x ◂⟨ S₂ ∣ S₂∣ℚ ⟩ (y)))
             ℚ∘→S₂-is-hom
             (ℚ-mult-right-id fe (p ℚ* q) ⁻¹)
             ⟩
       (((ℚ∘→S₂ pnz) ·⟨ S₂ ⟩ (ℚ∘→S₂ qnz)))
         ◂⟨ S₂ ∣ S₂∣ℚ ⟩ ((p ℚ* q) ℚ* 1ℚ)
       ＝⟨ refl ⟩
       (((ℚ∘→S₂ pnz) ·⟨ S₂ ⟩ (ℚ∘→S₂ qnz))
       , (pnz ·⟨ ℚ∘* ⟩ qnz))
         ◂⟨ S₂ ⊗ ℚ∘* ∣ S₂-ℚ∘*∣ℚ ⟩
         1ℚ
       ＝⟨ action-assoc (S₂ ⊗ ℚ∘*) S₂-ℚ∘*∣ℚ
             (ℚ∘→S₂ pnz , pnz)
             (ℚ∘→S₂ qnz , qnz) 1ℚ  ⟩
       ((ℚ∘→S₂ pnz) ◂⟨ S₂ ∣ S₂∣ℚ ⟩
         (pnz ◂⟨ ℚ∘* ∣ ℚ∘*∣ℚ ⟩
           ((ℚ∘→S₂ qnz) ◂⟨ S₂ ∣ S₂∣ℚ ⟩
             (q ℚ* 1ℚ))))
       ＝⟨ ap (λ x →
              (ℚ∘→S₂ pnz) ◂⟨ S₂ ∣ S₂∣ℚ ⟩
         (pnz ◂⟨ ℚ∘* ∣ ℚ∘*∣ℚ ⟩
           ((ℚ∘→S₂ qnz) ◂⟨ S₂ ∣ S₂∣ℚ ⟩
             x)))
            (ℚ-mult-right-id fe q) ⟩
       {!{- OK: I am here. -} (ℚ∘→S₂ pnz) ◂⟨ S₂ ∣ S₂∣ℚ ⟩!}
       ＝⟨ action-assoc ℚ∘* ℚ∘*∣ℚ {!ℚ∘-sign pnz!} {!!} {!!} ⟩
       pr₁((pr₁ (ℚ∘→ℚ₊ pnz)) ·⟨ ℚ∘* ⟩ (pr₁ (ℚ∘→ℚ₊ qnz))) ∎))

      {-
   ℚ∘→S₂×ℚ₊-is-hom : is-hom ℚ∘* (S₂ ⊗ ℚ₊*) ℚ∘→S₂×ℚ₊
   ℚ∘→S₂×ℚ₊-is-hom {p} {q} =
      {!!}
        ＝⟨ {!!} ⟩
      {!!} ∎

   Flip-𝓟ℚ : Action' S₂
   Flip-𝓟ℚ = Flip (𝓟 ℚ) ((𝓟-is-set' fe pe))

   S₂⊗ℚ₊*∣pre-cut-action : action-structure (S₂ ⊗ ℚ₊*) pre-cut
   S₂⊗ℚ₊*∣pre-cut-action πp@(π , p) (L , R) =
     π ◂⟨ S₂ ∣ Flip-𝓟ℚ ⟩
          ( πp ◂⟨ S₂ ⊗ ℚ₊* ∣ S₂⊗ℚ₊*∣𝓟ℚ ⟩ L
          , πp ◂⟨ S₂ ⊗ ℚ₊* ∣ S₂⊗ℚ₊*∣𝓟ℚ ⟩ R  )

   S₂⊗ℚ₊*∣pre-cut : Action' (S₂ ⊗ ℚ₊*)
   S₂⊗ℚ₊*∣pre-cut
     = pre-cut
     , S₂⊗ℚ₊*∣pre-cut-action
     , pre-cut-is-set ℚ<
     , (λ { πp@(id∈S₂ , p) σq@(id∈S₂ , q) (L , R) → ap2 _,_
              (action-assoc (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣𝓟ℚ
                πp σq L)
              (action-assoc (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣𝓟ℚ
                πp σq R)
          -- hopefully there's a symmetric proof instead
          ; πp@(id∈S₂ , p) σq@(flip  , q) (L , R) → ap2 _,_
              (action-assoc (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣𝓟ℚ
                πp σq R)
              (action-assoc (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣𝓟ℚ
                πp σq L)
          ; πp@(flip  , p) σq@(id∈S₂ , q) (L , R) → ap2 _,_
              (action-assoc (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣𝓟ℚ
                πp σq R)
              (action-assoc (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣𝓟ℚ
                πp σq L)
          ; πp@(flip  , p) σq@(flip  , q) (L , R) → ap2 _,_
              (action-assoc (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣𝓟ℚ
                πp σq L)
              (action-assoc (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣𝓟ℚ
                πp σq R)
          })
     , λ (L , R) → ap2 _,_
          (action-unit (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣𝓟ℚ L )
          (action-unit (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣𝓟ℚ R )

   ℚ∘*∣pre-cut-structure : action-structure ℚ∘* pre-cut
   ℚ∘*∣pre-cut-structure p LR =
     (ℚ∘→S₂×ℚ₊ p) ◂⟨ S₂ ⊗ ℚ₊* ∣ S₂⊗ℚ₊*∣pre-cut ⟩ LR
   ℚ∘*∣pre-cut-is-assoc : is-assoc ℚ∘* ℚ∘*∣pre-cut-structure
   ℚ∘*∣pre-cut-is-assoc p q LR =
     (ℚ∘→S₂×ℚ₊ (p ·⟨ ℚ∘* ⟩ q)) ◂⟨ S₂ ⊗ ℚ₊* ∣ S₂⊗ℚ₊*∣pre-cut ⟩ LR
       ＝⟨ ap (λ x → action-op-syntax (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣pre-cut x LR)
              ℚ∘→S₂×ℚ₊-is-hom ⟩
     (ℚ∘→S₂×ℚ₊ (p) ·⟨ S₂ ⊗ ℚ₊* ⟩ ℚ∘→S₂×ℚ₊ (q)) ◂⟨ S₂ ⊗ ℚ₊* ∣ S₂⊗ℚ₊*∣pre-cut ⟩ LR
       ＝⟨ action-assoc (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣pre-cut
           (ℚ∘→S₂×ℚ₊ (p)) (ℚ∘→S₂×ℚ₊ (q)) LR ⟩
     (ℚ∘→S₂×ℚ₊ p) ◂⟨ S₂ ⊗ ℚ₊* ∣ S₂⊗ℚ₊*∣pre-cut ⟩
         ((ℚ∘→S₂×ℚ₊ q) ◂⟨ S₂ ⊗ ℚ₊* ∣ S₂⊗ℚ₊*∣pre-cut ⟩ LR) ∎
   ℚ∘*∣pre-cut : Action' ℚ∘*
   ℚ∘*∣pre-cut
     = pre-cut
     , ℚ∘*∣pre-cut-structure
     , pre-cut-is-set ℚ<
     , (λ p q LR → {!action-assoc (S₂ ⊗ ℚ₊*) S₂⊗ℚ₊*∣pre-cut
         (ℚ∘→S₂×ℚ₊ p) (ℚ∘→S₂×ℚ₊ q) LR!})
     , {!action-assoc!}
-}
